import Lean

/-!
Reusable measurements for executable evaluation and actual `by rfl` proofs.
Used by `scripts/benchmarks/benchmark_lean.py`; see `scripts/benchmarks/benchmark_lean.md`.
The proof-measurement method comes from the archived Walk experiments.
-/

open Lean Elab Command Meta

namespace LeanDefinitionBench

/-- An executable case with input preparation and result validation outside the clock.
Use `prepare` to specify whether inputs are fresh or shared. -/
structure EvalCase where
  name : String
  Input : Type
  Output : Type
  prepare : IO Input
  run : Input → IO Output
  check : Output → IO Unit

private def counts : IO (Nat × Nat) := do
  let warmups := (← IO.getEnv "LEAN_BENCH_WARMUPS").getD "2"
  let trials := (← IO.getEnv "LEAN_BENCH_TRIALS").getD "7"
  let some warmups := warmups.toNat? | throw <| IO.userError "invalid warmup count"
  let some trials := trials.toNat? | throw <| IO.userError "invalid trial count"
  unless trials > 0 do throw <| IO.userError "trial count must be positive"
  return (warmups, trials)

private def record (name stage : String) (trial position warmups ns : Nat)
    (heartbeats : Option Nat := none) : IO Unit := do
  let fields := [("case", toJson name), ("stage", toJson stage),
    ("trial", toJson trial), ("position", toJson position),
    ("phase", toJson (if trial < warmups then "warmup" else "measure")),
    ("wall_ns", toJson ns)]
  let fields := match heartbeats with
    | none => fields
    | some n => fields ++ [("heartbeats", toJson n)]
  IO.println ("LEAN_BENCH " ++ (Json.mkObj fields).compress)
  (← IO.getStdout).flush

-- Keep the call inside the two clock reads, including for closed candidate terms.
@[noinline] private def invoke (c : EvalCase) (input : c.Input) : IO c.Output := c.run input

/-- Run interleaved cases. Call this from the fixture's `main`.
The default runner uses Lean's executable evaluator. An independently compiled fixture
can use the same entry point for native measurements. -/
def runEval (cases : Array EvalCase) : IO Unit := do
  unless cases.size > 0 do throw <| IO.userError "no executable cases"
  let names := cases.toList.map (·.name)
  unless names.eraseDups.length == names.length do
    throw <| IO.userError "duplicate executable case names"
  let (warmups, trials) ← counts
  let stage := (← IO.getEnv "LEAN_BENCH_RUNTIME").getD "eval"
  for trial in [:warmups + trials] do
    for position in [:cases.size] do
      let some c := cases[(trial + position) % cases.size]? |
        throw <| IO.userError "invalid case index"
      let input ← c.prepare
      let start ← IO.monoNanosNow
      let result ← invoke c input
      let stop ← IO.monoNanosNow
      c.check result
      record c.name stage trial position warmups (stop - start)

private def proofTrial (name : String) (goal : Expr) (trial position warmups : Nat) :
    CommandElabM Unit := do
  let stx ← `(by rfl)
  let (proof, ns, hb) ← runTermElabM fun _ => withFreshCache do
    let h0 ← IO.getNumHeartbeats
    let t0 ← IO.monoNanosNow
    let proof ← Term.elabTermEnsuringType stx (some goal)
    Term.synthesizeSyntheticMVarsNoPostponing
    let proof ← instantiateMVars proof
    let t1 ← IO.monoNanosNow
    let h1 ← IO.getNumHeartbeats
    if proof.hasMVar || proof.hasSorry then
      throwError "benchmark proof contains metavariables or sorry"
    return (proof, t1 - t0, h1 - h0)
  liftIO <| record name "elab" trial position warmups ns hb
  let env ← getEnv
  let opts ← getOptions
  if debug.skipKernelTC.get opts then throwError "kernel checking must be enabled"
  let declaration := Declaration.thmDecl {
    name := `lean_definition_benchmark_trial
    levelParams := [], type := goal, value := proof }
  let h0 ← IO.getNumHeartbeats
  let t0 ← IO.monoNanosNow
  let checked := Lean.Kernel.Environment.addDecl env.toKernelEnv opts declaration
  let t1 ← IO.monoNanosNow
  let h1 ← IO.getNumHeartbeats
  match checked with
  | .error ex => throwKernelException ex
  | .ok checkedEnv =>
    unless (checkedEnv.find? `lean_definition_benchmark_trial).isSome do
      throwError "benchmark theorem missing after kernel checking"
  liftIO <| record name "kernel" trial position warmups (t1 - t0) (h1 - h0)

/-- Time literal `by rfl` elaboration and synchronous kernel checking separately.
Goals are elaborated before timing; each proof gets fresh elaborator caches and the
same starting kernel environment. Case order rotates between rounds. -/
syntax (name := benchRfl) "#bench_rfl" "[" str " => " term
  ("," str " => " term)* "]" : command

elab_rules : command
  | `(#bench_rfl [$firstName:str => $firstGoal:term $[, $names:str => $goals:term]*]) => do
    if (← liftIO <| IO.getEnv "LEAN_BENCH_STAGE") == some "eval" then return
    let syntaxGoals := #[(firstName, firstGoal)] ++ names.zip goals
    let mut cases : Array (String × Expr) := #[]
    for (name, goal) in syntaxGoals do
      let expr ← runTermElabM fun _ => do
        let expr ← Term.elabTermEnsuringType goal (some (mkSort .zero))
        Term.synthesizeSyntheticMVarsNoPostponing
        let expr ← instantiateMVars expr
        if expr.hasMVar || expr.hasSorry then throwError "invalid benchmark goal"
        return expr
      cases := cases.push (name.getString, expr)
    let (warmups, trials) ← liftIO counts
    for trial in [:warmups + trials] do
      for position in [:cases.size] do
        let (name, goal) := cases[(trial + position) % cases.size]!
        proofTrial name goal trial position warmups

end LeanDefinitionBench
