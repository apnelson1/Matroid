import LeanDefinitionBench

/-! A small standalone fixture. All candidate definitions and expected values are local. -/

open LeanDefinitionBench

@[noinline] def reverseSlow {α : Type} : List α → List α
  | [] => []
  | a :: rest => reverseSlow rest ++ [a]

@[noinline] def reverseAccumulator {α : Type} (xs : List α) : List α :=
  xs.reverse

def proofInput : List Nat := [0, 1, 2, 3, 4, 5, 6, 7]
def proofExpected : List Nat := [7, 6, 5, 4, 3, 2, 1, 0]

#bench_rfl [
  "slow" => reverseSlow proofInput = proofExpected,
  "accumulator" => reverseAccumulator proofInput = proofExpected]

def executableCases : Array EvalCase :=
  #[makeCase "slow" reverseSlow, makeCase "accumulator" reverseAccumulator]
where
  makeCase (name : String) (candidate : List Nat → List Nat) : EvalCase := {
    name
    Input := List Nat
    Output := List Nat
    prepare := pure (List.range 256)
    run := fun input => pure (candidate input)
    check := fun result => do
      unless result == (List.range 256).reverse do
        throw <| IO.userError s!"{name}: incorrect result" }

def main : IO Unit := runEval executableCases
