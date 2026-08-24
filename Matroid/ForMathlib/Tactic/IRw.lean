/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Mathlib.Logic.Equiv.Set
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.Logic.Equiv.Sum
public import Mathlib.Logic.Equiv.Option
public import Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Function
public import Mathlib.Data.Subtype
public meta import Mathlib.Lean.Meta.Simp
public meta import Lean.Elab.Tactic.Rewrite
public meta import Lean.Meta.Tactic.Replace
public meta import Lean.Meta.Tactic.Grind.Main
public meta import Lean.Meta.Tactic.Grind.RegisterCommand

namespace IRw.SupportGrind

/-- Rules available to the restricted support-certificate solver used by `irw`. -/
register_grind_attr irw_support

end IRw.SupportGrind

/-!
# Isomorphism rewriting

`irw i` transports a proposition along a supplied isomorphism `i`. Earlier typeclass closure
handled only a fixed family of proposition shapes. This tactic instead traverses the *actual
proposition expression*, so its logical recursion has no arity ceiling.

The tactic has transformation-system and domain registries plus system-indexed equivalence and
naturality theorem databases.

* `@[irw_system]`: a transformation/type constructor accepted as the argument to `irw`. Its final
  two parameters are respectively the source and target objects.

* `@[irw_domain]`: a primitive total or support-restricted domain action for that system.

* `@[irw_support]`: a theorem available only to the restricted support-certificate solver.

* `@[irw_naturality]`: a system-indexed equality or iff. Equalities normalize mechanically
  transported syntax; proposition-valued declarations also serve as primitive atomic transport.
  Both are oriented from mechanically transported source syntax to canonical target syntax.

* `@[irw_equiv]`: a theorem whose first explicit argument is the supplied isomorphism and whose
  result is an `Equiv`.  These rules transport quantified binder types.

Except for `@[irw_system]`, registrations accept the usual optional Lean priority (`low`, `high`,
or a numeral). Contributors should omit it. Exact matches always outrank definitional matches;
within one match class higher priority wins. Equal-priority naturality rules with overlapping left
sides must produce the same canonical form and are otherwise rejected at registration time.

For project-owned API, place a registration on the canonical declaration beside its definition.
Separate registration modules are reserved for declarations owned by Mathlib. A naturality theorem
should take the transformation as its first explicit argument and be oriented from mechanically
transported source syntax to ordinary canonical target syntax.

Within the active system, exact instantiated source matches outrank merely definitionally equal
matches. Conflicting exact matches are rejected rather than resolved by declaration order.

Logical connectives and quantifiers are handled by the metaprogram itself.  Bounded quantifiers
such as `∀ X, X ⊆ E → ...` and `∃ X, X ⊆ E ∧ ...` are recognized when the ambient binder type does
not itself transport: the guard is bundled into a subtype and `@[irw_equiv]` is asked to transport
that subtype.  Universal guards may also be batched after several binders, as in
`∀ X Y, guardX → guardY → ...`; the engine proves a telescope permutation, reuses the same bounded
transport path, and then restores the original binder/guard ordering.
Existential guards may likewise be batched after several witnesses. The engine hoists each guard
next to its witness with a checked logical equivalence, transports the adjacent bounded form, and
then restores the original batched ordering.

This file is deliberately domain-independent.  Matroid and Graph registrations live in their
adapter files, so it imports nothing from `Matroid`.
-/

@[expose] public section

open Lean Meta Elab Elab.Tactic

namespace IRw

universe u v

/-! ## Small proof-producing lemmas used by the metaprogram -/

/-- Compose an iff with an equality on its right side. -/
theorem iff_trans_eq {p q r : Prop} (h : p ↔ q) (e : q = r) : p ↔ r := by
  subst r
  exact h

/-- Transport an implication when the consequent equivalence may use the source antecedent as a
logical support fact. -/
theorem imp_congr_of_left {a a' b b' : Prop} (ha : a ↔ a')
    (hb : a → (b ↔ b')) : (a → b) ↔ (a' → b') := by
  constructor
  · intro hab ha'
    have ha0 := ha.mpr ha'
    exact (hb ha0).mp (hab ha0)
  · intro hab' ha0
    exact (hb ha0).mpr (hab' (ha.mp ha0))

/-- Transport equality through an equivalence. -/
theorem eq_congr_equiv {α β : Sort*} (e : α ≃ β) (x y : α) :
    (x = y) ↔ (e x = e y) := e.injective.eq_iff.symm

/-- Transport membership through an equivalence. -/
theorem mem_congr_equiv {α β : Type*} (e : α ≃ β) (x : α) (S : Set α) :
    x ∈ S ↔ e x ∈ e '' S := by simp

/-- Transport subset through an equivalence. -/
theorem subset_congr_equiv {α β : Type*} (e : α ≃ β) (S T : Set α) :
    S ⊆ T ↔ e '' S ⊆ e '' T :=
  (Set.image_subset_image_iff e.injective).symm

/-! ### Coherence cleanup for structural binder equivalences

When recursion enters a binder transported by a structural equivalence `E`, the source body is
instantiated at `E.symm y`.  Atomic rules then transport the pieces of that source value again.
For a bare value this produces `e (e.symm y)`, handled by `Equiv.apply_symm_apply`. Product
projections and sets hide that same cancellation behind their constructors. Forward structural
transport can also hide a payload beneath a constructor, as in `optionCongr e (some x)`, or beneath
function transport. The equations below expose both kinds of structure to the small `irw` cleanup
simp set so normalization can continue recursively through arbitrary compositions.

These are deliberately *not* global `[simp]` lemmas.  They belong to the normalization protocol of
`irw`'s internally constructed structural equivalences. -/

/-- First projection of the inverse product transport. -/
theorem prodCongr_symm_apply_fst {α₁ α₂ β₁ β₂ : Type*}
    (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) (p : α₂ × β₂) :
    ((Equiv.prodCongr e₁ e₂).symm p).1 = e₁.symm p.1 := by
  cases p
  rfl

/-- Second projection of the inverse product transport. -/
theorem prodCongr_symm_apply_snd {α₁ α₂ β₁ β₂ : Type*}
    (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) (p : α₂ × β₂) :
    ((Equiv.prodCongr e₁ e₂).symm p).2 = e₂.symm p.2 := by
  cases p
  rfl

/-- Forward product transport acts componentwise on a constructor. -/
theorem prodCongr_apply_mk {α₁ α₂ β₁ β₂ : Type*}
    (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) (x : α₁) (y : β₁) :
    Equiv.prodCongr e₁ e₂ (x, y) = (e₁ x, e₂ y) := rfl

/-- Forward sum transport preserves the left constructor and transports its payload. -/
theorem sumCongr_apply_inl {α₁ α₂ β₁ β₂ : Type*}
    (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) (x : α₁) :
    Equiv.sumCongr e₁ e₂ (Sum.inl x) = Sum.inl (e₁ x) := rfl

/-- Forward sum transport preserves the right constructor and transports its payload. -/
theorem sumCongr_apply_inr {α₁ α₂ β₁ β₂ : Type*}
    (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) (y : β₁) :
    Equiv.sumCongr e₁ e₂ (Sum.inr y) = Sum.inr (e₂ y) := rfl

/-- `Equiv.Set.congr` transports a set by image.  Applying the element transport to the inverse
transport of a set therefore cancels.  This is the set-level analogue of
`Equiv.apply_symm_apply`. -/
theorem image_setCongr_symm_apply {α β : Type*} (e : α ≃ β) (S : Set β) :
    e '' ((Equiv.Set.congr e).symm S) = S := by
  change e '' (e.symm '' S) = S
  exact e.image_symm_image S

/-- Expose the image representation used by set-valued naturality rules. -/
theorem setCongr_apply_eq_image {α β : Type*} (e : α ≃ β) (S : Set α) :
    Equiv.Set.congr e S = e '' S := rfl

/-- Applying a function transported backwards by `arrowCongr` to an argument transported backwards,
then transporting the result forwards, recovers ordinary target-side application. -/
theorem apply_arrowCongr_symm_apply {α₁ α₂ β₁ β₂ : Sort*}
    (eα : α₁ ≃ α₂) (eβ : β₁ ≃ β₂) (f : α₂ → β₂) (x : α₂) :
    eβ (((Equiv.arrowCongr eα eβ).symm f) (eα.symm x)) = f x := by
  simp [Equiv.arrowCongr]

/-- Pointwise action of the inverse function-space transport. -/
theorem arrowCongr_symm_apply {α₁ α₂ β₁ β₂ : Sort*}
    (eα : α₁ ≃ α₂) (eβ : β₁ ≃ β₂) (f : α₂ → β₂) (x : α₁) :
    ((Equiv.arrowCongr eα eβ).symm f) x = eβ.symm (f (eα x)) := rfl

/-- Forward function-space transport is conjugation by the domain and codomain equivalences.
Stating this at function level lets cleanup descend beneath structural constructors containing a
transported function. -/
theorem arrowCongr_apply_fun {α₁ α₂ β₁ β₂ : Sort*}
    (eα : α₁ ≃ α₂) (eβ : β₁ ≃ β₂) (f : α₁ → β₁) :
    Equiv.arrowCongr eα eβ f = fun x => eβ (f (eα.symm x)) := rfl

/-- Structural transport preserves `Option.none`. -/
theorem optionCongr_none {α β : Type*} (e : α ≃ β) :
    Equiv.optionCongr e none = none := rfl

/-- Forward option transport preserves `some` and transports its payload. -/
theorem optionCongr_some {α β : Type*} (e : α ≃ β) (x : α) :
    Equiv.optionCongr e (some x) = some (e x) := rfl

/-- Forward transport cancels inverse transport beneath `Option.some`. -/
theorem optionCongr_some_symm {α β : Type*} (e : α ≃ β) (x : β) :
    Equiv.optionCongr e (some (e.symm x)) = some x := by
  simp [Equiv.optionCongr]

/-- Rewrite a universally quantified proposition using an equivalence of binder types. -/
theorem forall_congr_equiv {α β : Sort*} (e : α ≃ β)
    {P : α → Prop} {Q : β → Prop} (h : ∀ y, P (e.symm y) ↔ Q y) :
    (∀ x, P x) ↔ ∀ y, Q y := e.forall_congr' h

/-- Rewrite an existentially quantified proposition using an equivalence of binder types. -/
theorem exists_congr_equiv {α β : Sort*} (e : α ≃ β)
    {P : α → Prop} {Q : β → Prop} (h : ∀ y, P (e.symm y) ↔ Q y) :
    (∃ x, P x) ↔ ∃ y, Q y := e.exists_congr' h

/-- Explicit-argument form of `exists_and_left`, used by the existential guard normalizer. -/
theorem exists_and_left_explicit {α : Sort u} (b : Prop) (p : α → Prop) :
    (∃ x, b ∧ p x) ↔ b ∧ ∃ x, p x := exists_and_left

/-- Turn an implication-guarded universal quantifier into a subtype quantifier. -/
theorem forall_guard_to_subtype {α : Sort*} {S : α → Prop} {P : α → Prop} :
    (∀ x, S x → P x) ↔ ∀ x : {x // S x}, P x := by
  constructor
  · intro h x
    exact h x.1 x.2
  · intro h x hx
    exact h ⟨x, hx⟩

/-- Turn a conjunction-guarded existential quantifier into a subtype quantifier. -/
theorem exists_guard_to_subtype {α : Sort*} {S : α → Prop} {P : α → Prop} :
    (∃ x, S x ∧ P x) ↔ ∃ x : {x // S x}, P x := by
  constructor
  · rintro ⟨x, hx, hP⟩
    exact ⟨⟨x, hx⟩, hP⟩
  · rintro ⟨⟨x, hx⟩, hP⟩
    exact ⟨x, hx, hP⟩

/-- Transport a guarded universal directly, preserving ordinary bounded-quantifier syntax. -/
theorem forall_guard_congr_equiv {α β : Sort*} {S : α → Prop} {T : β → Prop}
    (e : {x // S x} ≃ {y // T y}) {P : ∀ x, S x → Prop} {Q : ∀ y, T y → Prop}
    (h : ∀ y hy, P (e.symm ⟨y, hy⟩).1 (e.symm ⟨y, hy⟩).2 ↔ Q y hy) :
    (∀ x hx, P x hx) ↔ ∀ y hy, Q y hy := by
  constructor
  · intro hP y hy
    exact (h y hy).mp <| hP _ _
  · intro hQ x hx
    let y := e ⟨x, hx⟩
    have h' := (h y.1 y.2).mpr (hQ y.1 y.2)
    simpa [y] using h'

/-- Transport a conjunction-guarded existential directly.  The target body is proof-independent,
which is the form produced by ordinary bounded-existential notation. -/
theorem exists_guard_congr_equiv {α β : Sort*} {S : α → Prop} {T : β → Prop}
    (e : {x // S x} ≃ {y // T y})  {P : α → Prop} {Q : β → Prop}
    (h : ∀ y hy, P (e.symm ⟨y, hy⟩).1 ↔ Q y) : (∃ x, S x ∧ P x) ↔ ∃ y, T y ∧ Q y := by
  constructor
  · rintro ⟨x, hx, hP⟩
    let y := e ⟨x, hx⟩
    refine ⟨y.1, y.2, ?_⟩
    exact (h y.1 y.2).mp <| by simpa [y] using hP
  · rintro ⟨y, hy, hQ⟩
    let x := e.symm ⟨y, hy⟩
    refine ⟨x.1, x.2, ?_⟩
    exact (h y hy).mpr hQ

/-! ## Transport-domain descriptors -/

/-- A domain on which the chosen transformation acts everywhere. -/
structure TotalDomain (A : Sort u) (B : Sort v) where
  equiv : A ≃ B

/-- A domain on which the chosen transformation acts only after establishing support. -/
structure SupportedDomain (A : Type u) (B : Type v) where
  sourceSupport : A → Prop
  targetSupport : B → Prop
  equiv : {a // sourceSupport a} ≃ {b // targetSupport b}

/-- Transport an equality of ambient values when both values are known to lie in a supported
domain.  The target equality is stated on ambient values as well, so support proofs remain an
internal implementation detail. -/
theorem eq_congr_supported {α β : Type*} (d : SupportedDomain α β) (x y : α)
    (hx : d.sourceSupport x) (hy : d.sourceSupport y) :
    (x = y) ↔ (d.equiv ⟨x, hx⟩).1 = (d.equiv ⟨y, hy⟩).1 := by
  constructor
  · rintro rfl
    rfl
  · intro h
    have h' : d.equiv ⟨x, hx⟩ = d.equiv ⟨y, hy⟩ := Subtype.ext h
    exact congrArg Subtype.val (d.equiv.injective h')

/-- Ambient sets supported by `S` are equivalent to sets of the support subtype. -/
def supportedSetEquiv {A : Type u} (S : A → Prop) :
    {X : Set A // ∀ ⦃x⦄, x ∈ X → S x} ≃ Set {x // S x} where
  toFun X := Subtype.val ⁻¹' X.1
  invFun T := ⟨Subtype.val '' T, fun _ ⟨x, _, hxy⟩ => hxy ▸ x.2⟩
  left_inv := by
    rintro ⟨X, hX⟩
    ext x
    constructor
    · rintro ⟨⟨y, hy⟩, hyX, rfl⟩
      exact hyX
    · exact fun hx => ⟨⟨x, hX hx⟩, hx, rfl⟩
  right_inv := by
    intro T
    ext ⟨x, hx⟩
    simp

/-- Supported domains lift structurally to ambient sets whose elements are supported. -/
def SupportedDomain.set {A : Type u} {B : Type v} (d : SupportedDomain A B) :
    SupportedDomain (Set A) (Set B) where
  sourceSupport X := ∀ ⦃x⦄, x ∈ X → d.sourceSupport x
  targetSupport Y := ∀ ⦃y⦄, y ∈ Y → d.targetSupport y
  equiv := (supportedSetEquiv d.sourceSupport).trans <|
    (Equiv.Set.congr d.equiv).trans (supportedSetEquiv d.targetSupport).symm

/-- Restrict a universal quantifier to a supported domain when its body is automatic outside that
domain. -/
theorem forall_iff_forall_guard {A : Sort u} {S : A → Prop} {P : A → Prop}
    (outside : ∀ x, ¬ S x → P x) : (∀ x, P x) ↔ ∀ x, S x → P x := by
  constructor
  · exact fun h x _ => h x
  · intro h x
    by_cases hx : S x
    · exact h x hx
    · exact outside x hx

/-- Restrict an existential quantifier to a supported domain when every witness is supported. -/
theorem exists_iff_exists_guard {A : Sort u} {S : A → Prop} {P : A → Prop}
    (supported : ∀ x, P x → S x) : (∃ x, P x) ↔ ∃ x, S x ∧ P x := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, supported x hx, hx⟩
  · rintro ⟨x, _, hx⟩
    exact ⟨x, hx⟩

end IRw

end

/-! ## The tactic itself

Everything below is compile-time code, so it lives in a `meta` section. -/

public meta section

open Lean Meta Elab Elab.Tactic

namespace IRw

/-! ## Registries -/

/-- Identifier of a registered change-of-coordinates system.  Phase 1 uses the head declaration of
the supplied isomorphism type; later registry entries are indexed by this identifier. -/
abbrev SystemId := Name

/-- A system-indexed IRw registration. Higher priorities are considered first, but priorities only
resolve otherwise-overlapping rules; exact matches always outrank definitional matches. -/
structure Registration where
  system : SystemId
  declName : Name
  priority : Nat
  deriving Inhabited, BEq

/-- Transformation/type constructors recognized by `irw` (for example `Graph.Iso` and
`Matroid.Iso`). -/
initialize systemExt : SimpleScopedEnvExtension Name (Array Name) ←
  registerSimpleScopedEnvExtension {
    name := by exact decl_name%
    initial := #[]
    addEntry := fun xs n => xs.push n
  }

/-- Binder-type equivalence rules used by `irw`. -/
initialize equivExt : SimpleScopedEnvExtension Registration (Array Registration) ←
  registerSimpleScopedEnvExtension {
    name := by exact decl_name%
    initial := #[]
    addEntry := fun xs entry => xs.push entry
  }

/-- Primitive total or supported transport-domain rules used by `irw`. -/
initialize domainExt : SimpleScopedEnvExtension Registration (Array Registration) ←
  registerSimpleScopedEnvExtension {
    name := by exact decl_name%
    initial := #[]
    addEntry := fun xs entry => xs.push entry
  }

/-- Canonicalization rules used only by IRw's private, system-indexed normalizer. -/
initialize naturalityExt : SimpleScopedEnvExtension Registration (Array Registration) ←
  registerSimpleScopedEnvExtension {
    name := by exact decl_name%
    initial := #[]
    addEntry := fun xs entry => xs.push entry
  }

/-- Return the registered system whose type constructor is the head of `type`, if any. -/
def registeredSystemForType? (type : Expr) : CoreM (Option SystemId) := do
  let some head := type.getAppFn.constName? | return none
  if (systemExt.getState (← getEnv)).contains head then return some head
  return none

/-- Infer the unique transformation system mentioned by a registration theorem's telescope. -/
def inferRegistrationSystem (declName : Name) : MetaM SystemId := do
  let info ← getConstInfo declName
  forallTelescope info.type fun xs _ => do
    let mut systems : Array SystemId := #[]
    for x in xs do
      let decl ← x.fvarId!.getDecl
      if let some system ← registeredSystemForType? decl.type then
        if !systems.contains system then systems := systems.push system
    match systems.toList with
    | [system] =>
        let mut firstExplicitSystem : Option SystemId := none
        for x in xs do
          let decl ← x.fvarId!.getDecl
          if decl.binderInfo == .default then
            firstExplicitSystem ← registeredSystemForType? decl.type
            break
        unless firstExplicitSystem == some system do
          throwError "IRw registration `{declName}` must take its {system} transformation as its \
            first explicit argument"
        return system
    | [] =>
        throwError "IRw registration `{declName}` does not contain an argument belonging to a \
          registered @[irw_system]"
    | _ =>
        throwError "IRw registration `{declName}` contains arguments from multiple transport \
          systems: {systems.toList}"

def validateSystem (declName : Name) : MetaM Unit := do
  let info ← getConstInfo declName
  let (xs, _, result) ← forallMetaTelescope info.type
  unless (← whnf result).isSort do
    throwError "@[irw_system] declaration `{declName}` must be a type constructor"
  if xs.size < 2 then
    throwError "@[irw_system] declaration `{declName}` must have source and target objects as its \
      final two parameters"

def validateEquiv (declName : Name) : MetaM Unit := do
  let info ← getConstInfo declName
  let (xs, _, conclusion) ← forallMetaTelescope info.type
  if xs.isEmpty then
    throwError "@[irw_equiv] theorem `{declName}` must have an explicit isomorphism argument"
  let conclusion ← whnf conclusion
  unless conclusion.isAppOfArity ``Equiv 2 do
    throwError "@[irw_equiv] theorem `{declName}` must return an Equiv, but returns\n  {conclusion}"

def validateDomain (declName : Name) : MetaM Unit := do
  let info ← getConstInfo declName
  let (xs, _, conclusion) ← forallMetaTelescope info.type
  if xs.isEmpty then
    throwError "@[irw_domain] declaration `{declName}` must have a transformation argument"
  let conclusion ← whnf conclusion
  unless conclusion.isAppOfArity ``IRw.TotalDomain 2 ||
      conclusion.isAppOfArity ``IRw.SupportedDomain 2 do
    throwError "@[irw_domain] declaration `{declName}` must return `TotalDomain` or \
      `SupportedDomain`, but returns\n  {conclusion}"

def validateNaturality (declName : Name) : MetaM Unit := do
  let info ← getConstInfo declName
  let (xs, _, conclusion) ← forallMetaTelescope info.type
  if xs.isEmpty then
    throwError "@[irw_naturality] theorem `{declName}` must have a transformation argument"
  let conclusion ← whnf conclusion
  unless conclusion.isAppOfArity ``Eq 3 || conclusion.isAppOfArity ``Iff 2 do
    throwError "@[irw_naturality] theorem `{declName}` must conclude an equality or iff, but \
      concludes\n  {conclusion}"

/-- Instantiate a naturality theorem and return its oriented left- and right-hand sides. -/
def naturalitySides (declName : Name) : MetaM (Expr × Expr) := do
  let info ← getConstInfo declName
  let (_, _, conclusion) ← forallMetaTelescope info.type
  let conclusion ← whnf conclusion
  if conclusion.isAppOfArity ``Eq 3 then
    let args := conclusion.getAppArgs
    return (args[1]!, args[2]!)
  if conclusion.isAppOfArity ``Iff 2 then
    let args := conclusion.getAppArgs
    return (args[0]!, args[1]!)
  throwError "irw internal error: `{declName}` is not a validated naturality theorem"

/-- Reject equal-priority naturality rules whose left sides overlap but whose proposed canonical
forms disagree. This makes import/declaration order irrelevant and reports the problem at the
second attribute rather than during an unrelated later proof. -/
def validateNaturalityOverlap (system : SystemId) (priority : Nat) (declName : Name) : MetaM Unit :=
  for previous in naturalityExt.getState (← getEnv) do
    if previous.system == system && previous.priority == priority && previous.declName != declName
    then
      let saved ← saveState
      let conflict ← try
          let (lhs, rhs) ← naturalitySides declName
          let (previousLhs, previousRhs) ← naturalitySides previous.declName
          if lhs.getAppFn.constName? != previousLhs.getAppFn.constName? then
            pure false
          else if !(← isDefEq lhs previousLhs) then
            pure false
          else
            pure !(← isDefEq rhs previousRhs)
        catch _ => pure false
      restoreState saved
      if conflict then
        throwError "@[irw_naturality] rule `{declName}` overlaps `{previous.declName}` at \
          priority {priority}, but they produce different canonical forms.\nUse one canonical \
          primitive rule, or give the genuinely more specific rule a higher priority."

syntax (name := irwEquivAttr) "irw_equiv" (ppSpace prio)? : attr
syntax (name := irwSystemAttr) "irw_system" : attr
syntax (name := irwDomainAttr) "irw_domain" (ppSpace prio)? : attr
syntax (name := irwNaturalityAttr) "irw_naturality" (ppSpace prio)? : attr

initialize registerBuiltinAttribute {
  name := `irwSystemAttr
  descr := "register a transformation/type constructor as an `irw` system"
  add := fun declName _stx _kind => do
    MetaM.run' <| validateSystem declName
    systemExt.add declName
}

initialize registerBuiltinAttribute {
  name := `irwEquivAttr
  descr := "register a binder-type equivalence rule for `irw`"
  add := fun declName stx _kind => do
    MetaM.run' <| validateEquiv declName
    let system ← MetaM.run' <| inferRegistrationSystem declName
    let priority ← getAttrParamOptPrio stx[1]
    equivExt.add { system, declName, priority }
}

initialize registerBuiltinAttribute {
  name := `irwDomainAttr
  descr := "register a total or supported transport domain for `irw`"
  add := fun declName stx _kind => do
    MetaM.run' <| validateDomain declName
    let system ← MetaM.run' <| inferRegistrationSystem declName
    let priority ← getAttrParamOptPrio stx[1]
    domainExt.add { system, declName, priority }
}

initialize registerBuiltinAttribute {
  name := `irwNaturalityAttr
  descr := "register a canonicalization rule for IRw's private normalizer"
  add := fun declName stx _kind => do
    MetaM.run' <| validateNaturality declName
    let system ← MetaM.run' <| inferRegistrationSystem declName
    let priority ← getAttrParamOptPrio stx[1]
    MetaM.run' <| validateNaturalityOverlap system priority declName
    naturalityExt.add { system, declName, priority }
}

initialize registerTraceClass `irw
initialize registerTraceClass `irw.rule
initialize registerTraceClass `irw.equiv
initialize registerTraceClass `irw.domain
initialize registerTraceClass `irw.support
initialize registerTraceClass `irw.system
initialize registerTraceClass `irw.context
initialize registerTraceClass `irw.naturality

/-! ## Metaprogramming core

The engine lives in `IRw.Core` rather than `IRw.Meta`: an inner namespace called `Meta` would be
ambiguous with `Lean.Meta`, which this file has open. -/

namespace Core

/-- A source-side local datum and its target-side representative, together with the equivalence and
kernel-checked coherence theorem used to normalize that correspondence. -/
structure LocalTransport where
  source : Expr
  target : Expr
  sourceType : Expr
  targetType : Expr
  equiv : Expr
  coherence : Expr
  deriving Inhabited

/-- Runtime state shared by every IRw subsystem. -/
structure TransportContext where
  system : SystemId
  iso : Expr
  locals : Array LocalTransport := #[]
  deriving Inhabited

/-- The source object is the penultimate argument of a registered binary transformation system.
Carrier and universe parameters may precede it; the target object is the final argument. -/
def TransportContext.sourceObject (ctx : TransportContext) : MetaM Expr := do
  let isoType ← whnf (← instantiateMVars (← inferType ctx.iso))
  let args := isoType.getAppArgs
  if args.size < 2 then
    throwError "irw internal error: a registered transformation has fewer than two object \
      arguments:\n  {isoType}"
  return args[args.size - 2]!

/-- Build the initial context and reject unregistered transformation notions early. -/
def mkTransportContext (iso : Expr) : MetaM TransportContext := do
  let isoType ← instantiateMVars (← inferType iso)
  let some system ← registeredSystemForType? isoType
    | throwError "irw does not recognize the supplied transformation type\n  {isoType}\n\
        Register its type constructor with @[irw_system]."
  trace[irw.system] "recognized system {system} from {isoType}"
  return { system, iso }

inductive MatchQuality where
  | exact
  | defEq
  deriving Inhabited, BEq, Repr

structure PropResult where
  target : Expr
  proof : Expr
  deriving Inhabited

structure EquivResult where
  target : Expr
  equiv : Expr
  deriving Inhabited

structure SupportedResult where
  target : Expr
  sourceSupport : Expr
  targetSupport : Expr
  equiv : Expr
  descriptor : Expr
  deriving Inhabited

inductive DomainResult where
  | total (result : EquivResult)
  | supported (result : SupportedResult)
  deriving Inhabited

def iffSides? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let e ← whnf e
  if e.isAppOfArity ``Iff 2 then
    let args := e.getAppArgs
    return some (args[0]!, args[1]!)
  return none

def equivSides? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let e ← whnf e
  if e.isAppOfArity ``Equiv 2 then
    let args := e.getAppArgs
    return some (args[0]!, args[1]!)
  return none

/-- Split a `Subtype` type into its carrier and predicate. -/
def subtypeParts? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let e ← whnf e
  if e.isAppOfArity ``Subtype 2 then
    let args := e.getAppArgs
    return some (args[0]!, args[1]!)
  return none

def mkIffRefl (p : Expr) : MetaM Expr := mkAppM ``Iff.refl #[p]

/-- Apply an `Equiv` to an argument.  An `Equiv` is not a function, so the application has to go
through the `FunLike` coercion; `mkApp` on the bare equivalence produces an ill-typed term. -/
def mkEquivApply (e x : Expr) : MetaM Expr := mkAppM ``DFunLike.coe #[e, x]

/-- Apply the inverse of an `Equiv` to an argument. -/
def mkEquivSymmApply (e x : Expr) : MetaM Expr := do
  mkEquivApply (← mkAppM ``Equiv.symm #[e]) x

/-- Record the source representative `e.symm target` introduced beneath a transported binder.
The stored coherence theorem is a local normalization rule `e source = target`. -/
def TransportContext.pushTotal (ctx : TransportContext)
    (source target sourceType targetType equiv : Expr) : MetaM TransportContext := do
  let coherence ← mkAppM ``Equiv.apply_symm_apply #[equiv, target]
  check coherence
  let coherenceType ← whnf (← inferType coherence)
  unless coherenceType.isAppOfArity ``Eq 3 do
    throwError "irw internal error: local transport coherence is not an equality"
  let sides := coherenceType.getAppArgs
  let transportedSource ← mkEquivApply equiv source
  unless ← isDefEq sides[1]! transportedSource do
    throwError "irw internal error: local transport has the wrong source representative"
  unless ← isDefEq sides[2]! target do
    throwError "irw internal error: local transport has the wrong target representative"
  trace[irw.context] "recording local transport\n  source: {source}\n  target: {target}\n\
    source type: {sourceType}\n  target type: {targetType}"
  return { ctx with locals := ctx.locals.push {
    source, target, sourceType, targetType, equiv, coherence } }

/-- Check every proof produced by the tactic before it can be installed into a goal.  This is
intentionally more defensive than most tactics: failures in metaprograms are otherwise liable to
surface only much later as kernel errors. -/
def checkedPropResult (source : Expr) (r : PropResult) : MetaM PropResult := do
  let proof ← instantiateMVars r.proof
  let target ← instantiateMVars r.target
  if proof.hasExprMVar || target.hasExprMVar then
    throwError "irw internal error: unresolved metavariables remained while transporting\n  \
      {source}\ntarget:\n  {target}"
  check proof
  let proofTy ← inferType proof
  let some (lhs, rhs) ← iffSides? proofTy
    | throwError "irw internal error: generated proof is not an iff proof:\n  {proofTy}"
  unless ← isDefEq lhs source do
    throwError "irw internal error: generated proof has wrong source\nexpected:\n  \
      {source}\nactual:\n  {lhs}"
  unless ← isDefEq rhs target do
    throwError "irw internal error: generated proof has wrong target\nexpected:\n  \
      {target}\nactual:\n  {rhs}"
  return { target, proof }

def checkedEquivResult (source : Expr) (r : EquivResult) : MetaM EquivResult := do
  let equiv ← instantiateMVars r.equiv
  let target ← instantiateMVars r.target
  if equiv.hasExprMVar || target.hasExprMVar then
    throwError "irw internal error: unresolved metavariables remained in binder transport\n  \
      {source}"
  check equiv
  let ty ← inferType equiv
  let some (lhs, rhs) ← equivSides? ty
    | throwError "irw internal error: generated binder transport is not an Equiv:\n  {ty}"
  unless ← isDefEq lhs source do
    throwError "irw internal error: generated binder equivalence has wrong source\nexpected:\n  \
      {source}\nactual:\n  {lhs}"
  unless ← isDefEq rhs target do
    throwError "irw internal error: generated binder equivalence has wrong target\nexpected:\n  \
      {target}\nactual:\n  {rhs}"
  return { target, equiv }

def checkedSupportedResult (source : Expr) (r : SupportedResult) : MetaM SupportedResult := do
  let target ← instantiateMVars r.target
  let sourceSupport ← instantiateMVars r.sourceSupport
  let targetSupport ← instantiateMVars r.targetSupport
  let equiv ← instantiateMVars r.equiv
  let descriptor ← instantiateMVars r.descriptor
  if target.hasExprMVar || sourceSupport.hasExprMVar || targetSupport.hasExprMVar ||
      equiv.hasExprMVar || descriptor.hasExprMVar then
    throwError "irw internal error: unresolved metavariables remained in a supported domain"
  check descriptor
  check sourceSupport
  check targetSupport
  check equiv
  let descriptorType ← whnf (← inferType descriptor)
  unless descriptorType.isAppOfArity ``IRw.SupportedDomain 2 do
    throwError "irw internal error: supported-domain descriptor has type\n  {descriptorType}"
  let descriptorArgs := descriptorType.getAppArgs
  unless ← isDefEq descriptorArgs[0]! source do
    throwError "irw internal error: supported domain has the wrong source type"
  unless ← isDefEq descriptorArgs[1]! target do
    throwError "irw internal error: supported domain has the wrong target type"
  return { target, sourceSupport, targetSupport, equiv, descriptor }

def supportedResultFromDescriptor (source descriptor : Expr) : MetaM SupportedResult := do
  let descriptorType ← whnf (← inferType descriptor)
  unless descriptorType.isAppOfArity ``IRw.SupportedDomain 2 do
    throwError "irw internal error: expected a supported-domain descriptor, got\n  {descriptorType}"
  let args := descriptorType.getAppArgs
  let target ← instantiateMVars args[1]!
  let sourceSupport ← instantiateMVars
    (← mkAppM ``IRw.SupportedDomain.sourceSupport #[descriptor])
  let targetSupport ← instantiateMVars
    (← mkAppM ``IRw.SupportedDomain.targetSupport #[descriptor])
  let equiv ← instantiateMVars (← mkAppM ``IRw.SupportedDomain.equiv #[descriptor])
  checkedSupportedResult source { target, sourceSupport, targetSupport, equiv, descriptor }

/-- Try a registered theorem by applying the supplied isomorphism as its first explicit argument,
then using unification against `source` to infer all remaining theorem arguments.  Failed attempts
are backtracked completely. -/
def tryRule (declName : Name) (ctx : TransportContext) (source : Expr) :
    MetaM (Option (MatchQuality × PropResult)) :=
  commitWhenSomeNoEx? do
    let applied ← mkAppM declName #[ctx.iso]
    let appliedTy ← inferType applied
    let (xs, _, conclusion) ← forallMetaTelescope appliedTy
    let proof := mkAppN applied xs
    let some (lhs, rhs) ← iffSides? conclusion | return none
    unless ← isDefEq lhs source do return none
    let lhs ← instantiateMVars lhs
    let source ← instantiateMVars source
    let quality := if lhs == source then MatchQuality.exact else MatchQuality.defEq
    let proof ← instantiateMVars proof
    let rhs ← instantiateMVars rhs
    if proof.hasExprMVar || rhs.hasExprMVar then return none
    trace[irw.rule] "rule {declName} matched {source} with {repr quality} quality and \
      produced {rhs}"
    return some (quality, ← checkedPropResult source { target := rhs, proof })

def tryEquivRule (declName : Name) (ctx : TransportContext) (source : Expr) :
    MetaM (Option (MatchQuality × EquivResult)) :=
  commitWhenSomeNoEx? do
    let applied ← mkAppM declName #[ctx.iso]
    let ty ← inferType applied
    -- An equivalence rule is expected to have all data arguments inferable from its source type.
    -- We still permit explicit trailing arguments and solve them by unification against the source.
    let (xs, _, conclusion) ← forallMetaTelescope ty
    let equiv := mkAppN applied xs
    let some (lhs, rhs) ← equivSides? conclusion | return none
    unless ← isDefEq lhs source do return none
    let lhs ← instantiateMVars lhs
    let source ← instantiateMVars source
    let quality := if lhs == source then MatchQuality.exact else MatchQuality.defEq
    let equiv ← instantiateMVars equiv
    let rhs ← instantiateMVars rhs
    if equiv.hasExprMVar || rhs.hasExprMVar then return none
    trace[irw.equiv] "equiv rule {declName} matched {source} with {repr quality} quality and \
      produced {rhs}"
    return some (quality, ← checkedEquivResult source { target := rhs, equiv })

def tryRegisteredEquiv (ctx : TransportContext) (source : Expr) : MetaM (Option EquivResult) := do
  let mut exactMatch : Option (Registration × EquivResult) := none
  let mut defEqMatch : Option (Registration × EquivResult) := none
  for registration in equivExt.getState (← getEnv) do
    if registration.system == ctx.system then
      if let some (quality, r) ← tryEquivRule registration.declName ctx source then
        let update (current : Option (Registration × EquivResult)) := do
          let some (previous, previousResult) := current
            | return some (registration, r)
          if registration.priority > previous.priority then
            return some (registration, r)
          if registration.priority < previous.priority then return current
          unless (← withNewMCtxDepth <| isDefEq previousResult.target r.target) &&
              (← withNewMCtxDepth <| isDefEq previousResult.equiv r.equiv) do
            throwError "irw found ambiguous binder equivalences for\n  {source}\n\
              candidates at priority {registration.priority}: `{previous.declName}` and \
              `{registration.declName}`"
          return current
        if quality == .exact then
          exactMatch ← update exactMatch
        else
          defEqMatch ← update defEqMatch
  return match exactMatch with
    | some (_, r) => some r
    | none => defEqMatch.map (fun (_, r) ↦ r)

/-- Find the registered binder equivalence which is definitionally the equivalence stored in a
supported-domain descriptor.  Unlike ordinary binder lookup, coherence with the descriptor can
disambiguate two roles whose support subtypes are definitionally equal. -/
def tryCoherentRegisteredEquiv (ctx : TransportContext) (source equiv : Expr) :
    MetaM (Option EquivResult) := do
  let mut bestExact : Option (Registration × EquivResult) := none
  let mut bestDefEq : Option (Registration × EquivResult) := none
  for registration in equivExt.getState (← getEnv) do
    if registration.system == ctx.system then
      if let some (quality, result) ← tryEquivRule registration.declName ctx source then
        if ← withNewMCtxDepth <| isDefEq equiv result.equiv then
          if quality == .exact then
            if bestExact.isNone || registration.priority > bestExact.get!.1.priority then
              bestExact := some (registration, result)
          else if bestDefEq.isNone || registration.priority > bestDefEq.get!.1.priority then
            bestDefEq := some (registration, result)
  let best := match bestExact with
    | some result => some result
    | none => bestDefEq
  return best.map (fun (_, result) ↦ result)

/-- Replace the implementation field of a supported-domain descriptor by a registered, named
equivalence when the two are definitionally equal.  Naturality rules can then state their target
using the public equivalence and the cleanup pass sees the syntactic `e (e.symm x)` cancellation.
This applies equally to primitive supported domains and to structurally derived ones such as
supported sets. -/
def canonicalizeSupportedResult (ctx : TransportContext) (result : SupportedResult) :
    MetaM SupportedResult := do
  let sourceSubtype ← mkAppM ``Subtype #[result.sourceSupport]
  let some canonical ← tryCoherentRegisteredEquiv ctx sourceSubtype result.equiv
    | return result
  let canonicalType ← inferType canonical.equiv
  let some (canonicalSource, canonicalTarget) ← equivSides? canonicalType
    | return result
  let some (_, sourceSupport) ← subtypeParts? canonicalSource
    | return result
  let some (_, targetSupport) ← subtypeParts? canonicalTarget
    | return result
  return { result with sourceSupport, targetSupport, equiv := canonical.equiv }

def tryDomainRule (declName : Name) (ctx : TransportContext) (source : Expr) :
    MetaM (Option (MatchQuality × DomainResult)) :=
  commitWhenSomeNoEx? do
    let applied ← mkAppM declName #[ctx.iso]
    let appliedType ← inferType applied
    let (xs, _, conclusion) ← forallMetaTelescope appliedType
    let descriptor := mkAppN applied xs
    let conclusion ← whnf conclusion
    if conclusion.isAppOfArity ``IRw.TotalDomain 2 then
      let args := conclusion.getAppArgs
      unless ← isDefEq args[0]! source do return none
      let lhs ← instantiateMVars args[0]!
      let source ← instantiateMVars source
      let quality := if lhs == source then MatchQuality.exact else MatchQuality.defEq
      let target ← instantiateMVars args[1]!
      let equiv ← instantiateMVars (← mkAppM ``IRw.TotalDomain.equiv #[descriptor])
      if target.hasExprMVar || equiv.hasExprMVar then return none
      let result ← checkedEquivResult source { target, equiv }
      trace[irw.domain] "total domain {declName} matched {source} with {repr quality} quality"
      return some (quality, .total result)
    if conclusion.isAppOfArity ``IRw.SupportedDomain 2 then
      let args := conclusion.getAppArgs
      unless ← isDefEq args[0]! source do return none
      let lhs ← instantiateMVars args[0]!
      let source ← instantiateMVars source
      let quality := if lhs == source then MatchQuality.exact else MatchQuality.defEq
      let result ← canonicalizeSupportedResult ctx
        (← supportedResultFromDescriptor source descriptor)
      trace[irw.domain] "supported domain {declName} matched {source} with {repr quality} quality"
      return some (quality, .supported result)
    return none

def registeredDomainCandidates (ctx : TransportContext) (source : Expr) :
    MetaM (Array (Name × DomainResult)) := do
  let mut exactMatches : Array (Name × DomainResult) := #[]
  let mut defEqMatches : Array (Name × DomainResult) := #[]
  let mut exactPriority : Option Nat := none
  let mut defEqPriority : Option Nat := none
  for registration in domainExt.getState (← getEnv) do
    if registration.system == ctx.system then
      if let some (quality, result) ← tryDomainRule registration.declName ctx source then
        let entry := (registration.declName, result)
        if quality == .exact then
          if exactPriority.isNone || registration.priority > exactPriority.get! then
            exactPriority := some registration.priority
            exactMatches := #[entry]
          else if registration.priority == exactPriority.get! then
            exactMatches := exactMatches.push entry
        else if defEqPriority.isNone || registration.priority > defEqPriority.get! then
          defEqPriority := some registration.priority
          defEqMatches := #[entry]
        else if registration.priority == defEqPriority.get! then
          defEqMatches := defEqMatches.push entry
  if !exactMatches.isEmpty then return exactMatches
  return defEqMatches

def tryRegisteredDomain (ctx : TransportContext) (source : Expr) : MetaM (Option DomainResult) := do
  let candidates ← registeredDomainCandidates ctx source
  if h : candidates.size > 1 then
    let firstName := candidates[0].1
    let secondName := candidates[1].1
    throwError "irw found ambiguous exact domain rules for\n  {source}\n\
      candidates: `{firstName}` and `{secondName}`"
  return candidates[0]?.map (fun candidate => candidate.2)

/-- Try proposition-valued naturality declarations as atomic transport facts. Equality-valued
declarations are ignored here and remain private-normalizer rules. -/
def tryRegisteredNaturalityProp (ctx : TransportContext) (source : Expr) :
    MetaM (Option PropResult) := do
  let mut exactMatch : Option (Registration × PropResult) := none
  let mut defEqMatch : Option (Registration × PropResult) := none
  for registration in naturalityExt.getState (← getEnv) do
    if registration.system == ctx.system then
      if let some (quality, r) ← tryRule registration.declName ctx source then
        let update (current : Option (Registration × PropResult)) := do
          let some (previous, previousResult) := current
            | return some (registration, r)
          if registration.priority > previous.priority then
            return some (registration, r)
          if registration.priority < previous.priority then return current
          unless ← withNewMCtxDepth <| isDefEq previousResult.target r.target do
            throwError "irw found ambiguous proposition-valued naturality rules for\n  \
              {source}\n  candidates at priority {registration.priority}: \
              `{previous.declName}` and `{registration.declName}`"
          return current
        if quality == .exact then
          exactMatch ← update exactMatch
        else
          defEqMatch ← update defEqMatch
  return match exactMatch with
    | some (_, r) => some r
    | none => defEqMatch.map (fun (_, r) ↦ r)

def mkReflEquiv (α : Expr) : MetaM EquivResult := do
  let e ← mkAppM ``Equiv.refl #[α]
  checkedEquivResult α { target := α, equiv := e }

def isConstApp (e : Expr) (n : Name) (arity : Nat) : Bool :=
  e.isAppOfArity n arity

/-- Derive an equivalence for a quantified binder type. Domain-specific equivalences are tried
first; afterwards the routine structurally closes under elementary type constructors. A final
reflexive fallback is intentional: genuinely object-independent binder types (`Nat`, a fixed index
type, etc.) should remain unchanged. -/
partial def deriveEquiv (ctx : TransportContext) (source : Expr) : MetaM EquivResult := do
  let source ← instantiateMVars source
  trace[irw.equiv] "transporting binder type {source}"
  if let some (.total result) ← tryRegisteredDomain ctx source then return result
  if let some r ← tryRegisteredEquiv ctx source then return r

  -- Keep reducible type constructors such as `Set` visible.  `whnf` would unfold `Set α`
  -- to `α → Prop`, losing exactly the structural head we want to recurse through.
  let s := source
  -- Set
  if isConstApp s ``Set 1 then
    let α := s.getAppArgs[0]!
    let ea ← deriveEquiv ctx α
    let e ← mkAppM ``Equiv.Set.congr #[ea.equiv]
    let ty ← inferType e
    let some (_, target) ← equivSides? ty | throwError "irw internal error in Set equivalence"
    return ← checkedEquivResult source { target, equiv := e }

  -- Product
  if isConstApp s ``Prod 2 then
    let args := s.getAppArgs
    let ea ← deriveEquiv ctx args[0]!
    let eb ← deriveEquiv ctx args[1]!
    let e ← mkAppM ``Equiv.prodCongr #[ea.equiv, eb.equiv]
    let ty ← inferType e
    let some (_, target) ← equivSides? ty | throwError "irw internal error in product equivalence"
    return ← checkedEquivResult source { target, equiv := e }

  -- Sum
  if isConstApp s ``Sum 2 then
    let args := s.getAppArgs
    let ea ← deriveEquiv ctx args[0]!
    let eb ← deriveEquiv ctx args[1]!
    let e ← mkAppM ``Equiv.sumCongr #[ea.equiv, eb.equiv]
    let ty ← inferType e
    let some (_, target) ← equivSides? ty | throwError "irw internal error in sum equivalence"
    return ← checkedEquivResult source { target, equiv := e }

  -- Option
  if isConstApp s ``Option 1 then
    let α := s.getAppArgs[0]!
    let ea ← deriveEquiv ctx α
    let e ← mkAppM ``Equiv.optionCongr #[ea.equiv]
    let ty ← inferType e
    let some (_, target) ← equivSides? ty | throwError "irw internal error in option equivalence"
    return ← checkedEquivResult source { target, equiv := e }

  -- Nondependent function.  Dependent Pi transport is deliberately out of scope for now.
  if let .forallE _ domain body bi := s then
    if bi == .default && !body.hasLooseBVar 0 then
      let ea ← deriveEquiv ctx domain
      let eb ← deriveEquiv ctx body
      let e ← mkAppM ``Equiv.arrowCongr #[ea.equiv, eb.equiv]
      let ty ← inferType e
      let some (_, target) ← equivSides? ty
        | throwError "irw internal error in function equivalence"
      return ← checkedEquivResult source { target, equiv := e }

  -- Fixed binder type: leave it alone.  This is semantically a constant family.  If the body
  -- actually needs a transported active object, recursive leaf matching will fail loudly rather
  -- than silently inventing a transport of the ambient carrier.
  return ← mkReflEquiv source

/-- Resolve a primitive supported/total domain first, then fall back to the legacy total-domain
engine and its structural closure. -/
partial def findDomain (ctx : TransportContext) (source : Expr) : MetaM DomainResult := do
  if let some result ← tryRegisteredDomain ctx source then return result
  if isConstApp source ``Set 1 then
    let elementType := source.getAppArgs[0]!
    if let .supported elementDomain ← findDomain ctx elementType then
      let descriptor ← mkAppM ``IRw.SupportedDomain.set #[elementDomain.descriptor]
      trace[irw.domain] "derived supported Set domain for {source}"
      return .supported (← canonicalizeSupportedResult ctx
        (← supportedResultFromDescriptor source descriptor))
  return .total (← deriveEquiv ctx source)

/-- Lemmas used to tidy up the transported proposition.

This must stay a *small, targeted* list.  Running the full default simp set here is actively
harmful: lemmas such as `Set.image_subset_image_iff` and `Set.mem_image_equiv` rewrite a
transported `⇑e '' S ⊆ ⇑e '' T` straight back to `S ⊆ T`, so `irw` would faithfully build a
transport proof and then throw it away, leaving the goal untouched. -/
def cleanupLemmas : List Name :=
  [``Equiv.apply_symm_apply, ``Equiv.symm_apply_apply, ``Equiv.refl_apply, ``Equiv.refl_symm,
   ``Equiv.coe_refl, ``Equiv.symm_symm, ``IRw.prodCongr_symm_apply_fst,
   ``IRw.prodCongr_symm_apply_snd, ``IRw.prodCongr_apply_mk,
   ``IRw.sumCongr_apply_inl, ``IRw.sumCongr_apply_inr, ``IRw.image_setCongr_symm_apply,
   ``IRw.setCongr_apply_eq_image,
   ``IRw.apply_arrowCongr_symm_apply, ``IRw.arrowCongr_symm_apply, ``IRw.arrowCongr_apply_fun,
   ``IRw.optionCongr_none, ``IRw.optionCongr_some, ``IRw.optionCongr_some_symm,
   ``Set.image_id, ``Set.image_id']

def simplifyTarget (ctx : TransportContext) (source : Expr) (r : PropResult) :
    MetaM PropResult := do
  let naturalityRules := (naturalityExt.getState (← getEnv)).filter fun registration ↦
    registration.system == ctx.system
  let mut simpCtx ← Simp.Context.ofNames cleanupLemmas true
  let mut simpTheorems := simpCtx.simpTheorems
  for registration in naturalityRules do
    if simpTheorems.isEmpty then
      let thms : SimpTheorems := {}
      simpTheorems := #[← thms.addConst registration.declName (prio := registration.priority)]
    else
      simpTheorems ← simpTheorems.modifyM 0 fun thms ↦
        thms.addConst registration.declName (prio := registration.priority)
  for i in [:ctx.locals.size] do
    let entry := ctx.locals[i]!
    let origin := Origin.other <| Name.str `_irw.local (toString i)
    simpTheorems ← simpTheorems.addTheorem origin entry.coherence
      (config := simpCtx.indexConfig)
  simpCtx := simpCtx.setSimpTheorems simpTheorems
  if !ctx.locals.isEmpty then
    trace[irw.context] "normalizing with {ctx.locals.size} local transport correspondence(s)"
  if !naturalityRules.isEmpty then
    let traceRules := naturalityRules.map fun registration ↦
      (registration.declName, registration.priority)
    trace[irw.naturality] "normalizing with system rules {traceRules.toList}"
  let (sr, _) ← simp r.target simpCtx
  let some eqProof := sr.proof? | return r
  if sr.expr == r.target then return r
  let proof ← mkAppM ``IRw.iff_trans_eq #[r.proof, eqProof]
  checkedPropResult source { target := sr.expr, proof }

def mkBinaryCongr (ctx : TransportContext) (source : Expr) (lemmaName : Name)
    (rl rr : PropResult) : MetaM PropResult := do
  let proof ← mkAppM lemmaName #[rl.proof, rr.proof]
  let ty ← inferType proof
  let some (_, target) ← iffSides? ty
    | throwError "irw internal error: {lemmaName} did not produce iff"
  simplifyTarget ctx source (← checkedPropResult source { target, proof })

def mkNotCongr (ctx : TransportContext) (source : Expr) (r : PropResult) : MetaM PropResult := do
  let proof ← mkAppM ``not_congr #[r.proof]
  let ty ← inferType proof
  let some (_, target) ← iffSides? ty
    | throwError "irw internal error: not_congr did not produce iff"
  simplifyTarget ctx source (← checkedPropResult source { target, proof })

def isNondependentForall (body : Expr) : Bool := !body.hasLooseBVar 0

partial def occursFVar (id : FVarId) : Expr → Bool
  | .fvar id' => id == id'
  | .app f a => occursFVar id f || occursFVar id a
  | .lam _ d b _ => occursFVar id d || occursFVar id b
  | .forallE _ d b _ => occursFVar id d || occursFVar id b
  | .letE _ t v b _ => occursFVar id t || occursFVar id v || occursFVar id b
  | .mdata _ e => occursFVar id e
  | .proj _ _ e => occursFVar id e
  | _ => false

/-- Syntactic occurrence of an arbitrary expression, rather than only a free variable. -/
partial def occursExpr (needle : Expr) : Expr → Bool
  | e@(.app f a) => e == needle || occursExpr needle f || occursExpr needle a
  | e@(.lam _ d b _) => e == needle || occursExpr needle d || occursExpr needle b
  | e@(.forallE _ d b _) => e == needle || occursExpr needle d || occursExpr needle b
  | e@(.letE _ t v b _) =>
      e == needle || occursExpr needle t || occursExpr needle v || occursExpr needle b
  | e@(.mdata _ body) => e == needle || occursExpr needle body
  | e@(.proj _ _ body) => e == needle || occursExpr needle body
  | e => e == needle

/-- Check dependency through both an expression and the types of the free variables it contains.
The latter matters for an opaque `Q x`: the term does not spell the source object, but the types of
`Q` and `x` do. -/
partial def dependsOnExpr (needle e : Expr) (seen : Array FVarId := #[]) : MetaM Bool := do
  if occursExpr needle e then return true
  match e with
  | .fvar id =>
      if seen.contains id then return false
      let decl ← id.getDecl
      let seen := seen.push id
      if ← dependsOnExpr needle decl.type seen then return true
      if let some value := decl.value? then dependsOnExpr needle value seen else return false
  | .app f a => return (← dependsOnExpr needle f seen) || (← dependsOnExpr needle a seen)
  | .lam _ d b _ | .forallE _ d b _ =>
      return (← dependsOnExpr needle d seen) || (← dependsOnExpr needle b seen)
  | .letE _ t v b _ =>
      return (← dependsOnExpr needle t seen) || (← dependsOnExpr needle v seen) ||
        (← dependsOnExpr needle b seen)
  | .mdata _ body | .proj _ _ body => dependsOnExpr needle body seen
  | _ => return false

/-- An opaque proposition is fixed only when it is independent of both the source object and every
source-side representative introduced beneath transported binders. -/
def isFixedAtom (ctx : TransportContext) (source : Expr) : MetaM Bool := do
  if ← dependsOnExpr (← ctx.sourceObject) source then return false
  for entry in ctx.locals do
    if occursExpr entry.source source then return false
  return true

partial def supportProofFromHyp? (goal h : Expr) (depth : Nat) : MetaM (Option Expr) := do
  if depth == 0 then return none
  let type ← instantiateMVars (← inferType h)
  if ← withNewMCtxDepth <| isDefEq type goal then return some h
  let type ← whnf type
  if type.isAppOfArity ``And 2 then
    let left ← mkAppM ``And.left #[h]
    if let some proof ← supportProofFromHyp? goal left (depth - 1) then return some proof
    let right ← mkAppM ``And.right #[h]
    if let some proof ← supportProofFromHyp? goal right (depth - 1) then return some proof
  return none

/-- Recognize a set-subset proposition without unfolding it to a dependent function type. -/
def setSubsetSides? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let e ← instantiateMVars e
  if e.isAppOfArity ``LE.le 4 || e.isAppOfArity ``HasSubset.Subset 4 then
    let args := e.getAppArgs
    if args[0]!.isAppOfArity ``Set 1 then
      return some (args[2]!, args[3]!)
  -- Domain descriptors often hide the same proposition behind reducible projections.  Recover
  -- its endpoints by checked unification with a fresh `Set.Subset` proposition.
  let some headName := e.getAppFn.constName? | return none
  unless headName == ``IRw.SupportedDomain.sourceSupport ||
      headName == ``IRw.SupportedDomain.targetSupport do return none
  let reduced ← whnf e
  let .forallE _ elementType _ _ := reduced | return none
  commitWhenSomeNoEx? do
    let setType ← mkAppM ``Set #[elementType]
    let left ← mkFreshExprMVar setType
    let right ← mkFreshExprMVar setType
    let candidate ← mkAppM ``Set.Subset #[left, right]
    unless ← isDefEq e candidate do return none
    let left ← instantiateMVars left
    let right ← instantiateMVars right
    if left.hasExprMVar || right.hasExprMVar then return none
    return some (left, right)

/-- Close set support obligations under transitivity of locally available subset hypotheses. -/
partial def proveSubset? (left right : Expr) (depth : Nat) : MetaM (Option Expr) := do
  if depth == 0 then return none
  let target ← mkAppM ``Set.Subset #[left, right]
  for fvarId in (← getPropHyps) do
    let h := mkFVar fvarId
    let hType ← instantiateMVars (← inferType h)
    if ← withNewMCtxDepth <| isDefEq hType target then return some h
    let some (hLeft, hRight) ← setSubsetSides? hType | continue
    unless ← withNewMCtxDepth <| isDefEq hLeft left do continue
    if ← withNewMCtxDepth <| isDefEq hRight right then return some h
    if let some tail ← proveSubset? hRight right (depth - 1) then
      return some (← mkAppM ``Set.Subset.trans #[h, tail])
  return none

/-- Small initial support prover.  It intentionally uses only local hypotheses and elementary
propositional decomposition; Phase 6 can replace the backend with restricted `grind` without
changing this interface. -/
partial def proveSupport? (ctx : TransportContext) (goal : Expr) (depth : Nat := 16) :
    MetaM (Option Expr) := do
  if depth == 0 then return none
  let goal ← instantiateMVars goal
  for fvarId in (← getPropHyps) do
    if let some proof ← supportProofFromHyp? goal (.fvar fvarId) depth then
      trace[irw.support] "proved {goal} from local hypothesis {mkFVar fvarId}"
      return some proof
  -- A coerced element of a support subtype carries the required proof even though its
  -- `Subtype.property` is not a proposition-valued local declaration in the context.
  if let some value := goal.getAppArgs.back? then
    let value ← whnf value
    if value.isAppOfArity ``Subtype.val 3 then
      let element := value.getAppArgs[2]!
      let property ← mkAppM ``Subtype.property #[element]
      let propertyType ← inferType property
      if ← withNewMCtxDepth <| isDefEq propertyType goal then
        trace[irw.support] "proved {goal} from {element}'s subtype property"
        return some property
  let subsetSides ← setSubsetSides? goal
  if let some (left, right) := subsetSides then
    if let some proof ← proveSubset? left right depth then
      trace[irw.support] "proved {goal} by subset transitivity"
      return some proof
  let reduced ← whnf goal
  if reduced.isConstOf ``True then return some (mkConst ``True.intro)
  if reduced.isAppOfArity ``And 2 then
    let args := reduced.getAppArgs
    let some left ← proveSupport? ctx args[0]! (depth - 1) | return none
    let some right ← proveSupport? ctx args[1]! (depth - 1) | return none
    return some (← mkAppM ``And.intro #[left, right])
  if reduced.isAppOfArity ``Or 2 then
    let args := reduced.getAppArgs
    if let some left ← proveSupport? ctx args[0]! (depth - 1) then
      return some (← mkAppOptM ``Or.inl #[args[0]!, args[1]!, left])
    if let some right ← proveSupport? ctx args[1]! (depth - 1) then
      return some (← mkAppOptM ``Or.inr #[args[0]!, args[1]!, right])
    return none
  if let .forallE n domain body bi := reduced then
    return ← withLocalDecl n bi domain fun h => do
      let consequent := body.instantiate1 h
      let some proof ← proveSupport? ctx consequent (depth - 1) | return none
      return some (← mkLambdaFVars #[h] proof)
  -- Forward-chain local implications whose conclusions may provide the goal or a useful conjunct.
  -- In particular, use a local negated support hypothesis before considering case splits.
  for fvarId in (← getPropHyps) do
    let h := mkFVar fvarId
    let type ← instantiateMVars (← inferType h)
    let type ← if type.isAppOfArity ``Not 1 then whnf type else pure type
    if let .forallE _ premise conclusion _ := type then
      if (← isProp premise) && isNondependentForall conclusion then
        if let some premiseProof ← proveSupport? ctx premise (depth - 1) then
          let consequence := mkApp h premiseProof
          if let some proof ← supportProofFromHyp? goal consequence (depth - 1) then
            trace[irw.support] "proved {goal} by forward-chaining {h}"
            return some proof
  -- For a non-subset goal, contradiction is preferable to splitting every disjunctive fact in
  -- the context.  Do not use this path for subset goals: proving the contradiction would ask for
  -- the same support proposition again.
  if subsetSides.isNone && !reduced.isConstOf ``False then
    if let some hFalse ← proveSupport? ctx (mkConst ``False) (depth - 1) then
      return some (← mkAppOptM ``False.elim #[goal, hFalse])
  -- A disjunctive local fact may establish support in either branch.  Both branch proofs are
  -- checked independently before constructing the elimination term.  This comes after direct
  -- subset closure so recursive branches do not reconsider the same disjunction unnecessarily.
  for fvarId in (← getPropHyps) do
    let h := mkFVar fvarId
    let type ← instantiateMVars (← inferType h)
    if type.isAppOfArity ``Or 2 then
      let args := type.getAppArgs
      let some leftFn ← withLocalDecl `h_left .default args[0]! fun hLeft => do
          let some leftProof ← proveSupport? ctx goal (depth - 1) | return none
          return some (← mkLambdaFVars #[hLeft] leftProof)
        | continue
      let some rightFn ← withLocalDecl `h_right .default args[1]! fun hRight => do
          let some rightProof ← proveSupport? ctx goal (depth - 1) | return none
          return some (← mkLambdaFVars #[hRight] rightProof)
        | continue
      let proof ← mkAppM ``Or.elim #[h, leftFn, rightFn]
      trace[irw.support] "proved {goal} by cases on {h}"
      return some proof
  return none

/-- Resource-bounded `grind` configuration for support certificates.  Arithmetic, extensionality,
congruence-closure extras, and the global `@[grind]` theorem database are deliberately disabled. -/
def supportGrindConfig : Lean.Grind.Config where
  locals := false
  splits := 12
  ematch := 4
  gen := 6
  genLocal := 6
  instances := 128
  matchEqs := false
  splitMatch := false
  splitIte := false
  splitIndPred := false
  splitImp := true
  canonHeartbeats := 200
  ext := false
  etaStruct := false
  funext := false
  lookahead := false
  verbose := false
  clean := false
  mbtc := false
  ring := false
  linarith := false
  lia := false
  ac := false
  inj := false
  order := false
  useSorry := false
  funCC := false

def mkSupportGrindParams : MetaM Lean.Meta.Grind.Params := do
  let structural ← Lean.Meta.Grind.getOnlyExtensionState
  let some supportExt ← Lean.Meta.Grind.getExtension? `irw_support
    | throwError "irw internal error: the `irw_support` grind extension is unavailable"
  let supportRules := supportExt.getState (← getEnv)
  Lean.Meta.Grind.mkParams supportGrindConfig #[structural, supportRules]

/-- Try the restricted support-specific `grind` database and the current local context. -/
def proveSupportWithGrind? (goal : Expr) : MetaM (Option Expr) :=
  commitWhenSomeNoEx? do
    let goal ← whnf goal
    let proof ← mkFreshExprSyntheticOpaqueMVar goal `irw.support
    let result ← Lean.Meta.Grind.main proof.mvarId! (← mkSupportGrindParams)
    if result.failure?.isSome then return none
    let proof ← instantiateMVars proof
    if proof.hasExprMVar then return none
    check proof
    trace[irw.support] "proved {goal} with restricted grind"
    return some proof

def proveSupport (ctx : TransportContext) (goal : Expr) : MetaM Expr := do
  let proof ← match ← proveSupport? ctx goal with
    | some proof => pure proof
    | none =>
        let some proof ← proveSupportWithGrind? goal
          | throwError "irw could not establish the support requirement\n  {goal}"
        pure proof
  check proof
  return proof

/-- Collect support proofs carried by subtype-valued subterms.  This exposes facts such as the
`IsWalk` proof bundled into a supported walk when proving support for one of its endpoints. -/
partial def subtypePropertiesIn (term : Expr) : MetaM (Array Expr) := do
  let mut properties := #[]
  let termType? ← try
      pure (some (← instantiateMVars (← inferType term)))
    catch _ => pure none
  if let some termType := termType? then
    if (← subtypeParts? termType).isSome then
      properties := properties.push (← mkAppM ``Subtype.property #[term])
  match term with
  | .app f a =>
      properties := properties ++ (← subtypePropertiesIn f)
      properties := properties ++ (← subtypePropertiesIn a)
  | .proj _ _ value | .mdata _ value =>
      properties := properties ++ (← subtypePropertiesIn value)
  | _ => pure ()
  return properties

/-- Prove support using a genuine subtype property contained in `term` as an explicit premise,
then discharge that premise with its bundled proof. -/
partial def proveSupportUsingTerm (ctx : TransportContext) (goal term : Expr) : MetaM Expr := do
  let properties ← subtypePropertiesIn term
  trace[irw.support] "support facts contained in {term}: {properties.toList}"
  for property in properties do
    let propertyType ← inferType property
    let implication := Expr.forallE `_irw_subtype_property propertyType goal .default
    if let some implicationProof ← proveSupportWithGrind? implication then
      return mkApp implicationProof property
  proveSupport ctx goal

/-- Try to transport an equality on an ambient carrier through a supported domain.  A candidate is
usable only when support for both operands follows from the local context. -/
def transportSupportedEquality? (ctx : TransportContext) (source α x y : Expr) :
    MetaM (Option PropResult) := do
  let candidates ← registeredDomainCandidates ctx α
  let mut success : Option (Name × PropResult) := none
  for (declName, candidate) in candidates do
    let .supported sr := candidate | continue
    trace[irw.support] "trying supported equality domain {declName}\n  left: \
      {(mkApp sr.sourceSupport x).headBeta}\n  right: {(mkApp sr.sourceSupport y).headBeta}"
    let trial ← commitWhenSomeNoEx? do
      let sourceSupport ← whnf sr.sourceSupport
      let targetSupport ← whnf sr.targetSupport
      let descriptor ← mkAppM ``IRw.SupportedDomain.mk
        #[sourceSupport, targetSupport, sr.equiv]
      let hx ← proveSupportUsingTerm ctx ((mkApp sourceSupport x).headBeta) x
      let hy ← proveSupportUsingTerm ctx ((mkApp sourceSupport y).headBeta) y
      let proof ← mkAppM ``IRw.eq_congr_supported #[descriptor, x, y, hx, hy]
      let ty ← inferType proof
      let some (_, target) ← iffSides? ty
        | throwError "irw internal error in supported equality"
      let result ← simplifyTarget ctx source
        (← checkedPropResult source { target, proof })
      return some result
    if let some result := trial then
      if let some (previousName, previous) := success then
        unless ← withNewMCtxDepth <| isDefEq previous.target result.target do
          throwError "irw found ambiguous supported equality domains for\n  {α}\n\
            candidates: `{previousName}` and `{declName}`"
      else
        success := some (declName, result)
  return success.map (fun (_, result) ↦ result)

def universalSupportCertificate (ctx : TransportContext) (n : Name) (bi : BinderInfo)
    (domain body sourceSupport : Expr) : MetaM Expr :=
  withLocalDecl n bi domain fun x => do
    let support := (mkApp sourceSupport x).headBeta
    let notSupport ← mkAppM ``Not #[support]
    withLocalDecl `h_not_supported .default notSupport fun hnot => do
      let proposition := body.instantiate1 x
      let proof ← proveSupport ctx proposition
      mkLambdaFVars #[x, hnot] proof

def existentialSupportCertificate (ctx : TransportContext) (n : Name) (bi : BinderInfo)
    (domain pred sourceSupport : Expr) : MetaM Expr :=
  withLocalDecl n bi domain fun x => do
    let proposition := pred.beta #[x]
    withLocalDecl `h_witness .default proposition fun hWitness => do
      let support := (mkApp sourceSupport x).headBeta
      let proof ← proveSupport ctx support
      mkLambdaFVars #[x, hWitness] proof

def mkSubtypeType (pred : Expr) : MetaM Expr := do
  let predTy ← inferType pred
  unless predTy.isForall do
    throwError "irw internal error: subtype predicate is not a function"
  mkAppM ``Subtype #[pred]

/-- Prefer the canonical equivalence supplied by a supported domain when a syntactic guard is
definitionally that domain's support predicate.  This keeps bounded and inferred-supported
quantifiers on one coherence path. -/
def guardedEquivForSubtype? (ctx : TransportContext) (domain sourceSubtype : Expr) :
    MetaM (Option EquivResult) := do
  let some registered ← tryRegisteredEquiv ctx sourceSubtype | return none
  if let .supported sr ← findDomain ctx domain then
    let canonicalSource ← mkSubtypeType sr.sourceSupport
    if ← withNewMCtxDepth <| isDefEq sourceSubtype canonicalSource then
      let canonicalTarget ← mkSubtypeType sr.targetSupport
      return some (← checkedEquivResult sourceSubtype
        { target := canonicalTarget, equiv := sr.equiv })
  return some registered

/-! ### Reordering batched guarded universal quantifiers

Lean elaborates
```
∀ I J K, gI → gJ → gK → P
```
as one `forallE` telescope.  The bounded-quantifier transporter, intentionally, only consumes the
local shape `∀ I, gI → ...`.  Rather than teach bounded transport a second semantics for batched
guards, we normalize a leading universal telescope by moving any *registered* unary guard directly
after the binder it guards.  The normalization is accompanied by an explicit iff proof, the
ordinary recursive transporter is run on the normalized proposition, and the transported telescope
is then permuted back to the source ordering.

This layer is deliberately only a telescope permutation.  It neither invents a transport nor
interprets arbitrary propositions as bounds: a guard is movable only if bundling it with its binder
produces a subtype accepted by `@[irw_equiv]`. -/

structure GuardMove where
  binderIdx : Nat
  guardIdx : Nat
  deriving Inhabited

def isMovedGuard (moves : Array GuardMove) (idx : Nat) : Bool := Id.run do
  for m in moves do
    if m.guardIdx == idx then return true
  return false

def guardForBinder? (moves : Array GuardMove) (idx : Nat) : Option Nat := Id.run do
  for m in moves do
    if m.binderIdx == idx then return some m.guardIdx
  return none

/-- A candidate guard may be moved directly after binder `i` only when its type does not mention a
later telescope variable.  This is slightly conservative (a later variable may itself eventually be
moved earlier), but it makes the permutation criterion local and prevents us from manufacturing an
ill-scoped dependent telescope. -/
def dependsOnLaterTelescopeFVar (guardTy : Expr) (fvars : Array Expr) (i : Nat) : Bool := Id.run do
  for k in [:fvars.size] do
    if i < k && occursFVar fvars[k]!.fvarId! guardTy then return true
  return false

/-- Find a later proposition binder which is a registered guard for `fvars[i]`. -/
def findGuardForBinder (ctx : TransportContext) (fvars : Array Expr)
    (moves : Array GuardMove) (i : Nat) :
    MetaM (Option Nat) := do
  let x := fvars[i]!
  let xDecl ← x.fvarId!.getDecl
  if ← isProp xDecl.type then return none
  for j in [:fvars.size] do
    if i < j && !isMovedGuard moves j then
      let g := fvars[j]!
      let gDecl ← g.fvarId!.getDecl
      if (← isProp gDecl.type) && occursFVar x.fvarId! gDecl.type &&
          !dependsOnLaterTelescopeFVar gDecl.type fvars i then
        let guardPred ← mkLambdaFVars #[x] gDecl.type
        let sourceSubtype ← mkSubtypeType guardPred
        if (← guardedEquivForSubtype? ctx xDecl.type sourceSubtype).isSome then
          return some j
  return none

/-- Discover all independent registered guards in a universal telescope.  A proof binder is used at
most once. -/
def findGuardMoves (ctx : TransportContext) (fvars : Array Expr) : MetaM (Array GuardMove) := do
  let mut moves : Array GuardMove := #[]
  for i in [:fvars.size] do
    if let some j ← findGuardForBinder ctx fvars moves i then
      moves := moves.push { binderIdx := i, guardIdx := j }
  return moves

/-- Remove moved guards from their original positions and insert each immediately after its guarded
binder.  All other binders keep their relative order. -/
def guardNormalizationOrder (size : Nat) (moves : Array GuardMove) : Array Nat := Id.run do
  let mut order : Array Nat := #[]
  for i in [:size] do
    if !isMovedGuard moves i then
      order := order.push i
      if let some j := guardForBinder? moves i then
        order := order.push j
  return order

def isIdentityOrder (order : Array Nat) : Bool := Id.run do
  for i in [:order.size] do
    if order[i]! != i then return false
  return true

/-- Invert an array representation of a permutation. -/
def invertOrder (order : Array Nat) : Array Nat := Id.run do
  let mut inv := Array.replicate order.size 0
  for i in [:order.size] do
    inv := inv.set! order[i]! i
  return inv

/-- Check that reordering the local declarations according to `order` respects all telescope
dependencies.  The result is checked again by the kernel when the permutation proof is built; this
pre-check exists to turn a scope problem into a useful trace instead of an opaque abstraction
failure. -/
def telescopeOrderValid (fvars : Array Expr) (order : Array Nat) : MetaM Bool := do
  if fvars.size != order.size then return false
  let pos := invertOrder order
  for i in [:fvars.size] do
    let decl ← fvars[i]!.fvarId!.getDecl
    for j in [:fvars.size] do
      if occursFVar fvars[j]!.fvarId! decl.type && pos[j]! >= pos[i]! then
        return false
  return true

/-- Permute the first `fvars.size` universal/implication binders of `source` according to `order`.
`fvars` and `tail` must come from opening that prefix of `source`.  Both directions are constructed
by pure lambda/application reshuffling and then kernel-checked. -/
def permuteForallTelescope (source : Expr) (fvars : Array Expr) (tail : Expr)
    (order : Array Nat) : MetaM PropResult := do
  unless ← telescopeOrderValid fvars order do
    throwError "irw internal error: attempted an ill-scoped forall telescope permutation"
  let reordered := order.map fun i => fvars[i]!
  let target ← mkForallFVars reordered tail
  let forward ← withLocalDecl `h .default source fun h => do
    let tailProof := mkAppN h fvars
    let targetProof ← mkLambdaFVars reordered tailProof
    mkLambdaFVars #[h] targetProof
  let backward ← withLocalDecl `h .default target fun h => do
    let tailProof := mkAppN h reordered
    let sourceProof ← mkLambdaFVars fvars tailProof
    mkLambdaFVars #[h] sourceProof
  let proof ← mkAppM ``Iff.intro #[forward, backward]
  checkedPropResult source { target, proof }

/-- Whether a transported result still exposes the candidate domain's support immediately after
its leading data binder.  When role candidates share a raw source carrier, eliminating this guard
is useful evidence that the body actually identifies the candidate's intended role. -/
def hasLeadingForallSupportGuard (r : PropResult) (sr : SupportedResult) : MetaM Bool := do
  let target ← whnf r.target
  let .forallE n domain body bi := target | return false
  unless ← withNewMCtxDepth <| isDefEq domain sr.target do return false
  withLocalDecl n bi domain fun y => do
    let body ← whnf (body.instantiate1 y)
    let .forallE _ guard _ _ := body | return false
    unless ← isProp guard do return false
    let expected := (mkApp sr.targetSupport y).headBeta
    withNewMCtxDepth <| isDefEq guard expected

/-- Existential analogue of `hasLeadingForallSupportGuard`. -/
def hasLeadingExistsSupportGuard (r : PropResult) (sr : SupportedResult) : MetaM Bool := do
  let target ← whnf r.target
  unless target.isAppOfArity ``Exists 2 do return false
  let args := target.getAppArgs
  unless ← withNewMCtxDepth <| isDefEq args[0]! sr.target do return false
  let pred := args[1]!
  let predType ← inferType pred
  let .forallE n domain _ bi := predType | return false
  withLocalDecl n bi domain fun y => do
    let body ← whnf (pred.beta #[y])
    unless body.isAppOfArity ``And 2 do return false
    let guard := body.getAppArgs[0]!
    let expected := (mkApp sr.targetSupport y).headBeta
    withNewMCtxDepth <| isDefEq guard expected

/-- Find the first conjunct after a nonempty leading existential telescope. The conjunct is
returned only when it is independent of every witness crossed on the way. -/
partial def guardAfterExists? (body : Expr) (crossed : Array FVarId := #[]) :
    MetaM (Option (Expr × Nat)) := do
  let body ← whnf body
  if body.isAppOfArity ``Exists 2 then
    let args := body.getAppArgs
    let predTy ← inferType args[1]!
    let .forallE n domain _ bi := predTy | return none
    return ← withLocalDecl n bi domain fun y =>
      guardAfterExists? (args[1]!.beta #[y]) (crossed.push y.fvarId!)
  unless body.isAppOfArity ``And 2 do return none
  if crossed.isEmpty then return none
  let guard := body.getAppArgs[0]!
  for id in crossed do
    if occursFVar id guard then return none
  return some (guard, crossed.size)

/-- Insert `guard` as the first conjunct after a leading existential telescope. -/
partial def insertGuardAfterExists (guard body : Expr) : MetaM Expr := do
  let bodyWhnf ← whnf body
  unless bodyWhnf.isAppOfArity ``Exists 2 do
    return ← mkAppM ``And #[guard, body]
  let args := bodyWhnf.getAppArgs
  let predTy ← inferType args[1]!
  let .forallE n domain _ bi := predTy
    | throwError "irw internal error: Exists predicate is not a function"
  withLocalDecl n bi domain fun y => do
    let inner ← insertGuardAfterExists guard (args[1]!.beta #[y])
    mkAppM ``Exists #[← mkLambdaFVars #[y] inner]

/-- Hoist a fixed first conjunct from the end of a leading existential telescope. Every step is an
explicit `exists_congr_equiv` followed by `exists_and_left_explicit`, so the returned equivalence is
kernel checked rather than justified by a syntactic rewrite. -/
partial def hoistGuardAcrossExists (guard body : Expr) : MetaM PropResult := do
  let bodyWhnf ← whnf body
  if bodyWhnf.isAppOfArity ``And 2 then
    let args := bodyWhnf.getAppArgs
    unless ← withNewMCtxDepth <| isDefEq args[0]! guard do
      throwError "irw internal error: batched existential guard changed while being hoisted"
    return ← checkedPropResult body { target := bodyWhnf, proof := ← mkIffRefl body }
  unless bodyWhnf.isAppOfArity ``Exists 2 do
    throwError "irw internal error: batched existential guard was not followed by a conjunction"
  let args := bodyWhnf.getAppArgs
  let domain := args[0]!
  let pred := args[1]!
  let predTy ← inferType pred
  let .forallE n _ _ bi := predTy
    | throwError "irw internal error: Exists predicate is not a function"
  let er ← mkReflEquiv domain
  let (targetPred, restPred, pointwise) ← withLocalDecl n bi domain fun y => do
    let rr ← hoistGuardAcrossExists guard (pred.beta #[y])
    let rrTarget ← whnf rr.target
    unless rrTarget.isAppOfArity ``And 2 do
      throwError "irw internal error: hoisted existential did not expose its guard"
    let rrArgs := rrTarget.getAppArgs
    let guardMatches ← withNewMCtxDepth <| isDefEq rrArgs[0]! guard
    unless guardMatches do
      throwError "irw internal error: hoisted existential exposed the wrong guard"
    return (← mkLambdaFVars #[y] rr.target, ← mkLambdaFVars #[y] rrArgs[1]!,
      ← mkLambdaFVars #[y] rr.proof)
  let congrProof ← mkAppOptM ``IRw.exists_congr_equiv
    #[none, none, er.equiv, pred, targetPred, pointwise]
  let hoistProof ← mkAppM ``IRw.exists_and_left_explicit #[guard, restPred]
  let proof ← mkAppM ``Iff.trans #[congrProof, hoistProof]
  let proofTy ← inferType proof
  let some (_, target) ← iffSides? proofTy
    | throwError "irw internal error: existential guard hoisting did not produce an iff"
  checkedPropResult body { target, proof }

mutual

/-- Transport a bounded universal `∀ x, guard x → body x` through an equivalence between the
corresponding guarded subtypes.  The generated target is again an ordinary guarded forall. -/
partial def transportBoundedForall (ctx : TransportContext) (source : Expr)
    (n : Name) (domain body : Expr)
    (bi : BinderInfo) : MetaM (Option PropResult) :=
  commitWhenSomeNoEx? do
    -- Split the source into a guard predicate `S` and a body `P : ∀ x, S x → Prop`.
    let some (guardPred, sourceP) ←
        withLocalDecl n bi domain fun x => do
          let bodyX ← whnf (body.instantiate1 x)
          let .forallE hn guard tail hbi := bodyX | return none
          unless ← isProp guard do return none
          let guardPred ← mkLambdaFVars #[x] guard
          let sourceP ← withLocalDecl hn hbi guard fun hx =>
            mkLambdaFVars #[x, hx] (tail.instantiate1 hx)
          return some (guardPred, sourceP)
      | return none
    let sourceSubtype ← mkSubtypeType guardPred
    -- Only a *registered* subtype equivalence justifies the bounded reading.  Falling back to
    -- `deriveEquiv` here would hand back `Equiv.refl` for every guard, and the bounded path
    -- would then win over the ordinary quantifier path while transporting strictly less.
    let some er ← guardedEquivForSubtype? ctx domain sourceSubtype | return none
    let some (targetDomain, targetPred) ← subtypeParts? er.target | return none
    let esymm ← mkAppM ``Equiv.symm #[er.equiv]
    withLocalDecl n bi targetDomain fun y => do
      let targetGuard := (mkApp targetPred y).headBeta
      withLocalDecl `hy .default targetGuard fun hy => do
        let ySub ← mkAppOptM ``Subtype.mk #[targetDomain, targetPred, y, hy]
        let xSub ← mkEquivApply esymm ySub
        let sourceVal ← mkAppM ``Subtype.val #[xSub]
        let sourceProperty ← mkAppM ``Subtype.property #[xSub]
        let sourcePropertyType ← inferType sourceProperty
        withLocalDecl `hx_source .default sourcePropertyType fun hxSource => do
          let rr ← transportProp ctx (sourceP.beta #[sourceVal, hxSource])
          if occursFVar hxSource.fvarId! rr.target then
            throwError "irw cannot re-express a bounded universal whose transported body depends \
              on the source support proof:\n  {rr.target}"
          let rrProofFn ← mkLambdaFVars #[hxSource] rr.proof
          let rrProof := mkApp rrProofFn sourceProperty
          let h ← mkLambdaFVars #[y, hy] rrProof
          let targetP ← mkLambdaFVars #[y, hy] rr.target
          let target ← mkForallFVars #[y, hy] rr.target
          let proof ← mkAppOptM ``IRw.forall_guard_congr_equiv
            #[none, none, none, none, er.equiv, sourceP, targetP, h]
          let result ← checkedPropResult source { target, proof }
          return some (← simplifyTarget ctx source result)

/-- Transport a bounded existential `∃ x, guard x ∧ body x` through an equivalence between the
corresponding guarded subtypes. -/
partial def transportBoundedExists (ctx : TransportContext) (source domain pred : Expr) :
    MetaM (Option PropResult) :=
  commitWhenSomeNoEx? do
    let predTy ← inferType pred
    let .forallE n _ _ bi := predTy | return none
    let some (guardPred, sourceP) ←
        withLocalDecl n bi domain fun x => do
          let bodyX ← whnf (pred.beta #[x])
          unless bodyX.isAppOfArity ``And 2 do return none
          let args := bodyX.getAppArgs
          let guardPred ← mkLambdaFVars #[x] args[0]!
          let sourceP ← mkLambdaFVars #[x] args[1]!
          return some (guardPred, sourceP)
      | return none
    let sourceSubtype ← mkSubtypeType guardPred
    -- Only a *registered* subtype equivalence justifies the bounded reading.  Falling back to
    -- `deriveEquiv` here would hand back `Equiv.refl` for every guard, and the bounded path
    -- would then win over the ordinary quantifier path while transporting strictly less.
    let some er ← guardedEquivForSubtype? ctx domain sourceSubtype | return none
    let some (targetDomain, targetPred) ← subtypeParts? er.target | return none
    let esymm ← mkAppM ``Equiv.symm #[er.equiv]
    withLocalDecl n bi targetDomain fun y => do
      let targetGuard := (mkApp targetPred y).headBeta
      withLocalDecl `hy .default targetGuard fun hy => do
        let ySub ← mkAppOptM ``Subtype.mk #[targetDomain, targetPred, y, hy]
        let xSub ← mkEquivApply esymm ySub
        let sourceVal ← mkAppM ``Subtype.val #[xSub]
        let rr ← transportProp ctx (sourceP.beta #[sourceVal])
        -- Ordinary bounded-existential syntax has a proof-independent body.  Bail out if a rule
        -- created a dependency on the bound proof.  Note this `throwError` is swallowed by the
        -- enclosing `commitWhenSomeNoEx?`: the effect is that the caller falls back to the
        -- ordinary (unbounded) existential path, not that the user sees this message.
        if occursFVar hy.fvarId! rr.target then
          throwError "irw cannot presently re-express a bounded existential whose transported \
            body depends on the bound proof:\n  {rr.target}"
        let h ← mkLambdaFVars #[y, hy] rr.proof
        let targetP ← mkLambdaFVars #[y] rr.target
        let target ← mkAppM ``Exists
          #[← mkLambdaFVars #[y] (← mkAppM ``And #[targetGuard, rr.target])]
        let proof ← mkAppOptM ``IRw.exists_guard_congr_equiv
          #[none, none, none, none, er.equiv, sourceP, targetP, h]
        let result ← checkedPropResult source { target, proof }
        return some (← simplifyTarget ctx source result)

/-- Transport an unguarded universal through a supported domain after proving that its body is
automatic outside the source support.  The first supported normal form deliberately exposes the
target guard. -/
partial def transportSupportedForall (ctx : TransportContext) (source : Expr)
    (n : Name) (domain body : Expr) (bi : BinderInfo) (sr : SupportedResult) :
    MetaM PropResult := do
  let certificate ← universalSupportCertificate ctx n bi domain body sr.sourceSupport
  let restrictProof ← mkAppM ``IRw.forall_iff_forall_guard #[certificate]
  let sourceP ← withLocalDecl n bi domain fun x =>
    withLocalDecl `hx .default ((mkApp sr.sourceSupport x).headBeta) fun hx =>
      mkLambdaFVars #[x, hx] (body.instantiate1 x)
  let esymm ← mkAppM ``Equiv.symm #[sr.equiv]
  let guardedResult ← withLocalDecl n bi sr.target fun y => do
    let targetGuard := (mkApp sr.targetSupport y).headBeta
    withLocalDecl `hy .default targetGuard fun hy => do
      let ySub ← mkAppOptM ``Subtype.mk #[sr.target, sr.targetSupport, y, hy]
      let xSub ← mkEquivApply esymm ySub
      let sourceVal ← mkAppM ``Subtype.val #[xSub]
      let rr ← transportProp ctx (body.instantiate1 sourceVal)
      let h ← mkLambdaFVars #[y, hy] rr.proof
      let targetP ← mkLambdaFVars #[y, hy] rr.target
      let target ← mkForallFVars #[y, hy] rr.target
      let guardedProof ← mkAppOptM ``IRw.forall_guard_congr_equiv
        #[none, none, none, none, sr.equiv, sourceP, targetP, h]
      let proof ← mkAppM ``Iff.trans #[restrictProof, guardedProof]
      simplifyTarget ctx source (← checkedPropResult source { target, proof })
  -- If the source body itself forces support (for example `B ⊆ A` under `A ⊆ E`), the
  -- newly exposed target support guard is redundant.  Remove it only with another checked local
  -- certificate; otherwise retain the explicit supported normal form.
  let .forallE targetName targetDomain targetBody targetBi := guardedResult.target
    | return guardedResult
  let guardedBody ← whnf targetBody
  let .forallE _ targetGuard targetTail _ := guardedBody | return guardedResult
  unless (← isProp targetGuard) && isNondependentForall targetTail do return guardedResult
  let unguardedBody := targetTail.instantiate1 (mkConst ``True.intro)
  let expectedGuard := (mkApp sr.targetSupport (.bvar 0)).headBeta
  let guardMatches ← withLocalDecl targetName targetBi targetDomain fun y =>
    withNewMCtxDepth <| isDefEq (targetGuard.instantiate1 y) (expectedGuard.instantiate1 y)
  unless guardMatches do return guardedResult
  -- Preserve the explicit supported normal form for bodies that are trivially true or whose
  -- first premise is the support predicate itself.  The guard is removed only for an independent
  -- later premise that entails support, such as `B ⊆ A`, or for a later data binder whose body
  -- supplies the certificate, such as the second endpoint of `Adj`.
  let candidateBody ← whnf unguardedBody
  let .forallE _ candidateDomain candidateTail _ := candidateBody
    | return guardedResult
  if ← isProp candidateDomain then
    unless isNondependentForall candidateTail do return guardedResult
    let premiseIsSupport ← withLocalDecl targetName targetBi targetDomain fun y =>
      withNewMCtxDepth <| isDefEq (candidateDomain.instantiate1 y)
        (expectedGuard.instantiate1 y)
    if premiseIsSupport then return guardedResult
  let some targetCertificate ← commitWhenSomeNoEx? do
      let proof ← universalSupportCertificate ctx targetName targetBi targetDomain unguardedBody
        sr.targetSupport
      return some proof
    | return guardedResult
  let exposeProof ← mkAppM ``IRw.forall_iff_forall_guard #[targetCertificate]
  let hideProof ← mkAppM ``Iff.symm #[exposeProof]
  let proof ← mkAppM ``Iff.trans #[guardedResult.proof, hideProof]
  let target := Expr.forallE targetName targetDomain unguardedBody targetBi
  simplifyTarget ctx source (← checkedPropResult source { target, proof })

/-- Transport an unguarded existential through a supported domain after proving that every source
witness is supported.  The first supported normal form deliberately exposes the target guard. -/
partial def transportSupportedExists (ctx : TransportContext) (source domain pred : Expr)
    (sr : SupportedResult) : MetaM PropResult := do
  let predTy ← inferType pred
  let .forallE n _ _ bi := predTy
    | throwError "irw internal error: Exists predicate is not a function"
  let certificate ← existentialSupportCertificate ctx n bi domain pred sr.sourceSupport
  let restrictProof ← mkAppM ``IRw.exists_iff_exists_guard #[certificate]
  let esymm ← mkAppM ``Equiv.symm #[sr.equiv]
  withLocalDecl n bi sr.target fun y => do
    let targetGuard := (mkApp sr.targetSupport y).headBeta
    withLocalDecl `hy .default targetGuard fun hy => do
      let ySub ← mkAppOptM ``Subtype.mk #[sr.target, sr.targetSupport, y, hy]
      let xSub ← mkEquivApply esymm ySub
      let sourceVal ← mkAppM ``Subtype.val #[xSub]
      let rr ← transportProp ctx (pred.beta #[sourceVal])
      if occursFVar hy.fvarId! rr.target then
        throwError "irw cannot re-express a supported existential whose transported body depends \
          on the target support proof:\n  {rr.target}"
      let h ← mkLambdaFVars #[y, hy] rr.proof
      let targetP ← mkLambdaFVars #[y] rr.target
      let target ← mkAppM ``Exists
        #[← mkLambdaFVars #[y] (← mkAppM ``And #[targetGuard, rr.target])]
      let guardedProof ← mkAppOptM ``IRw.exists_guard_congr_equiv
        #[none, none, none, none, sr.equiv, pred, targetP, h]
      let proof ← mkAppM ``Iff.trans #[restrictProof, guardedProof]
      simplifyTarget ctx source (← checkedPropResult source { target, proof })

/-- When several exact supported domains share the same raw carrier, use the quantified body as
delayed role evidence.  A candidate is committed only if both its support certificate and recursive
proposition transport succeed. -/
partial def transportAmbiguousSupportedForall? (ctx : TransportContext) (source : Expr)
    (n : Name) (domain body : Expr) (bi : BinderInfo) : MetaM (Option PropResult) := do
  let candidates ← registeredDomainCandidates ctx domain
  if candidates.size < 2 then return none
  let mut firstSuccess : Option Nat := none
  let mut guardFreeSuccess : Option Nat := none
  let mut successCount := 0
  let mut guardFreeCount := 0
  for idx in [:candidates.size] do
    let (_, candidate) := candidates[idx]!
    if let .supported sr := candidate then
      let saved ← saveState
      let trial ← try
          some <$> transportSupportedForall ctx source n domain body bi sr
        catch _ => pure none
      restoreState saved
      if let some result := trial then
        successCount := successCount + 1
        if firstSuccess.isNone then firstSuccess := some idx
        if !(← hasLeadingForallSupportGuard result sr) then
          guardFreeCount := guardFreeCount + 1
          if guardFreeSuccess.isNone then guardFreeSuccess := some idx
  let selected := if guardFreeCount == 1 then guardFreeSuccess
    else if guardFreeCount == 0 && successCount == 1 then firstSuccess
    else none
  if let some idx := selected then
    let (_, candidate) := candidates[idx]!
    if let .supported sr := candidate then
      let result ← transportSupportedForall ctx source n domain body bi sr
      trace[irw.domain] "resolved ambiguous domain for {domain} from its forall body"
      return some result
  let names := candidates.map (fun candidate => candidate.1)
  throwError "irw found several exact supported domains for\n  {domain}\n\
    but the quantified body did not determine a unique role\ncandidates: {names.toList}"

/-- Existential counterpart of `transportAmbiguousSupportedForall?`. -/
partial def transportAmbiguousSupportedExists? (ctx : TransportContext)
    (source domain pred : Expr) : MetaM (Option PropResult) := do
  let candidates ← registeredDomainCandidates ctx domain
  if candidates.size < 2 then return none
  let mut firstSuccess : Option Nat := none
  let mut guardFreeSuccess : Option Nat := none
  let mut successCount := 0
  let mut guardFreeCount := 0
  for idx in [:candidates.size] do
    let (_, candidate) := candidates[idx]!
    if let .supported sr := candidate then
      let saved ← saveState
      let trial ← try
          some <$> transportSupportedExists ctx source domain pred sr
        catch _ => pure none
      restoreState saved
      if let some result := trial then
        successCount := successCount + 1
        if firstSuccess.isNone then firstSuccess := some idx
        if !(← hasLeadingExistsSupportGuard result sr) then
          guardFreeCount := guardFreeCount + 1
          if guardFreeSuccess.isNone then guardFreeSuccess := some idx
  let selected := if guardFreeCount == 1 then guardFreeSuccess
    else if guardFreeCount == 0 && successCount == 1 then firstSuccess
    else none
  if let some idx := selected then
    let (_, candidate) := candidates[idx]!
    if let .supported sr := candidate then
      let result ← transportSupportedExists ctx source domain pred sr
      trace[irw.domain] "resolved ambiguous domain for {domain} from its existential body"
      return some result
  let names := candidates.map (fun candidate => candidate.1)
  throwError "irw found several exact supported domains for\n  {domain}\n\
    but the quantified body did not determine a unique role\ncandidates: {names.toList}"

/-- Normalize non-adjacent registered guards in a leading universal telescope, recurse through the
already-existing bounded-forall path, and restore the transported telescope to the original binder
ordering.  This handles batched syntax such as
```
∀ I J K, I ⊆ E → J ⊆ E → K ⊆ E → P I J K
```
without duplicating bounded-quantifier transport logic. -/
partial def transportBatchedForall (ctx : TransportContext) (source : Expr) :
    MetaM (Option PropResult) := do
  let sourceWhnf ← whnf source
  unless sourceWhnf.isForall do return none
  forallTelescope sourceWhnf fun fvars tail => do
    if fvars.size < 2 then return none
    let moves ← findGuardMoves ctx fvars
    if moves.isEmpty then return none
    let order := guardNormalizationOrder fvars.size moves
    -- If every recognised guard was already adjacent, the ordinary bounded-forall branch is the
    -- canonical path and there is nothing to normalize here.
    if isIdentityOrder order then return none
    unless ← telescopeOrderValid fvars order do
      trace[irw] "declining batched-guard normalization: moving a guard would break telescope \
        dependencies"
      return none
    trace[irw] "normalizing batched forall telescope with order {order.toList}"
    let normalized ← permuteForallTelescope source fvars tail order
    -- From this point onward a nonidentity registered guard permutation has been selected.  Do not
    -- swallow failures: any error in recursive transport/restoration is a real engine error and is
    -- substantially more useful than falling through to the unbounded `Equiv.refl` path.
    let transported ← transportProp ctx normalized.target
    let n := fvars.size
    forallBoundedTelescope transported.target (some n) fun targetFVars targetTail => do
      if targetFVars.size != n then
        throwError "irw internal error: batched-guard transport changed the leading telescope \
          size\nexpected {n} binders, found {targetFVars.size}\ntarget:\n  {transported.target}"
      let restoreOrder := invertOrder order
      let restored ← permuteForallTelescope transported.target targetFVars targetTail restoreOrder
      let p₁ ← mkAppM ``Iff.trans #[normalized.proof, transported.proof]
      let proof ← mkAppM ``Iff.trans #[p₁, restored.proof]
      let result ← checkedPropResult source { target := restored.target, proof }
      return some (← simplifyTarget ctx source result)

/-- Hoist the first guard in a batched existential across all later witnesses, transport the
resulting adjacent guarded existential, and restore the batched target shape. Recursion handles the
remaining guards after the first supported witness is entered. -/
partial def transportBatchedExists (ctx : TransportContext) (source : Expr) :
    MetaM (Option PropResult) := commitWhenSomeNoEx? do
  let s ← whnf source
  unless s.isAppOfArity ``Exists 2 do return none
  let outerArgs := s.getAppArgs
  let outerDomain := outerArgs[0]!
  let outerPred := outerArgs[1]!
  let outerPredTy ← inferType outerPred
  let .forallE outerName _ _ outerBi := outerPredTy | return none
  let some (guardPred, normalizedPred, pointwise) ←
      withLocalDecl outerName outerBi outerDomain fun x => do
        let outerBody ← whnf (outerPred.beta #[x])
        let some (guard, _) ← guardAfterExists? outerBody | return none
        let hoisted ← hoistGuardAcrossExists guard outerBody
        return some (← mkLambdaFVars #[x] guard, ← mkLambdaFVars #[x] hoisted.target,
          ← mkLambdaFVars #[x] hoisted.proof)
    | return none
  -- Reassociate only a registered support guard. Arbitrary conjunctions remain in the user's
  -- original shape and cannot accidentally acquire bounded-quantifier semantics.
  let sourceSubtype ← mkSubtypeType guardPred
  if (← guardedEquivForSubtype? ctx outerDomain sourceSubtype).isNone then return none
  let er ← mkReflEquiv outerDomain
  let normalizeProof ← mkAppOptM ``IRw.exists_congr_equiv
    #[none, none, er.equiv, outerPred, normalizedPred, pointwise]
  let normalizeType ← inferType normalizeProof
  let some (_, normalizedTarget) ← iffSides? normalizeType | return none
  let normalized ← checkedPropResult source { target := normalizedTarget, proof := normalizeProof }
  trace[irw] "normalizing one batched existential guard"
  let transported ← transportProp ctx normalized.target

  -- Read the transported adjacent form, insert its guard after the entire remaining witness
  -- telescope, and use the same checked hoisting construction in reverse.
  let transportedTarget ← whnf transported.target
  unless transportedTarget.isAppOfArity ``Exists 2 do
    throwError "irw internal error: batched existential transport lost its outer witness:\n  \
      {transported.target}"
  let targetOuterArgs := transportedTarget.getAppArgs
  let targetOuterDomain := targetOuterArgs[0]!
  let targetOuterPred := targetOuterArgs[1]!
  let targetOuterPredTy ← inferType targetOuterPred
  let .forallE targetOuterName _ _ targetOuterBi := targetOuterPredTy
    | throwError "irw internal error: transported Exists predicate is not a function"
  let (restoredPred, restorePointwise) ←
    withLocalDecl targetOuterName targetOuterBi targetOuterDomain fun x => do
      let targetOuterBody ← whnf (targetOuterPred.beta #[x])
      unless targetOuterBody.isAppOfArity ``And 2 do
        throwError "irw internal error: transported batched existential lost its adjacent \
          guard:\n  {transported.target}"
      let targetAndArgs := targetOuterBody.getAppArgs
      let batchedBody ← insertGuardAfterExists targetAndArgs[0]! targetAndArgs[1]!
      let hoisted ← hoistGuardAcrossExists targetAndArgs[0]! batchedBody
      unless ← withNewMCtxDepth <| isDefEq hoisted.target targetOuterBody do
        throwError "irw internal error: existential guard restoration changed the adjacent form"
      return (← mkLambdaFVars #[x] batchedBody,
        ← mkLambdaFVars #[x] (← mkAppM ``Iff.symm #[hoisted.proof]))
  let targetEr ← mkReflEquiv targetOuterDomain
  let restoreProof ← mkAppOptM ``IRw.exists_congr_equiv
    #[none, none, targetEr.equiv, targetOuterPred, restoredPred, restorePointwise]
  let restoreType ← inferType restoreProof
  let some (_, restoredTarget) ← iffSides? restoreType
    | throwError "irw internal error: existential reassociation did not produce an iff"
  let p₁ ← mkAppM ``Iff.trans #[normalized.proof, transported.proof]
  let proof ← mkAppM ``Iff.trans #[p₁, restoreProof]
  let result ← checkedPropResult source { target := restoredTarget, proof }
  return some (← simplifyTarget ctx source result)

/-- Recursive proposition transporter.  Every successful branch constructs a kernel-checkable iff
proof. An unmatched atomic leaf is left fixed only after checking that it is independent of the
source object and all transported local data. -/
partial def transportProp (ctx : TransportContext) (source : Expr) : MetaM PropResult := do
  let source ← instantiateMVars source
  unless ← isProp source do
    throwError "irw expected a proposition, got\n  {source}"
  trace[irw] "transporting proposition {source}"

  let s ← whnf source

  if s.isConstOf ``True || s.isConstOf ``False then
    return ← checkedPropResult source { target := source, proof := ← mkIffRefl source }

  -- Proposition-valued naturality gets first chance. This is important for predicates such as
  -- `IsBasis` whose internal definition is complicated but whose transport theorem is primitive
  -- API.
  if let some r ← tryRegisteredNaturalityProp ctx source then
    return ← simplifyTarget ctx source r

  -- Set subset is kept as an atomic relation rather than unfolded to a forall.  This lets the
  -- element equivalence transport both sets coherently.  It has to be recognised on the
  -- unreduced `source`: `whnf` turns `S ⊆ T` into a `∀`, which the binder code below would then
  -- take apart element by element.  Mathlib's `⊆` notation elaborates to `LE.le` on types tagged
  -- `@[use_set_notation_for_order]` (`Set` is one of them) and to `HasSubset.Subset` otherwise.
  if source.isAppOfArity ``LE.le 4 || source.isAppOfArity ``HasSubset.Subset 4 then
    let args := source.getAppArgs
    if args[0]!.isAppOfArity ``Set 1 then
      let α := args[0]!.getAppArgs[0]!
      let S := args[2]!
      let T := args[3]!
      let er ← deriveEquiv ctx α
      let proof ← mkAppM ``IRw.subset_congr_equiv #[er.equiv, S, T]
      let ty ← inferType proof
      let some (_, target) ← iffSides? ty | throwError "irw internal error in subset"
      return ← simplifyTarget ctx source (← checkedPropResult source { target, proof })

  -- Membership in a `Set`, likewise recognised before `whnf` collapses it to an application.
  if source.isAppOfArity ``Membership.mem 5 then
    let args := source.getAppArgs
    let S := args[3]!
    let x := args[4]!
    let setTy ← instantiateMVars (← inferType S)
    if setTy.isAppOfArity ``Set 1 then
      let α := setTy.getAppArgs[0]!
      let er ← deriveEquiv ctx α
      let proof ← mkAppM ``IRw.mem_congr_equiv #[er.equiv, x, S]
      let ty ← inferType proof
      let some (_, target) ← iffSides? ty | throwError "irw internal error in membership"
      return ← simplifyTarget ctx source (← checkedPropResult source { target, proof })

  -- Negation before generic implication, on the unreduced `source`: `whnf` unfolds `¬ p` to
  -- `p → False`, which would send it down the implication branch and lose the `¬`.
  if source.isAppOfArity ``Not 1 then
    let p := source.getAppArgs[0]!
    return ← mkNotCongr ctx source (← transportProp ctx p)

  if s.isAppOfArity ``And 2 then
    let a := s.getAppArgs[0]!
    let b := s.getAppArgs[1]!
    return ← mkBinaryCongr ctx source ``and_congr (← transportProp ctx a) (← transportProp ctx b)

  if s.isAppOfArity ``Or 2 then
    let a := s.getAppArgs[0]!
    let b := s.getAppArgs[1]!
    return ← mkBinaryCongr ctx source ``or_congr (← transportProp ctx a) (← transportProp ctx b)

  if s.isAppOfArity ``Iff 2 then
    let a := s.getAppArgs[0]!
    let b := s.getAppArgs[1]!
    return ← mkBinaryCongr ctx source ``iff_congr (← transportProp ctx a) (← transportProp ctx b)

  -- Existential.
  if s.isAppOfArity ``Exists 2 then
    let args := s.getAppArgs
    let domain := args[0]!
    let pred := args[1]!
    -- Prefer a bounded interpretation when one is syntactically visible.
    if let some r ← transportBoundedExists ctx source domain pred then return r
    if let some r ← transportBatchedExists ctx source then return r
    if let some r ← transportAmbiguousSupportedExists? ctx source domain pred then return r
    let domainResult ← findDomain ctx domain
    if let .supported sr := domainResult then
      return ← transportSupportedExists ctx source domain pred sr
    let .total er := domainResult
      | throwError "irw internal error: impossible domain result"
    let predTy ← inferType pred
    let .forallE n _ _ bi := predTy
      | throwError "irw internal error: Exists predicate is not a function"
    let esymm ← mkAppM ``Equiv.symm #[er.equiv]
    return ← withLocalDecl n bi er.target fun y => do
      let x ← mkEquivApply esymm y
      let innerCtx ← ctx.pushTotal x y domain er.target er.equiv
      let rr ← transportProp innerCtx (pred.beta #[x])
      let h ← mkLambdaFVars #[y] rr.proof
      let targetP ← mkLambdaFVars #[y] rr.target
      let target ← mkAppM ``Exists #[targetP]
      let proof ← mkAppOptM ``IRw.exists_congr_equiv
        #[none, none, er.equiv, pred, targetP, h]
      simplifyTarget ctx source (← checkedPropResult source { target, proof })

  -- Forall or implication.
  match s with
  | .forallE n domain body bi =>
      if (← isProp domain) && isNondependentForall body then
        let consequent := body.instantiate1 (mkConst ``True.intro)
        let ra ← transportProp ctx domain
        return ← withLocalDecl n bi domain fun hDomain => do
          let rb ← transportProp ctx consequent
          if occursFVar hDomain.fvarId! rb.target then
            throwError "irw internal error: transported implication target depends on the source \
              antecedent proof:\n  {rb.target}"
          let consequentProof ← mkLambdaFVars #[hDomain] rb.proof
          let proof ← mkAppM ``IRw.imp_congr_of_left #[ra.proof, consequentProof]
          let proofType ← inferType proof
          let some (_, target) ← iffSides? proofType
            | throwError "irw internal error: dependent implication congruence did not produce iff"
          simplifyTarget ctx source (← checkedPropResult source { target, proof })
      -- Prefer bounded interpretation of a guarded forall.
      if let some r ← transportBoundedForall ctx source n domain body bi then return r
      -- A later guard may belong to this binder (for example `∀ I J, gI → gJ → ...`).
      -- Normalize the entire leading telescope once, recurse through the ordinary bounded path,
      -- then restore the original batched ordering.
      if let some r ← transportBatchedForall ctx source then return r
      if let some r ← transportAmbiguousSupportedForall? ctx source n domain body bi then return r
      let domainResult ← findDomain ctx domain
      if let .supported sr := domainResult then
        return ← transportSupportedForall ctx source n domain body bi sr
      let .total er := domainResult
        | throwError "irw internal error: impossible domain result"
      let esymm ← mkAppM ``Equiv.symm #[er.equiv]
      let sourceP := Expr.lam n domain body bi
      return ← withLocalDecl n bi er.target fun y => do
        let x ← mkEquivApply esymm y
        let innerCtx ← ctx.pushTotal x y domain er.target er.equiv
        let rr ← transportProp innerCtx (body.instantiate1 x)
        let h ← mkLambdaFVars #[y] rr.proof
        let targetP ← mkLambdaFVars #[y] rr.target
        let target ← mkForallFVars #[y] rr.target
        let proof ← mkAppOptM ``IRw.forall_congr_equiv
          #[none, none, er.equiv, sourceP, targetP, h]
        simplifyTarget ctx source (← checkedPropResult source { target, proof })
  | _ => pure ()

  -- Generic equality leaf.
  if s.isAppOfArity ``Eq 3 then
    let args := s.getAppArgs
    let α := args[0]!
    let x := args[1]!
    let y := args[2]!
    if let some result ← transportSupportedEquality? ctx source α x y then
      return result
    let er ← deriveEquiv ctx α
    let proof ← mkAppM ``IRw.eq_congr_equiv #[er.equiv, x, y]
    let ty ← inferType proof
    let some (_, target) ← iffSides? ty | throwError "irw internal error in equality"
    return ← simplifyTarget ctx source (← checkedPropResult source { target, proof })

  -- Membership that only becomes visible after reduction: `x ∈ S` for `S : Set α` reduces to the
  -- application `S x`.
  if let .app S x := s then
    let setTy ← instantiateMVars (← inferType S)
    if setTy.isAppOfArity ``Set 1 then
      let α := setTy.getAppArgs[0]!
      let er ← deriveEquiv ctx α
      let proof ← mkAppM ``IRw.mem_congr_equiv #[er.equiv, x, S]
      let ty ← inferType proof
      let some (_, target) ← iffSides? ty | throwError "irw internal error in membership"
      return ← simplifyTarget ctx source (← checkedPropResult source { target, proof })

  -- Opaque object-independent atoms are constant families for this transformation. Inspecting
  -- free-variable types prevents `Q x` from being mistaken for fixed when `x` belongs to the
  -- source object even though that dependency is not written in the application itself.
  if ← isFixedAtom ctx source then
    trace[irw] "leaving object-independent atomic proposition fixed: {source}"
    return ← checkedPropResult source { target := source, proof := ← mkIffRefl source }

  let naturalityRules := (naturalityExt.getState (← getEnv)).filterMap fun registration =>
    if registration.system == ctx.system then
      some (registration.declName, registration.priority)
    else none
  throwError "irw could not transport the atomic proposition\n  {source}\n\
    The supplied isomorphism has type\n  {← inferType ctx.iso}\n\
    No proposition-valued @[irw_naturality] matched.\n\
    Naturality rules: {naturalityRules.toList}"

end

end Core

/-! ## Tactic frontend -/

def rewriteTargetWith (mvarId : MVarId) (iso : Expr) : MetaM MVarId := mvarId.withContext do
  let source ← instantiateMVars (← mvarId.getType)
  let ctx ← Core.mkTransportContext iso
  let r ← Core.transportProp ctx source
  let eqProof ← mkAppM ``propext #[r.proof]
  check eqProof
  mvarId.replaceTargetEq r.target eqProof

def rewriteLocalWith (mvarId : MVarId) (fvarId : FVarId) (iso : Expr) : MetaM MVarId :=
  mvarId.withContext do
    let decl ← fvarId.getDecl
    let source ← instantiateMVars decl.type
    let ctx ← Core.mkTransportContext iso
    let r ← Core.transportProp ctx source
    let eqProof ← mkAppM ``propext #[r.proof]
    check eqProof
    let rr ← mvarId.replaceLocalDecl fvarId r.target eqProof
    return rr.mvarId

syntax (name := irwTac) "irw " term (ppSpace Parser.Tactic.location)? : tactic

elab_rules : tactic
  | `(tactic| irw $isoStx:term $[$loc?]?) => withMainContext do
      let iso ← Term.elabTerm isoStx none
      Term.synthesizeSyntheticMVarsNoPostponing
      let iso ← instantiateMVars iso
      check iso
      let loc := expandOptLocation (Lean.mkOptionalNode (loc?.map (·.raw)))
      withLocation loc
        (atLocal := fun fvarId => do
          let g ← getMainGoal
          let g' ← rewriteLocalWith g fvarId iso
          replaceMainGoal [g'])
        (atTarget := do
          let g ← getMainGoal
          let g' ← rewriteTargetWith g iso
          replaceMainGoal [g'])
        (failed := fun _ => throwError "irw failed: no requested location could be transported")

/-- Debugging frontend: show the proposition that `irw i` would produce without changing the
goal. -/
syntax (name := irwQueryTac) "irw? " term : tactic

elab_rules : tactic
  | `(tactic| irw? $isoStx:term) => withMainContext do
      let iso ← Term.elabTerm isoStx none
      Term.synthesizeSyntheticMVarsNoPostponing
      let iso ← instantiateMVars iso
      let source ← instantiateMVars (← getMainTarget)
      let ctx ← Core.mkTransportContext iso
      let r ← Core.transportProp ctx source
      logInfo m!"irw target:{indentExpr r.target}\nproof:{indentExpr r.proof}"

end IRw
