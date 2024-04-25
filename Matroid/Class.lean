import Matroid.Representation.Basic

/-
We collect material on matroid invariants and closure properties of classes of matroids here.
-/

open Set

namespace Matroid

section Property

universe u

variable {η : Type*} {P : ∀ {β : Type u}, Matroid β → Prop} {α : Type u} {M N : Matroid α}

section Invariant

/-- A matroid invariant is a parameter or property that is invariant under isomorphism. -/
class Invariant {η : Type} (f : ∀ {α : Type u}, Matroid α → η) : Prop :=
  (on_iso : ∀ {α β : Type u} {M : Matroid α} {N : Matroid β}, M ≅ N → f M = f N)

theorem IsIso.pred_iff_pred {P : ∀ {η : Type u}, Matroid η → Prop} [Invariant P]
    {α β : Type u} {M : Matroid α} {N : Matroid β} (hMN : M ≅ N) : P M ↔ P N := by
  simpa using Invariant.on_iso (f := P) hMN

theorem IsIso.pred_of_pred [Invariant P] {α β : Type u} {M : Matroid α} {N : Matroid β}
  (hMN : M ≅ N) (hM : P M) : P N := hMN.pred_iff_pred.1 hM

-- theorem Invariant.and {P Q : ∀ {η : Type u}, Matroid η → Prop} (hP : Invariant P)
--     (hQ : Invariant Q) : Invariant (fun M ↦ P M ∧ Q M) := by
--   intro α β M N hMN
--   simp only [eq_iff_iff]
--   rw [hP.pred_iff_pred hMN, hQ.pred_iff_pred hMN]

instance invariant_finite : Invariant.{u} Matroid.Finite where
  on_iso := by intro _ _ _ _ hMN ; rw [hMN.finite_iff]

instance invariant_finiteRk : Invariant.{u} FiniteRk where
  on_iso := by intro _ _ _ _ hMN ; rw [hMN.finiteRk_iff]

instance invariant_erk : Invariant.{u} erk where
  on_iso := by intro _ _ _ _ hMN; exact hMN.erk_eq_erk

instance invariant_fieldRep {𝔽 : Type*} [Field 𝔽] : Invariant.{u} (FieldRep 𝔽) where
  on_iso := by
    intro _ _ _ _ hMN; rw [fieldRep_def, fieldRep_def, hMN.representable_iff, hMN.finite_iff]

end Invariant

section Restriction

class RestrictionClosed (P : ∀ {α : Type u}, Matroid α → Prop) : Prop :=
  (forall_restriction : ∀ {α : Type u} {N M : Matroid α}, N ≤r M → P M → P N)

theorem Restriction.pred_restriction [RestrictionClosed P] (hNM : N ≤r M) (hM : P M) : P N :=
  RestrictionClosed.forall_restriction hNM hM

end Restriction

section Minor

/-- A minor-closed matroid property -/
class MinorClosed (P : ∀ {α : Type u}, Matroid α → Prop) : Prop :=
  (forall_minor : ∀ {α : Type u} {N M : Matroid α}, N ≤m M → P M → P N)

theorem Minor.pred_minor [MinorClosed P] (hNM : N ≤m M) (hM : P M) : P N :=
  MinorClosed.forall_minor hNM hM

instance minorClosed_finite : MinorClosed.{u} Matroid.Finite where
  forall_minor := fun a _ ↦ Minor.finite a

instance minorClosed_finiteRk : MinorClosed.{u} FiniteRk where
  forall_minor := fun a _ ↦ Minor.finiteRk a

instance minorClosed_finitary : MinorClosed.{u} Finitary where
  forall_minor := fun a _ ↦ Minor.finitary a

instance minorClosed_fieldRep (𝔽 : Type*) [Field 𝔽] :
    MinorClosed (FieldRep 𝔽) :=
  ⟨fun {_ _ _} hNM ⟨hMrep, hMfin⟩ ↦ ⟨hMrep.minor hNM, hNM.pred_minor hMfin⟩⟩

/-- `M` is an `ExclMinor` for property `P` if `M` is minor-minimal not satisfying `P`. -/
@[pp_dot] def ExclMinor {β : Type u} (M : Matroid β) (P : ∀ {α : Type u}, Matroid α → Prop) :=
  ¬ P M ∧ ∀ {N}, N <m M → P N

theorem ExclMinor.not_prop_self (h : M.ExclMinor P) : ¬ P M :=
  h.1

theorem ExclMinor.prop_of_strictMinor (hM : M.ExclMinor P) (hMN : N <m M) : P N :=
  hM.2 hMN

theorem ExclMinor.eq_of_not_prop_of_minor (hM : M.ExclMinor P) (hNM : N ≤m M) (hN : ¬ P N) :
    N = M := by
  obtain (hNM' | rfl) := hNM.strictMinor_or_eq
  · exact (hN <| hM.prop_of_strictMinor hNM').elim
  rfl

theorem ExclMinor.prop_deleteElem (hM : M.ExclMinor P) (he : e ∈ M.E) : P (M ⧹ e) :=
  hM.prop_of_strictMinor (deleteElem_strictMinor he)

theorem ExclMinor.prop_contractElem (hM : M.ExclMinor P) (he : e ∈ M.E) : P (M ⧸ e) :=
  hM.prop_of_strictMinor (contractElem_strictMinor he)

theorem exclMinor_iff_forall_contract_delete [MinorClosed P] {M : Matroid α} :
    M.ExclMinor P ↔ ¬ P M ∧ ∀ e ∈ M.E, P (M ⧸ e) ∧ P (M ⧹ e) := by
  refine ⟨fun h ↦ ⟨h.not_prop_self, fun e he ↦ ⟨h.prop_contractElem he, h.prop_deleteElem he⟩⟩,
    fun h ↦ ⟨h.1, fun {N} hNM ↦ ?_⟩⟩
  obtain ⟨e, he, (hc | hd)⟩ := strictMinor_iff_minor_contract_or_delete.1 hNM
  · exact hc.pred_minor (h.2 e he).1
  exact hd.pred_minor (h.2 e he).2

theorem pred_iff_not_exists_exclMinor_minor [MinorClosed P] (M : Matroid α) [M.Finite] :
    P M ↔ ¬ ∃ N, N ≤m M ∧ N.ExclMinor P := by
  refine ⟨fun h ⟨N, hNM, hN⟩ ↦ hN.not_prop_self <| hNM.pred_minor h,
    fun h ↦ by_contra fun hM ↦ h ?_⟩
  obtain ⟨N, ⟨hNM : N ≤m M, hPN : ¬ P N ⟩, hmin⟩ := Finite.exists_minimal_wrt id _
    (M.finite_setOf_minor.inter_of_left {M' | ¬ P M'}) ⟨M, Minor.refl, hM⟩
  refine ⟨N, hNM, hPN, fun {N₀} hlt ↦ by_contra fun hN₀ ↦ ?_⟩
  obtain rfl := hmin N₀ ⟨hlt.minor.trans hNM, hN₀⟩ hlt.minor
  exact strictMinor_irrefl _ hlt

theorem exists_minimal_minor_between (P : Matroid α → Prop) [M.Finite] (hM : P M) (hNM : N ≤m M) :
    ∃ (M₀ : Matroid α), N ≤m M₀ ∧ M₀ ≤m M ∧ ∀ M₀', N ≤m M₀' → M₀' <m M₀ → ¬ P M₀' := by
  obtain ⟨M₀, ⟨hM₀M, -, hNM₀⟩, hmin⟩ :=  Finite.exists_minimal_wrt id _
    (M.finite_setOf_minor.inter_of_left {M' | P M' ∧ N ≤m M'}) ⟨M, Minor.refl, hM, hNM⟩
  exact ⟨M₀, hNM₀, hM₀M, fun M' hM' hM'M₀ hP ↦ hM'M₀.ne.symm <|
    hmin _ ⟨hM'M₀.minor.trans hM₀M, hP, hM'⟩ hM'M₀.minor⟩

end Minor

section Dual

/-- A self-dual matroid parameter -/
def SelfDual (P : ∀ {α : Type u}, Matroid α → η) : Prop :=
  ∀ {α : Type u} (M : Matroid α), P M = P M✶

/-- A matroid property that is preserved under taking duals. -/
class DualClosed (P : ∀ {α : Type u}, Matroid α → Prop) : Prop :=
  (forall_dual : ∀ {α : Type u} {M : Matroid α}, P M → P M✶)

theorem toDualPred [DualClosed P] (hM : P M) : P M✶ :=
  DualClosed.forall_dual hM

theorem ofDualPred [DualClosed P] (hM : P M✶) : P M :=
  M.dual_dual ▸ toDualPred hM

@[simp] theorem iffDualPred [DualClosed P] : P M✶ ↔ P M :=
  ⟨ofDualPred, toDualPred⟩

/-- The class of finite matroids is closed under duality -/
instance dualClosed_finite : DualClosed.{u} Matroid.Finite where
  forall_dual := fun a ↦ by infer_instance

/-- The class of finite `𝔽`-representable matroids is closed under duality -/
instance dualClosed_fieldRep (𝔽 : Type*) [Field 𝔽] : DualClosed.{u} (FieldRep 𝔽) where
  forall_dual := fun {_ _} ⟨hMrep, hMfin⟩ ↦ ⟨hMrep.dual, by infer_instance⟩

theorem ExclMinor.toDual [DualClosed P] (h : M.ExclMinor P) : M✶.ExclMinor P :=
  ⟨fun h' ↦ h.1 <| ofDualPred h',
    fun {_} hNM ↦ ofDualPred (h.prop_of_strictMinor <| strictMinor_dual_iff_dual_strictMinor.1 hNM)⟩

end Dual


section Finite

/-- The property of a matroid class that all its members are finite -/
class FinClass (P : ∀ {β : Type u}, Matroid β → Prop) : Prop where
  (forall_fin : ∀ {α : Type u} {M : Matroid α}, P M → M.Finite)

theorem finite_of_pred [FinClass P] (hM : P M) : M.Finite :=
    FinClass.forall_fin hM

instance fieldRep_finClass (𝔽 : Type*) [Field 𝔽] : FinClass.{u} (FieldRep 𝔽) where
  forall_fin := fun h ↦ h.2

instance finite_finClass : FinClass.{u} Matroid.Finite where
  forall_fin := id

theorem ExclMinor.finite [FinClass P] (hM : M.ExclMinor P) : M.Finite := by
  obtain (rfl | ⟨⟨e,he⟩⟩ ) := eq_emptyOn_or_nonempty M
  · infer_instance
  have := finite_of_pred <| hM.prop_deleteElem he
  exact ⟨((M ⧹ e).ground_finite.insert e).subset (by simp)⟩

section Finite


section Loops

/-- A matroid property `P` is `DeleteLoopClosed` if it is unchanged by deleting/adding a single
  loop. This is not the same as stating -/
class DeleteLoopClosed (P : ∀ {β : Type u}, Matroid β → Prop) : Prop :=
  (iff_deleteLoop : ∀ {α : Type u} {M : Matroid α} {e : α}, M.Loop e → (P (M ⧹ e) ↔ P M))

theorem pred_delete_loop_iff [DeleteLoopClosed P] {M : Matroid α} (he : M.Loop e) :
    P (M ⧹ e) ↔ P M :=
  DeleteLoopClosed.iff_deleteLoop he

theorem ExclMinor.loopless [DeleteLoopClosed P] [MinorClosed P] (hM : M.ExclMinor P) :
    M.Loopless := by
  rw [loopless_iff_forall_not_loop]
  intro e heE he
  rw [exclMinor_iff_forall_contract_delete, ← pred_delete_loop_iff he (P := P)] at hM
  exact hM.1 (hM.2 e heE).2

@[simp] theorem pred_removeLoops_iff [DeleteLoopClosed P] {M : Matroid α} [M.Finite] :
    P M.removeLoops ↔ P M := by
  set S := (M.cl ∅).powerset ∩ {X : Set α | (P M ↔ P (M ⧹ X))}
  have hfin : S.Finite
  · exact (M.ground_finite.subset (M.cl_subset_ground ∅)).finite_subsets.inter_of_left _
  obtain ⟨X, ⟨hXss : _ ⊆ M.cl ∅, hPX : P M ↔ P (M ⧹ X)⟩, hX⟩ :=
    Finite.exists_maximal_wrt id S hfin ⟨∅, by simp⟩
  obtain (hss | rfl) := hXss.ssubset_or_eq
  · obtain ⟨e, heX, hel⟩ := exists_of_ssubset hss
    refine (hel <|
      (hX (insert e X) ⟨insert_subset heX hXss, ?_⟩ (by simp)).symm.subset (mem_insert _ _)).elim
    rw [mem_setOf_eq, hPX, ← union_singleton, ← delete_delete, ← deleteElem,
      pred_delete_loop_iff (P := P)]
    rwa [delete_loop_iff, and_iff_left hel]
  rw [hPX, removeLoops_eq_delete]

/-- A matroid property `P` is `RemoveLoopClosed` if `P M ↔ P M.removeLoops` for all `M`.
  This property cannot hold for classes whose members are all finite, so is not so useful. -/
class RemoveLoopsClosed (P : ∀ {β : Type u}, Matroid β → Prop) : Prop :=
  /- `P` holds for `M` iff it holds after removing loops. -/
  (iff_removeLoops : ∀ {α : Type u} {M : Matroid α}, P M ↔ P M.removeLoops)

@[simp] theorem pred_removeLoops_iff' [RemoveLoopsClosed P] {M : Matroid α} :
    P M.removeLoops ↔ P M :=
  RemoveLoopsClosed.iff_removeLoops.symm

end Loops

section Simple

/-- Property `P` is unchanged by deleting loops and parallel copies. This is weaker than
  being closed under simplification, because simplification may remove an infinite set. -/
class DeleteParallelClosed (P : ∀ {β : Type u}, Matroid β → Prop) extends DeleteLoopClosed P :=
  (iff_delete_parallel :
    ∀ {α : Type u} {M : Matroid α} {e f : α}, M.Parallel e f → e ≠ f → (P (M ⧹ e) ↔ P M))

-- instance DeleteParallelClosed.deleteLoopClosed [DeleteParallelClosed P] : DeleteLoopClosed P where
--   iff_deleteLoop := fun {_ _} ↦ iff_delete_loop

theorem pred_delete_parallel_iff [DeleteParallelClosed P] {M : Matroid α} (hef : M.Parallel e f)
  (hne : e ≠ f) : P (M ⧹ e) ↔ P M :=
  DeleteParallelClosed.iff_delete_parallel hef hne

@[simp] theorem pred_simplification_iff (P : ∀ {β : Type u}, Matroid β → Prop)
    [DeleteParallelClosed P] {M : Matroid α} [M.Finite] : P M.simplification ↔ P M := by
  set S := {N | M.simplification ≤r N ∧ (P M ↔ P N)}
  have := M.finite_setOf_restriction.inter_of_right S
  obtain ⟨(N : Matroid α), ⟨⟨hNs, hNP⟩,hNM : N ≤r M⟩,hmin⟩ := Finite.exists_minimal_wrt
    (α := Matroid α) (β := Matroidᵣ α) id _
    (M.finite_setOf_restriction.inter_of_right {N | M.simplification ≤r N ∧ (P M ↔ P N)})
    ⟨M, ⟨M.simplification_restriction,Iff.rfl⟩, Restriction.refl⟩
  obtain (rfl | hNs) := hNs.eq_or_strictRestriction
  · rwa [Iff.comm]
  obtain (⟨e,he⟩ | ⟨e,f,hef,he,hf⟩) :=
    exists_loop_or_parallel_of_simplification_strictRestriction hNs hNM
  · rw  [← pred_delete_loop_iff (P := P) he] at hNP
    have hesi : e ∉ M.simplification.E :=
      fun he' ↦ M.simplification.not_loop e <| he.loop_restriction hNs.restriction he'
    rw [show N = N ⧹ e from hmin (N ⧹ e) ⟨⟨hNs.restriction.restriction_deleteElem hesi,hNP⟩,
      (delete_restriction _ _).trans hNM⟩ (delete_restriction _ _)] at he
    simp at he
  rw [← pred_delete_parallel_iff (P := P) hef (fun h ↦ he <| h ▸ hf)] at hNP
  rw [show N = N ⧹ e from hmin (N ⧹ e)
    ⟨⟨hNs.restriction.restriction_deleteElem he,hNP⟩, (delete_restriction _ _).trans hNM⟩
    (delete_restriction _ _)] at hef
  exact (hef.nonloop_left.mem_ground.2 rfl).elim





-- /-- A matroid property `P` is `SimpClosed` if it is unchanged by parallel extensions.
--   This is different from being closed under simplification (for instance, the property
--   of being finite is closed under the former but not the latter), but is the same in
--   a finite setting. -/
-- class SimpClosed (P : ∀ {α : Type u}, Matroid α → Prop) : Prop :=
--   (iff_parallel_extend : ∀ {β : Type u} {M : Matroid β} {e f : β}
--     M.Parallel
--     P (M.parallelExtend e f) ↔ P M )



/-- A matroid property `P` is `SimpClosed` if `P M ↔ P M.simplification` for all `M`. -/
class SimpClosed (P : ∀ {α : Type u}, Matroid α → Prop) : Prop :=
  /- `P` holds for `M` iff it holds after simplifying. -/
  (iff_simp : ∀ {β : Type u} {M : Matroid β}, P M ↔ P M.simplification)

@[simp] theorem pred_simplification_iff' (P : ∀ {β : Type u}, Matroid β → Prop) [SimpClosed P] :
    P M.simplification ↔ P M :=
  SimpClosed.iff_simp.symm

-- instance removeLoopClosed_of_simpClosed (P : ∀ {β : Type u}, Matroid β → Prop) [SimpClosed P] :
--     RemoveLoopClosed P where
--   iff_removeLoops := fun {α} M ↦ by
--     rw [← pred_simplification_iff P, Iff.comm, ← pred_simplification_iff P,
--       removeLoops_simplification_eq]

-- instance fieldRep.simpClosed {𝔽 : Type*} [Field 𝔽] : SimpClosed.{u} (FieldRep 𝔽) := by
--   refine ⟨fun {α M} ↦ ⟨fun ⟨h1,h2⟩ ↦ ?_, fun ⟨h1,h2⟩ ↦ ?_⟩⟩
--   sorry
--   sorry

-- theorem ExclMinor.simple [SimpClosed P] [MinorClosed P] (hM : M.ExclMinor P) : M.Simple := by
--   rw [← simplification_eq_self_iff]
--   apply hM.eq_of_not_prop_of_minor (simplification_restriction M).minor
--   simp_rw [pred_simplification_iff]
--   exact hM.not_prop_self

-- theorem ExclMinor.dual_simple [SimpClosed P] [MinorClosed P] [DualClosed P] (hM : M.ExclMinor P) :
--     M✶.Simple :=
--   hM.toDual.simple

end Simple

-- example (hM : M.ExclMinor (FieldRep (ZMod 2))) : M.Simple ∧ M✶.Simple ∧ M.Finite := by
--   constructor
--   · have := hM.simple
