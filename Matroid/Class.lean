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

def Invariant {η : Type*} (f : ∀ {α : Type u}, Matroid α → η) : Prop :=
  ∀ {α β : Type u} {M : Matroid α} {N : Matroid β}, M ≅ N → f M = f N

theorem Invariant.pred_iff_pred {P : ∀ {η : Type u}, Matroid η → Prop} (hP : Invariant P)
    {α β : Type u} {M : Matroid α} {N : Matroid β} (hMN : M ≅ N) : P M ↔ P N := by
  simp [hP hMN]

theorem Invariant.and {P Q : ∀ {η : Type u}, Matroid η → Prop} (hP : Invariant P)
    (hQ : Invariant Q) : Invariant (fun M ↦ P M ∧ Q M) := by
  intro α β M N hMN
  simp only [eq_iff_iff]
  rw [hP.pred_iff_pred hMN, hQ.pred_iff_pred hMN]

theorem invariant_finite : Invariant Matroid.Finite := by
  intro α β M N hMN
  simp only [eq_iff_iff]
  exact hMN.finite_iff

theorem invariant_finiteRk : Invariant Matroid.FiniteRk := by
  intro α β M N hMN
  simp only [eq_iff_iff]
  exact hMN.finiteRk_iff

-- def InvariantPred (f : ∀ {α : Type u}, Matroid α → Prop) : Prop :=
--   Invariant f

-- theorem Invariant.onIso {η α β : Type*} {f : ∀ {α : Type u}, Matroid α → η}
--     (hf : Invariant f) {M : Matroid α} {N : Matroid β} (hMN : M ≅ N) :


theorem invariant_erk : Invariant Matroid.erk := by
  intro _ _ _ _ hMN
  exact IsIso.erk_eq_erk hMN

theorem invariant_representable (𝔽 : Type*) [Field 𝔽] :
    Invariant (fun M ↦ M.Representable 𝔽) := by
  refine fun {α} {β} M N hMN ↦ ?_
  simp only [eq_iff_iff, hMN.representable_iff]

end Invariant

section Minor

/-- A minor-closed matroid property -/
class MinorClosed (P : ∀ {α : Type u}, Matroid α → Prop) : Prop :=
    (forall_minor : ∀ {α : Type u} {N M : Matroid α}, N ≤m M → P M → P N)

theorem Minor.pred_minor [MinorClosed P] (hNM : N ≤m M) (hM : P M) : P N :=
  MinorClosed.forall_minor hNM hM

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

theorem ExclMinor.prop_deleteElem (hM : M.ExclMinor P) (he : e ∈ M.E) : P (M ⟍ e) :=
  hM.prop_of_strictMinor (deleteElem_strictMinor he)

theorem ExclMinor.prop_contractElem (hM : M.ExclMinor P) (he : e ∈ M.E) : P (M ⟋ e) :=
  hM.prop_of_strictMinor (contractElem_strictMinor he)

theorem exclMinor_iff_forall_contract_delete [MinorClosed P] {M : Matroid α} :
    M.ExclMinor P ↔ ¬ P M ∧ ∀ e ∈ M.E, P (M ⟋ e) ∧ P (M ⟍ e) := by
  refine ⟨fun h ↦ ⟨h.not_prop_self, fun e he ↦ ⟨h.prop_contractElem he, h.prop_deleteElem he⟩⟩,
    fun h ↦ ⟨h.1, fun {N} hNM ↦ ?_⟩⟩
  obtain ⟨e, he, (hc | hd)⟩ := strictMinor_iff_minor_contract_or_delete.1 hNM
  · exact hc.pred_minor (h.2 e he).1
  exact hd.pred_minor (h.2 e he).2

instance minorClosed_finite : MinorClosed.{u} Matroid.Finite where
  forall_minor := fun a _ ↦ Minor.finite a

instance minorClosed_finiteRk : MinorClosed.{u} FiniteRk where
  forall_minor := fun a _ ↦ Minor.finiteRk a

instance minorClosed_finitary : MinorClosed.{u} Finitary where
  forall_minor := fun a _ ↦ Minor.finitary a

instance minorClosed_fieldRep (𝔽 : Type*) [Field 𝔽] :
    MinorClosed (FieldRep 𝔽) :=
  ⟨fun {_ _ _} hNM ⟨hMrep, hMfin⟩ ↦ ⟨hMrep.minor hNM, hNM.pred_minor hMfin⟩⟩

end Minor

section Dual

/-- A self-dual matroid parameter -/
def SelfDual (P : ∀ {α : Type u}, Matroid α → η) : Prop :=
  ∀ {α : Type u} (M : Matroid α), P M = P M﹡

/-- A matroid property that is preserved under taking duals. -/
class DualClosed (P : ∀ {α : Type u}, Matroid α → Prop) : Prop :=
  (forall_dual : ∀ {α : Type u} {M : Matroid α}, P M → P M﹡)

theorem toDualPred [DualClosed P] (hM : P M) : P M﹡ :=
  DualClosed.forall_dual hM

theorem ofDualPred [DualClosed P] (hM : P M﹡) : P M :=
  M.dual_dual ▸ toDualPred hM

@[simp] theorem iffDualPred [DualClosed P] : P M﹡ ↔ P M :=
  ⟨ofDualPred, toDualPred⟩

/-- The class of finite matroids is closed under duality -/
instance dualClosed_finite : DualClosed.{u} Matroid.Finite where
  forall_dual := fun a ↦ by infer_instance

/-- The class of finite `𝔽`-representable matroids is closed under duality -/
instance dualClosed_fieldRep (𝔽 : Type*) [Field 𝔽] : DualClosed.{u} (FieldRep 𝔽) where
  forall_dual := fun {_ _} ⟨hMrep, hMfin⟩ ↦ ⟨hMrep.dual, by infer_instance⟩

theorem ExclMinor.toDual [DualClosed P] (h : M.ExclMinor P) : M﹡.ExclMinor P :=
  ⟨fun h' ↦ h.1 <| ofDualPred h',
    fun {_} hNM ↦ ofDualPred (h.prop_of_strictMinor <| strictMinor_dual_iff_dual_strictMinor.1 hNM)⟩

end Dual

section Simple

/-- A matroid property `P` is `RemoveLoopClosed` if `P M ↔ P M.removeLoops` for all `M`. -/
class RemoveLoopClosed (P : ∀ {β : Type u}, Matroid β → Prop) : Prop :=
  /- `P` holds for `M` iff it holds after removing loops. -/
  (iff_removeLoops : ∀ {α : Type u} {M : Matroid α}, P M ↔ P M.removeLoops)

@[simp] theorem pred_removeLoops_iff [RemoveLoopClosed P] {M : Matroid α} : P M.removeLoops ↔ P M :=
  RemoveLoopClosed.iff_removeLoops.symm

theorem removeLoopClosed_iff_forall_delete :
    RemoveLoopClosed P ↔
      ∀ {α : Type u} {M : Matroid α} {X : Set α}, X ⊆ M.cl ∅ → (P M ↔ P (M ⟍ X)) := by
  refine ⟨fun h {α} M X hX ↦ ?_, fun h ↦ ⟨fun {γ M} ↦ ?_⟩ ⟩
  · rw [h.iff_removeLoops, Iff.comm, h.iff_removeLoops, removeLoops_eq_delete,
      removeLoops_eq_delete, delete_cl_eq, empty_diff, delete_delete, union_diff_self,
      union_eq_self_of_subset_left hX]
  simp only [removeLoops_eq_delete]
  exact h Subset.rfl

/-- In the setting of finite matroids, there would be an `iff` version of this lemma.  -/
theorem RemoveLoopClosed.iff_delete_loop (hP : RemoveLoopClosed P) {M : Matroid α} (he : M.Loop e) :
    P M ↔ P (M ⟍ e) := by
  rw [removeLoopClosed_iff_forall_delete] at hP
  apply hP
  simpa

theorem ExclMinor.loopless [RemoveLoopClosed P] [MinorClosed P] (hM : M.ExclMinor P) :
    M.Loopless := by
  rw [← removeLoops_eq_self_iff]
  apply hM.eq_of_not_prop_of_minor M.removeLoops_restriction.minor
  simp_rw [pred_removeLoops_iff]
  exact hM.not_prop_self

/-- A matroid property `P` is `SimpClosed` if `P M ↔ P M.simplification` for all `M`. -/
class SimpClosed (P : ∀ {α : Type u}, Matroid α → Prop) : Prop :=
  /- `P` holds for `M` iff it holds after simplifying. -/
  (iff_simp : ∀ {β : Type u} {M : Matroid β}, P M ↔ P M.simplification)

@[simp] theorem pred_simplification_iff (P : ∀ {β : Type u}, Matroid β → Prop) [SimpClosed P] :
    P M.simplification ↔ P M :=
  SimpClosed.iff_simp.symm

instance removeLoopClosed_of_simpClosed (P : ∀ {β : Type u}, Matroid β → Prop) [SimpClosed P] :
    RemoveLoopClosed P where
  iff_removeLoops := fun {α} M ↦ by
    rw [← pred_simplification_iff P, Iff.comm, ← pred_simplification_iff P,
      removeLoops_simplification_eq]

theorem ExclMinor.simple [SimpClosed P] [MinorClosed P] (hM : M.ExclMinor P) : M.Simple := by
  rw [← simplification_eq_self_iff]
  apply hM.eq_of_not_prop_of_minor (simplification_restriction M).minor
  simp_rw [pred_simplification_iff]
  exact hM.not_prop_self

end Simple

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
  exact ⟨((M ⟍ e).ground_finite.insert e).subset (by simp)⟩

theorem mem_iff_not_exists_exclMinor_minor [MinorClosed P] (M : Matroid α) [M.Finite] :
    P M ↔ ¬ ∃ N, N ≤m M ∧ N.ExclMinor P := by
  refine ⟨fun h ⟨N, hNM, hN⟩ ↦ hN.not_prop_self <| hNM.pred_minor h,
    fun h ↦ by_contra fun hM ↦ h ?_⟩
  obtain (hM' | hM') := em (M.ExclMinor P)
  · exact ⟨M, Minor.refl M, hM'⟩
  simp_rw [ExclMinor, not_and, not_forall] at hM'
  obtain ⟨N, hNM, hPN⟩ := hM' hM
  have := hNM.encard_ground_lt
  have hNfin := hNM.minor.finite
  have h' := mt (mem_iff_not_exists_exclMinor_minor (M := N)).2 hPN
  rw [not_not] at h'
  obtain ⟨N', hN'N, hN'⟩ := h'
  exact ⟨N', hN'N.trans hNM.minor, hN'⟩

termination_by _ => M.E.encard








section Finite
