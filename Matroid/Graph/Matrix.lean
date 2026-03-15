import Matroid.Graph.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyUnimodular
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Matroid.Graph.Walk.Cycle

open Set Matrix Function Classical BigOperators Finset

variable {α β : Type*} {G H : Graph α β} {x y z u v w : α} {e f : β} {F : Set β} {X Y : Set α}

namespace Graph

structure orientation (G : Graph α β) where
  dInc : E(G) → α × α
  isLink_of_dInc : ∀ e, G.IsLink e.val (dInc e).1 (dInc e).2

lemma orientation_nonempty : Nonempty (orientation G) := by
  let f : E(G) → α × α := fun e ↦
    let he := G.exists_isLink_of_mem_edgeSet e.prop
    (he.choose, he.choose_spec.choose)
  refine ⟨f, fun e ↦ ?_⟩
  generalize_proofs h at f
  exact (h e).choose_spec.choose_spec

namespace orientation

def anti (hGH : G ≤ H) (D : orientation H) : orientation G where
  dInc e := D.dInc ⟨e, edgeSet_mono hGH e.prop⟩
  isLink_of_dInc e := D.isLink_of_dInc ⟨e, edgeSet_mono hGH e.prop⟩ |>.of_le_of_mem hGH e.prop

@[simp]
lemma anti_apply (hGH : G ≤ H) (D : orientation H) (e : E(G)) :
    (D.anti hGH).dInc e = D.dInc ⟨e, edgeSet_mono hGH e.prop⟩ := rfl

variable {𝔽 : Type*} [CommRing 𝔽] [DecidablePred (· ∈ E(G))] [DecidableEq α]

def signedIncMatrix (D : orientation G) (𝔽 : Type*) [Ring 𝔽] : Matrix β α 𝔽 :=
  Matrix.of fun e ↦ if he : e ∈ E(G) then (update (0 : α → 𝔽) (D.dInc ⟨e, he⟩).2 (1 : 𝔽)) -
    (update (0 : α → 𝔽) (D.dInc ⟨e, he⟩).1 (1 : 𝔽)) else 0

lemma signedIncMatrix_apply_of_mem (he : e ∈ E(G)) (D : orientation G) :
    signedIncMatrix D 𝔽 e = (update (0 : α → 𝔽) (D.dInc ⟨e, he⟩).2 (1 : 𝔽)) -
    (update (0 : α → 𝔽) (D.dInc ⟨e, he⟩).1 (1 : 𝔽)) := by
  ext y
  simp only [signedIncMatrix, Matrix.of_apply]
  rw [dif_pos he, Pi.sub_apply]

lemma signedIncMatrix_apply_of_not_mem (he : e ∉ E(G)) (D : orientation G) :
    signedIncMatrix D 𝔽 e = 0 := by
  ext y
  simp only [signedIncMatrix, Matrix.of_apply]
  rw [dif_neg he]

lemma signedIncMatrix_anti_submatrix (hGH : G ≤ H) (he : e ∈ E(G)) (D : orientation H) :
    signedIncMatrix (D.anti hGH) 𝔽 e = signedIncMatrix D 𝔽 e := by
  ext x
  rw [signedIncMatrix_apply_of_mem (edgeSet_mono hGH he), signedIncMatrix_apply_of_mem he]
  simp

lemma signedIncMatrix_ne_zero_iff [Nontrivial 𝔽] (D : orientation G) :
    signedIncMatrix D 𝔽 e x ≠ 0 ↔ G.IsNonloopAt e x := by
  refine ⟨fun h ↦ ?_, fun ⟨y, hne, hxy⟩ ↦ ?_⟩
  · obtain he | he := _root_.em (e ∈ E(G)) |>.symm
    · simp [signedIncMatrix_apply_of_not_mem he] at h
    rw [signedIncMatrix_apply_of_mem he] at h
    obtain rfl | h1 := eq_or_ne x (D.dInc ⟨e, he⟩).1
    · obtain h2 | h2 := eq_or_ne (D.dInc ⟨e, he⟩).1 (D.dInc ⟨e, he⟩).2
      · rw [← h2] at h
        simp at h
      exact ⟨_, h2.symm, D.isLink_of_dInc ⟨e, he⟩⟩
    · obtain rfl | h2 := eq_or_ne x (D.dInc ⟨e, he⟩).2
      · exact ⟨_, h1.symm, (D.isLink_of_dInc ⟨e, he⟩).symm⟩
      simp [update_of_ne h2, update_of_ne h1] at h
  · rw [signedIncMatrix_apply_of_mem hxy.edge_mem]
    have hlink := D.isLink_of_dInc ⟨e, hxy.edge_mem⟩
    simp only at hlink
    obtain ⟨hx, hy⟩ | ⟨hx, hy⟩ := hxy.eq_and_eq_or_eq_and_eq hlink <;> rw [← hx, ← hy] <;>
      simp [hne.symm]

lemma signedIncMatrix_pendent_col_support [Nontrivial 𝔽] (hx : G.IsPendant e x) (D : orientation G):
    ((signedIncMatrix D 𝔽).col x).support = {e} := by
  ext f
  simp only [mem_support, col, transpose_apply, mem_singleton_iff]
  rw [D.signedIncMatrix_ne_zero_iff]
  exact ⟨fun h ↦ hx.edge_unique h.inc, fun h ↦ h ▸ hx.isNonloopAt⟩

open WList

variable {w : WList α β} [DecidableEq β]

def coeff_walk (hw : G.IsWalk w) (𝔽 : Type*) [Ring 𝔽] (D : orientation G) : β → 𝔽 :=
  fun e ↦ if he : e ∈ w.edge then
    if (w.dIncLast he).1 = (D.dInc ⟨e, hw.edge_mem_of_mem he⟩).1
    then (1 : 𝔽) else (-1 : 𝔽)
  else 0

omit [DecidablePred (· ∈ E(G))] in
lemma coeff_isCycleWalk_not_zero (hw : G.IsCyclicWalk w) (he : e ∈ w.edge) (𝔽 : Type*) [Ring 𝔽]
    [Nontrivial 𝔽] (D : orientation G) : D.coeff_walk hw.isWalk 𝔽 e ≠ 0 := by
  simp only [coeff_walk, dif_pos he]
  split_ifs <;> simp

lemma coeff_signedIncMatrix (hw : G.IsWalk w) (he : e ∈ w.edge) (D : orientation G) :
    D.coeff_walk hw 𝔽 e • D.signedIncMatrix 𝔽 e = (update (0 : α → 𝔽) (w.dIncLast he).2 (1 : 𝔽)) -
    (update (0 : α → 𝔽) (w.dIncLast he).1 (1 : 𝔽)) := by
  simp only [coeff_walk, dif_pos he, ite_smul, one_smul, neg_smul]
  have hd := hw.isLink_of_dInc (w.dIncLast_dInc he)
  split_ifs with heq <;> ext x
  · have hl := D.isLink_of_dInc ⟨e, hw.edge_mem_of_mem he⟩ |>.right_unique (heq ▸ hd)
    rw [signedIncMatrix_apply_of_mem (hw.edge_mem_of_mem he), heq, hl, Pi.sub_apply]
  have hl := hd.eq_and_eq_or_eq_and_eq <| D.isLink_of_dInc ⟨e, hw.edge_mem_of_mem he⟩
  simp only [heq, false_and, false_or] at hl
  simp [signedIncMatrix_apply_of_mem (hw.edge_mem_of_mem he), hl.1, hl.2]

omit [DecidablePred (· ∈ E(G))] in
lemma coeff_walk_cons_stable (hw : G.IsWalk (w.cons x e)) (hf : f ∈ w.edge) (D : orientation G) :
    (D.coeff_walk hw 𝔽 f) = (D.coeff_walk (by simp at hw; tauto : G.IsWalk w) 𝔽 f) := by
  simp [orientation.coeff_walk, hf, w.dIncLast_cons_of_mem hf]

lemma signedIncMatrix_isTrail (hw : G.IsTrail w) (hne : w.Nonempty) (D : orientation G) :
    (∑ e ∈ w.edge.toFinset, (D.coeff_walk hw.isWalk 𝔽 e) • (D.signedIncMatrix 𝔽 e)) =
    (update (0 : α → 𝔽) w.last (1 : 𝔽)) - (update (0 : α → 𝔽) w.first (1 : 𝔽)) := by
  induction w with
  | nil u => simp at hne
  | cons u e w ih =>
  obtain ⟨hw', he, hew⟩ := by simpa only [cons_isTrail_iff] using hw
  obtain ⟨v, rfl⟩ | hwne := w.exists_eq_nil_or_nonempty
  · simp [D.coeff_signedIncMatrix hw.isWalk (by simp : e ∈ _), dIncLast_cons]
  simp only [cons_edge, List.toFinset_cons, List.mem_toFinset, hew, not_false_eq_true,
    sum_insert, first_cons, last_cons]
  rw [Finset.sum_congr (rfl : w.edge.toFinset = _) (fun e he ↦ congrArg (· • signedIncMatrix D 𝔽 _)
    (D.coeff_walk_cons_stable hw.isWalk (by simpa using he : e ∈ w.edge))), ih hw' hwne,
    D.coeff_signedIncMatrix hw.isWalk (by simp)]
  simp [dIncLast_cons, hew, ↓reduceDIte]

lemma signedIncMatrix_isCyclicWalk (hw : G.IsCyclicWalk w) (D : orientation G) :
    (∑ e ∈ w.edge.toFinset, (D.coeff_walk hw.isWalk 𝔽 e) • (signedIncMatrix D 𝔽 e)) = 0 := by
  rw [D.signedIncMatrix_isTrail hw.isTrail hw.nonempty, hw.isClosed, sub_self]

end orientation
end Graph
