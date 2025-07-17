import Matroid.Extension.ModularCut


open Set BigOperators Set.Notation Function

namespace Matroid

variable {α β : Type*} {ι : Type*} {η : Type*} {A : Set η} {M N : Matroid α}
    {B I J X X' Y Y' F : Set α} {e : α} {i j : ι} {Xs Ys Is Js : ι → Set α}

structure Projector (N M : Matroid α) (β : Type*) where
  carrier : Matroid (α ⊕ β)
  contract_eq' : carrier ／ range Sum.inr = N.mapEmbedding Embedding.inl
  delete_eq' : carrier ＼ range Sum.inr = M.mapEmbedding Embedding.inl

instance {N M : Matroid α} {β : Type*} : CoeOut (Projector N M β) (Matroid (α ⊕ β)) where
  coe P := P.carrier

lemma Projector.contract_eq (P : N.Projector M β) :
    (P : Matroid (α ⊕ β)) ／ range Sum.inr = N.mapEmbedding Embedding.inl := P.contract_eq'

lemma Projector.delete_eq (P : N.Projector M β) :
    (P : Matroid (α ⊕ β)) ＼ range Sum.inr = M.mapEmbedding Embedding.inl := P.delete_eq'

def Projector.pivot (P : N.Projector M β) : Set β :=
    Sum.inr ⁻¹' (P : Matroid (α ⊕ β)).E

lemma Projector.contract_image_pivot (P : N.Projector M β) :
    (P : Matroid (α ⊕ β)) ／ (.inr '' P.pivot) = N.mapEmbedding Embedding.inl := by
  rw [← P.contract_eq, eq_comm, ← contract_inter_ground_eq, pivot]
  sorry

/-- `N.IsProjectionBy M Y` means that `N` is obtained from `M` by projecting
some set with labels `Y`. -/
def IsProjectionBy (N M : Matroid α) (Y : Set β) : Prop :=
    ∃ P : Matroid (α ⊕ β), (
      P ／ (Sum.inr '' Y) = N.mapEmbedding Embedding.inl ∧
      P ＼ (Sum.inr '' Y) = M.mapEmbedding Embedding.inl )

def IsProjectionBy' (N M : Matroid α) (β : Type*) : Prop :=
    ∃ P : Matroid (α ⊕ β), (
      P ／ (range Sum.inr) = N.mapEmbedding Embedding.inl ∧
      P ＼ (range Sum.inr) = M.mapEmbedding Embedding.inl )

def IsProjection.{u} {α : Type u} (N M : Matroid α) : Prop :=
    ∃ (β : Type u) (Y : Set β), N.IsProjectionBy M Y

-- lemma IsProjectionBy'.comp {β γ : Type*} (h : N.IsProjectionBy' M β) (e : β ↪ γ) :
--     N.IsProjectionBy' M γ := by
--   obtain ⟨P, hPc, hPd⟩ := h
--   refine ⟨P.map (Sum.map id e) (by simp [InjOn]), ?_, ?_⟩
--   · rw [map_contra]

lemma exists_indep_coindep_of_delete_contract (M : Matroid α) (X : Set α) :
    ∃ (N : Matroid α) (I : Set α),
      I ⊆ X ∧ N.Indep I ∧ N.Coindep I ∧ N ＼ I = M ＼ X ∧ N ／ I = M ／ X := by
  wlog hX : X ⊆ M.E generalizing X with aux
  · obtain ⟨N, I, hss, hI, hI', hd, hc⟩ := aux (X ∩ M.E) inter_subset_right
    rw [contract_inter_ground_eq] at hc
    rw [delete_inter_ground_eq] at hd
    use N, I, hss.trans inter_subset_left, hI, hI', hd, hc
  obtain ⟨K, hK⟩ := M.exists_isBasis X
  obtain ⟨I, hI⟩ := (M ＼ (X \ K))✶.exists_isBasis K
    (subset_diff.2 ⟨hK.indep.subset_ground, disjoint_sdiff_right⟩)
  refine ⟨M ＼ (X \ K) ／ (K \ I), I, ?_, ?_, ?_, ?_, ?_⟩
  · grw [hI.subset, hK.subset]
  · rw [Indep.contract_indep_iff, and_iff_right disjoint_sdiff_right, delete_indep_iff,
      union_diff_cancel hI.subset, and_iff_right hK.indep]
    · exact disjoint_sdiff_right
    rw [delete_indep_iff, and_iff_left (disjoint_sdiff_right.mono_left diff_subset)]
    exact hK.indep.diff I
  · simpa [Coindep, disjoint_sdiff_right] using hI.indep
  · rw [← dual_inj]
    rw [dual_delete, dual_contract, ← contract_delete_comm _ disjoint_sdiff_right,
      ← hI.contract_eq_contract_delete, dual_delete, contract_contract,
      diff_union_of_subset hK.subset, dual_delete]
  rw [contract_contract, diff_union_of_subset hI.subset,
    ← contract_delete_comm _ disjoint_sdiff_right, hK.contract_eq_contract_delete]

lemma IsProjectionBy.mono {Y Z : Set β} (h : N.IsProjectionBy M Y) (hYZ : Y ⊆ Z) :
    N.IsProjectionBy M Z := by
  obtain ⟨P, hPc, hPd⟩ := h
  have hEss := diff_subset_iff.1 (congr_arg Matroid.E hPd).subset
  have hZY : Sum.inr '' Z ∩ P.E = Sum.inr '' Y ∩ P.E := by
    refine subset_antisymm (subset_inter ?_ inter_subset_right)
      (inter_subset_inter_left _ (image_subset _ hYZ))
    grw [hEss, inter_union_distrib_left, inter_eq_self_of_subset_right (image_subset _ hYZ),
      Disjoint.inter_eq (by simp [disjoint_left]), union_empty]
  refine ⟨P, ?_, ?_⟩
  · rw [← hPc, ← contract_inter_ground_eq, hZY, contract_inter_ground_eq]
  rw [← hPd, ← delete_inter_ground_eq, hZY, delete_inter_ground_eq]

lemma delete_isProjectionBy_contract (M : Matroid α) (X : Set α) :
    (M ／ X).IsProjectionBy (M ＼ X) X := by
  wlog hX : M.Indep X ∧ M.Coindep X with aux
  · obtain ⟨N, Y, hYX, hY, hY', hd, hc⟩ := exists_indep_coindep_of_delete_contract M X
    specialize aux N Y ⟨hY, hY'⟩
    rw [hc, hd] at aux
    exact aux.mono hYX
  set P : Matroid (α ⊕ α) := M.comapOn (.inl '' (M.E \ X) ∪ .inr '' X) (Sum.elim id id) with hP
  have hinj {I} (hss : I ⊆ M.E \ X) : InjOn (Sum.elim id id) (Sum.inl '' I ∪ Sum.inr '' X) := by
    suffices ∀ a ∈ X, a ∉ I by simpa [InjOn, imp_not_comm]
    exact fun a haX haI ↦ (hss haI).2 haX
  have hPX : P.Indep (.inr '' X) := by simp [hP, comapOn_indep_iff, image_image, hX.1, InjOn]
  refine ⟨P, ?_, ?_⟩
  · refine ext_indep (by simp [P]) fun I hIss ↦ ?_
    rw [contract_ground, hP, comapOn_ground_eq, union_diff_right,
      Disjoint.sdiff_eq_left (by simp [disjoint_left]), subset_image_iff] at hIss
    obtain ⟨I, hIss, rfl⟩ := hIss
    obtain ⟨hIE, hdj⟩ := subset_diff.1 hIss
    rw [hPX.contract_indep_iff, mapEmbedding_indep_iff, hX.1.contract_indep_iff]
    simp [hP, Embedding.inl, Sum.inl_injective.preimage_image, hdj, image_union,
      image_image, hIss, hinj hIss]
  refine ext_indep (by simp [P]) fun I hIss ↦ ?_
  rw [delete_ground, hP, comapOn_ground_eq, union_diff_right,
      Disjoint.sdiff_eq_left (by simp [disjoint_left]), subset_image_iff] at hIss
  obtain ⟨I, hIss, rfl⟩ := hIss
  obtain ⟨hIE, hdj⟩ := subset_diff.1 hIss
  simp [Embedding.inl, Sum.inl_injective.preimage_image, P, hIss, hdj, image_image,
    (hinj hIss).mono subset_union_left]
