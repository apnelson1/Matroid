import Matroid.Extension.Minor
import Matroid.ForMathlib.Matroid.Map
import Matroid.Order.Quotient

open Set BigOperators Set.Notation Function

namespace Matroid

universe u

variable {α β : Type*} {ι : Type*} {η : Type*} {A : Set η} {M N : Matroid α}
    {B I J X X' Y Y' F : Set α} {e : α} {i j : ι} {Xs Ys Is Js : ι → Set α}

/-- A matroid encoding the fact that `N` is a projection of `M`. -/
structure Projector (N M : Matroid α) (β : Type*) where
  carrier : Matroid (α ⊕ β)
  contract_eq' : carrier ／ range Sum.inr = N.map Sum.inl Sum.inl_injective.injOn
  delete_eq' : carrier ＼ range Sum.inr = M.map Sum.inl Sum.inl_injective.injOn

instance {α β : Type*} {N M : Matroid α} : CoeSort (Projector N M β) (Matroid (α ⊕ β)) where
  coe P := P.1

attribute [coe] Projector.carrier

/-- `N` is a projection of `M` if there exists a projector.
This works even if there are no elements outside the common ground set of `M` and `N`
to perform the projection within the type. -/
def IsProjection {α : Type u} (N M : Matroid α) : Prop :=
  ∃ (β : Type u), Nonempty (N.Projector M β)

lemma Projector.isProjection {α β : Type u} {M N : Matroid α} (P : N.Projector M β) :
    N.IsProjection M :=
  ⟨β, ⟨P⟩⟩

lemma Projector.contract_eq_mapEmbedding (P : N.Projector M β) :
    (P : Matroid (α ⊕ β)) ／ range Sum.inr = N.mapEmbedding Embedding.inl := P.contract_eq'

lemma Projector.contract_eq (P : N.Projector M β) :
    (P : Matroid (α ⊕ β)) ／ range Sum.inr = N.map Sum.inl Sum.inl_injective.injOn := P.contract_eq'

lemma Projector.delete_eq_eq_mapEmbedding (P : N.Projector M β) :
    (P : Matroid (α ⊕ β)) ＼ range Sum.inr = M.mapEmbedding Embedding.inl := P.delete_eq'

lemma Projector.delete_eq (P : N.Projector M β) :
    (P : Matroid (α ⊕ β)) ＼ range Sum.inr = M.map Sum.inl Sum.inl_injective.injOn := P.delete_eq'

lemma Projector.inl_mem_ground_iff {P : N.Projector M β} {e : α} :
    Sum.inl e ∈ (P : Matroid (α ⊕ β)).E ↔ e ∈ M.E := by
  revert e
  have h := congr_arg Matroid.E P.delete_eq
  simpa [Set.ext_iff] using h

lemma Projector.contract_comap_eq (P : N.Projector M β) :
    ((P : Matroid (α ⊕ β)) ／ range Sum.inr).comap .inl = N := by
  rw [P.contract_eq]
  exact comap_map Embedding.inl.injective

lemma Projector.delete_comap_eq (P : N.Projector M β) :
    ((P : Matroid (α ⊕ β)) ＼ range Sum.inr).comap .inl = M := by
  rw [P.delete_eq]
  exact comap_map Embedding.inl.injective

def Projector.pivot (P : N.Projector M β) : Set β :=
    Sum.inr ⁻¹' (P : Matroid (α ⊕ β)).E

lemma Projector.contract_image_pivot (P : N.Projector M β) :
    (P : Matroid (α ⊕ β)) ／ (.inr '' P.pivot) = N.map _ Sum.inl_injective.injOn := by
  rw [← P.contract_eq, eq_comm, ← contract_inter_ground_eq, pivot, image_preimage_eq_range_inter]

lemma Projector.delete_image_pivot (P : N.Projector M β) :
    (P : Matroid (α ⊕ β)) ＼ (.inr '' P.pivot) = M.map _ Sum.inl_injective.injOn := by
  rw [← P.delete_eq, eq_comm, ← delete_inter_ground_eq, pivot, image_preimage_eq_range_inter]

lemma Projector.preimage_inl_eq_left (P : N.Projector M β) :
    .inl ⁻¹' (P : Matroid (α ⊕ β)).E = N.E := by
  simp [← P.contract_comap_eq]

@[simp]
lemma Projector.preimage_inl_eq_right (P : N.Projector M β) :
    .inl ⁻¹' (P : Matroid (α ⊕ β)).E = M.E := by
  simp [← P.delete_comap_eq]

lemma Projector.ground_eq (P : N.Projector M β) : N.E = M.E := by
  rw [← P.preimage_inl_eq_left, ← P.preimage_inl_eq_right]

def Projector.dual (P : N.Projector M β) : M✶.Projector N✶ β where
  carrier := P✶
  contract_eq' := by rw [← dual_delete, P.delete_eq, map_dual]
  delete_eq' := by rw [← dual_contract, P.contract_eq, map_dual]

lemma Projector.map_aux {γ : Type*} (P : N.Projector M β) (f : β → γ) (hf : InjOn f P.pivot) :
    (P : Matroid (α ⊕ β)).map (Sum.map id f) (by simp_rw [InjOn]; aesop) ／ range Sum.inr
    = N.mapEmbedding Embedding.inl := by
  rw [← contract_inter_ground_eq]
  have heq := P.contract_image_pivot
  have hinj : InjOn (Sum.map id f) ((P : Matroid (α ⊕ β)) ／ Sum.inr '' P.pivot).E := by
    rw [InjOn]
    aesop
  have heq : ((P : Matroid (α ⊕ β)) ／ Sum.inr '' P.pivot).map (Sum.map id f) hinj =
      (N.map Sum.inl Sum.inl_injective.injOn).map (Sum.map id f) (by rwa [← heq]) := by
    simp_rw [heq]
  simp_rw [map_map] at heq
  generalize_proofs h1
  rw [contract_map h1 (by simp [Projector.pivot])] at heq
  convert heq
  ext (a | b) <;> simp [Projector.pivot]

def Projector.map {γ : Type u} (P : N.Projector M β) (f : β → γ) (hf : InjOn f P.pivot) :
    N.Projector M γ where
  carrier := Matroid.map (P : Matroid (α ⊕ β)) (Sum.map id f) (by simp_rw [InjOn]; aesop)
  contract_eq' := P.map_aux _ hf
  delete_eq' := by
    rw [← dual_inj, dual_delete, map_dual, map_dual]
    exact P.dual.map_aux f hf

@[simp]
lemma Projector.map_pivot {γ : Type u} (P : N.Projector M β) (f : β → γ) (hf : InjOn f P.pivot) :
    (P.map f hf).pivot = f '' P.pivot := by
  simp [Projector.pivot, Projector.map, Set.ext_iff]

lemma Projector.delete_contract_aux (M : Matroid α) (X : Set α) :
    M.comapOn (Sum.inl '' (M.E \ X) ∪ Sum.inr '' (X ∩ M.E)) (Sum.elim id id) ＼ range Sum.inr =
    (M ＼ X).mapEmbedding Embedding.inl := by
  have hrw : (Sum.inl '' (M.E \ X) ∪ Sum.inr '' (X ∩ M.E)) \ range Sum.inr
      = Sum.inl '' (M.E \ X) := by rw [union_diff_distrib,
      Disjoint.sdiff_eq_left (by simp [disjoint_left]), diff_eq_empty.2 (image_subset_range ..),
      union_empty]
  refine ext_indep (by simp [hrw]) ?_
  simp +contextual [ hrw, image_image, Embedding.inl, Sum.inl_injective.preimage_image,
      subset_diff, InjOn]

lemma Projector.bijOn_aux {X : Set α} (hX : X ⊆ M.E) :
    BijOn (Sum.elim id (Subtype.val : X → α)) (Sum.inl '' (M.E \ X) ∪ range Sum.inr) M.E := by
  refine ⟨?_, ?_, ?_⟩
  · simp [subset_def ▸ hX, (mapsTo_id _).mono_left diff_subset]
  · simp_rw [InjOn]
    aesop
  simp [SurjOn, image_union, ← range_comp, image_image]

def Projector.delete_contract' (M : Matroid α) (X : Set α) (hX : X ⊆ M.E) :
    (M ／ X).Projector (M ＼ X) X where
  carrier := M.comapOn (.inl '' (M.E \ X) ∪ range .inr) (Sum.elim id Subtype.val)
  contract_eq' := by
    apply Matroid.map_inj (Sum.elim id Subtype.val) (by simp [InjOn])
    rw [contract_map _ (by simp), map_comapOn (Projector.bijOn_aux hX)]
    simp [map_map, ← range_comp]
    · intro a ha b hb hab
      simp at ha hb hab ⊢
      obtain ⟨a', ⟨ha'M, ha'X⟩, rfl⟩ | ⟨a', ha'X, rfl⟩ := ha <;>
      obtain ⟨b', ⟨hb'M, hb'X⟩, rfl⟩ | ⟨b', hb'X, rfl⟩ := hb <;>
      simp_all
      exact hb'X (hab ▸ ha'X)
  delete_eq' := by
    apply Matroid.map_inj (Sum.elim id Subtype.val) (by simp [InjOn])
    rw [delete_map _ (by simp), map_comapOn (Projector.bijOn_aux hX)]
    simp [map_map, ← range_comp]
    · intro a ha b hb hab
      simp at ha hb hab ⊢
      obtain ⟨a', ⟨ha'M, ha'X⟩, rfl⟩ | ⟨a', ha'X, rfl⟩ := ha <;>
      obtain ⟨b', ⟨hb'M, hb'X⟩, rfl⟩ | ⟨b', hb'X, rfl⟩ := hb <;>
      simp_all
      exact hb'X (hab ▸ ha'X)

def Projector.copy {M M' N N' : Matroid α} (P : N.Projector M β) (hN : N = N') (hM : M = M') :
    N'.Projector M' β where
  carrier := P
  contract_eq' := by rw [P.contract_eq, hN]
  delete_eq' := by rw [P.delete_eq, hM]

def Projector.delete_contract (M : Matroid α) (X : Set α) : (M ／ X).Projector (M ＼ X) X :=
  ((Projector.delete_contract' M (X ∩ M.E) inter_subset_right).copy
    (contract_inter_ground_eq ..) (delete_inter_ground_eq ..)).map (inclusion inter_subset_left)
    (inclusion_injective _).injOn

lemma exists_indep_coindep_of_delete_contract (M : Matroid α) (X : Set α) :
    ∃ (N : Matroid α) (I : Set α),
      N ≤m M ∧ I ⊆ X ∧ N.Indep I ∧ N.Coindep I ∧ N ＼ I = M ＼ X ∧ N ／ I = M ／ X := by
  wlog hX : X ⊆ M.E generalizing X with aux
  · obtain ⟨N, hN, I, hss, hI, hI', hd, hc⟩ := aux (X ∩ M.E) inter_subset_right
    rw [contract_inter_ground_eq] at hc
    rw [delete_inter_ground_eq] at hd
    use N, hN, I, hss.trans inter_subset_left, hI, hI', hd, hc
  obtain ⟨K, hK⟩ := M.exists_isBasis X
  obtain ⟨I, hI⟩ := (M ＼ (X \ K))✶.exists_isBasis K
    (subset_diff.2 ⟨hK.indep.subset_ground, disjoint_sdiff_right⟩)
  refine ⟨M ＼ (X \ K) ／ (K \ I), I, delete_contract_isMinor .., ?_, ?_, ?_, ?_, ?_⟩
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

/-- We can always choose a projector so that the pivot set is independent and coindepent,
and consists of the entire type of projected elements. -/
lemma IsProjection.exists_good_projector {α : Type u} {M N : Matroid α} (h : N.IsProjection M) :
    ∃ (β : Type u) (P : N.Projector M β),
      (P : Matroid (α ⊕ β)).E = .inl '' M.E ∪ range .inr ∧
      (P : Matroid (α ⊕ β)).Indep (range .inr) ∧
      (P : Matroid (α ⊕ β)).Coindep (range .inr) := by
  obtain ⟨β, ⟨P⟩⟩ := h
  obtain ⟨M', J, hM', hJ, hJi, hJi', hd, hc⟩ :=
    exists_indep_coindep_of_delete_contract (P : Matroid (α ⊕ β)) (range .inr)
  obtain ⟨J, rfl⟩ := subset_range_iff_exists_image_eq.1 hJ
  have hbij : BijOn (Sum.map id (Subtype.val : J → β)) (Sum.inl '' M.E ∪ range Sum.inr) M'.E := by
    rw [← P.preimage_inl_eq_right]
    refine ⟨?_, by simp [InjOn], ?_⟩
    · rintro (x | ⟨x, hx⟩)
      simp only [mem_union, mem_image, mem_preimage, Sum.inl.injEq, exists_eq_right, mem_range,
        reduceCtorEq, exists_false, or_false, Sum.map_inl, id_eq]
      · exact fun hx ↦ ((congr_arg Matroid.E hc).symm.subset ⟨hx, by simp⟩).1
      suffices .inr x ∈ M'.E by simpa
      grw [← hJi.subset_ground]
      exact mem_image_of_mem _ hx
    simp only [SurjOn, Sum.map, CompTriple.comp_eq, image_union, image_image, Sum.elim_inl,
      ← range_comp]
    rw [image_preimage_eq_inter_range, Sum.elim_comp_inr, range_comp, Subtype.range_val,
      union_comm, ← diff_subset_iff, ← M'.delete_ground, hd, delete_ground,
      subset_inter_iff, and_iff_right diff_subset, diff_subset_iff]
    simp
  refine ⟨J, ⟨M'.comapOn (Sum.inl '' M.E ∪ range .inr) (Sum.map id Subtype.val), ?_, ?_⟩,
    by simp, ?_, ?_⟩
  · refine Matroid.map_inj (Sum.map id Subtype.val) (by simp [InjOn]) ?_
    rw [contract_map (by simp) (by simp), map_comapOn hbij]
    simp only [Sum.map, CompTriple.comp_eq, ← range_comp, Sum.elim_comp_inr]
    simp only [range_comp, Subtype.range_coe_subtype, setOf_mem_eq, map_map, Sum.elim_comp_inl]
    rw [hc, P.contract_eq]

  · refine Matroid.map_inj (Sum.map id Subtype.val) (by simp [InjOn]) ?_
    rw [delete_map (by simp) (by simp), map_comapOn hbij, map_map]
    simp only [Sum.map, CompTriple.comp_eq, ← range_comp, Sum.elim_comp_inr, Sum.elim_comp_inl]
    simp only [range_comp, Subtype.range_coe_subtype, setOf_mem_eq, hd, P.delete_eq]
  · suffices M'.Indep (range (Sum.inr ∘ Subtype.val)) by simpa [Sum.map, ← range_comp]
    simpa [range_comp]
  suffices M'.Coindep (range (Sum.inr ∘ Subtype.val)) by
    simpa [Coindep, comapOn_dual_eq_of_bijOn hbij, ← range_comp]
  simpa [range_comp]

lemma delete_isProjection_contract (M : Matroid α) (X : Set α) : (M ／ X).IsProjection (M ＼ X) :=
  ⟨_, ⟨Projector.delete_contract M X⟩⟩

/-- Given a modular cut `U` in `M`,
the projector certifying that `M.projectBy U` is a single-element projection of `M`. -/
def ModularCut.Projector (U : M.ModularCut) : (M.projectBy U).Projector M Unit where
  carrier := (M.map Sum.inl Sum.inl_injective.injOn).extendBy
    (.inr ()) (U.map Sum.inl Sum.inl_injective.injOn)
  contract_eq' := by
    rw [← image_univ, ← Subsingleton.eq_univ_of_nonempty (s := {()}) (by simp),
      image_singleton, (U.map Sum.inl Sum.inl_injective.injOn).extendBy_contractElem (by simp),
      ModularCut.projectBy_map]
  delete_eq' := by
    rw [← image_univ, ← Subsingleton.eq_univ_of_nonempty (s := {()}) (by simp),
      image_singleton, (U.map Sum.inl Sum.inl_injective.injOn).extendBy_deleteElem (by simp)]

lemma IsProjection.Quotient (h : N.IsProjection M) : N ≤q M := by
  obtain ⟨β, ⟨P⟩⟩ := h
  simp_rw [← P.contract_comap_eq, ← P.delete_comap_eq]
  exact ((P : Matroid (α ⊕ β)).contract_quotient_delete (range .inr)).comap Sum.inl

/-- The projector for `M` and itself. -/
def Projector.refl (M : Matroid α) : M.Projector M (Fin 0) where
  carrier := M.map Sum.inl Sum.inl_injective.injOn
  contract_eq' := by simp
  delete_eq' := by simp

-- def Projector.comp_projectBy_modularCut {M N : Matroid α} (P : N.Projector M β)
-- (U : N.ModularCut) :
--     (N.projectBy U).Projector M (Option β) where
--   carrier :=
--     have hinj : InjOn (Sum.map id some) (P : Matroid (α ⊕ β)).E := by simp [InjOn]
--     ((P : Matroid (α ⊕ β)).map _ hinj).extendBy (.inr none)
--       <| ((U.map Sum.inl Sum.inl_injective.injOn).copy P.contract_eq.symm).ofContract'.map _ hinj
--   contract_eq' := by
--     simp only
--     have hrw1 : range (Sum.inr : Option β → α ⊕ Option β)
--       = {.inr none} ∪ (.inr '' (range some)) := by ext (a | rfl | b) <;> simp
--     obtain rfl | hne := eq_or_ne U ⊤
--     simp
--     rw [hrw1, ← contract_contract]
--     rw [← ModularCut.projectBy_map]
--   delete_eq' := _


/-- If `P` is a projector for `N` and `M` using a type `β` that is small enough to map into
the complement of `M.E`, then in fact `N` and `M` have a common major within their own type. -/
lemma Projector.exists_contract_delete_of_embedding (P : N.Projector M β) (φ : β ↪ α)
    (hφ : Disjoint (range φ) M.E) : ∃ (Q : Matroid α), Q ／ (range φ) = N ∧ Q ＼ range φ = M := by
  have hss : Sum.inr '' P.pivot ⊆ (P : Matroid (α ⊕ β)).E := by simp [Projector.pivot]
  have hinj :  InjOn (Sum.elim id φ) (P : Matroid (α ⊕ β)).E := by
    have aux : (∀ a ∈ M.E, ∀ (b : β), Sum.inr b ∈ (P : Matroid (α ⊕ β)).E → ¬a = φ b) := by
      rintro _ hE b hmem rfl
      simpa using hφ.notMem_of_mem_right hE
    simp only [InjOn, Sum.forall, P.inl_mem_ground_iff, Sum.elim_inl, id_eq, Sum.elim_inr,
      Sum.inl.injEq, reduceCtorEq, EmbeddingLike.apply_eq_iff_eq, Sum.inr.injEq, ]
    tauto
  refine ⟨(P : Matroid (α ⊕ β)).map (Sum.elim id φ) hinj, ?_, ?_⟩
  · rw [← contract_inter_ground_eq, map_ground]
    convert ((P : Matroid (α ⊕ β)).contract_map hinj hss).symm
    · simp [image_sumElim, inter_union_distrib_left, hφ.inter_eq,
        inter_eq_self_of_subset_right (image_subset_range ..), pivot, image_image]
    simp [P.contract_image_pivot, map_map]
  rw [← delete_inter_ground_eq, map_ground]
  convert ((P : Matroid (α ⊕ β)).delete_map hinj hss).symm
  · simp [image_sumElim, inter_union_distrib_left, hφ.inter_eq,
      inter_eq_self_of_subset_right (image_subset_range ..), pivot, image_image]
  simp [P.delete_image_pivot, map_map]
