import Matroid.Uniform.Minor

namespace Matroid

open Set Function

variable {α : Type*} {M : Matroid α} {i j m n : ℕ} {e f x y : α} {I B : Set α} {a b : Fin n → α}

structure IsUpperTriangular (M : Matroid α) (a b : Fin n → α) : Prop where
  inj_left : Injective a
  -- inj_right : Injective b
  -- disjoint : Disjoint (range a) (range b)
  union_eq : range a ∪ range b = M.E
  indep_left : M.Indep (range a)
  -- isBase_right : M.IsBase (range b)
  isCircuit : ∀ i, M.IsCircuit (insert (b i) (a '' Iic i))
  -- closure_eq : ∀ i, M.closure (a '' Iio i) = M.closure (b '' Iio i)

lemma IsUpperTriangular.disjoint (h : M.IsUpperTriangular a b) : Disjoint (range a) (range b) := by
  rw [disjoint_left]
  rintro _ ⟨i, hi, rfl⟩ ⟨j, hj⟩
  exact (h.indep_left.subset (by grind)).not_dep (h.isCircuit j).dep

lemma IsUpperTriangular.apply_ne (h : M.IsUpperTriangular a b) {i j} : a i ≠ b j := by
  grind [disjoint_left.1 h.disjoint (mem_range_self i)]

lemma IsUpperTriangular.isBase_left (h : M.IsUpperTriangular a b) : M.IsBase (range a) := by
  refine h.indep_left.isBase_of_spanning ?_
  rw [spanning_iff_ground_subset_closure h.indep_left.subset_ground, ← h.union_eq, union_subset_iff,
    and_iff_right (M.subset_closure _ h.indep_left.subset_ground)]
  rintro _ ⟨i, hi, rfl⟩
  refine mem_of_mem_of_subset ((h.isCircuit i).mem_closure_diff_singleton_of_mem (mem_insert ..)) ?_
  grw [insert_diff_self_of_notMem, image_subset_range]
  grw [image_subset_range]
  simp [h.apply_ne]

lemma IsUpperTriangular.inj_right (h : M.IsUpperTriangular a b) : Injective b := by
  intro i j hij
  wlog hlt : i < j generalizing i j with aux
  · by_contra hcon
    exact hcon <| Eq.symm <| aux hij.symm (by grind)
  have hem := Set.ext_iff.1 (((h.isCircuit i).eq_of_subset_isCircuit (h.isCircuit j) ?_)) (a j)
  · simp_rw [mem_insert_iff, h.inj_left.mem_set_image, mem_Iic] at hem
    grind [h.apply_ne]
  grw [hij, Iic_subset_Iic.2 hlt.le]

lemma IsUpperTriangular.isBase_right (h : M.IsUpperTriangular a b) : M.IsBase (range b) := by
  suffices hi : M.Indep (range b) by
    refine hi.isBase_of_eRk_ge (finite_range b) ?_
    grw [hi.eRk_eq_encard, ← h.isBase_left.encard_eq_eRank, ← image_univ, h.inj_left.encard_image,
      ← image_univ, h.inj_right.encard_image]
  obtain rfl | n := n; simp [range_eq_empty]
  suffices aux : ∀ i, M.Indep (b '' (Iic i)) from (aux ⊤).subset <| by simp
  intro k
  induction k using Fin.induction with
  | zero =>
    refine ((h.isCircuit 0).diff_singleton_indep (e := a 0) (by grind)).subset ?_
    simp [Set.Iic, h.apply_ne.symm]
  | succ i ih =>
    rw [← Iio_insert, image_insert_eq, Indep.insert_indep_iff_of_notMem, mem_diff, and_iff_right]
    · intro hcl
      have hss : M.closure (b '' Iio i.succ) ⊆ M.closure (a '' Iio i.succ) := by
        refine closure_subset_closure_of_subset_closure ?_
        rintro _ ⟨j, hjmem : j < i.succ, rfl⟩
        refine mem_of_mem_of_subset
          ((h.isCircuit j).mem_closure_diff_singleton_of_mem (mem_insert ..)) ?_
        grw [insert_diff_self_of_notMem (by simp [h.apply_ne])]
        exact M.closure_subset_closure <| image_mono <| by grind
      specialize hss hcl
      rw [(h.indep_left.subset (image_subset_range ..)).mem_closure_iff_of_notMem
        (by simp [h.apply_ne])] at hss
      have hcon := (h.isCircuit i.succ).eq_of_dep_subset hss (by grind)
      apply_fun (a i.succ ∈ ·) at hcon
      simp [h.apply_ne, h.inj_left.eq_iff] at hcon
    · exact (h.isCircuit i.succ).subset_ground <| mem_insert ..
    · exact ih.subset <| image_mono <| by grind
    simp [h.inj_right.eq_iff]

lemma IsUpperTriangular.isCircuit' (h : M.IsUpperTriangular a b) (i : Fin n) :
    M.IsCircuit (insert (a i) (b '' Iic i)) := by
  _

lemma IsUpperTriangular.symm (h : M.IsUpperTriangular a b) : M.IsUpperTriangular b a where
  inj_left := h.inj_right
  inj_right := h.inj_left
  disjoint := h.disjoint.symm
  union_eq := union_comm _ _ ▸ h.union_eq
  isBase_left := h.isBase_right
  isBase_right := h.isBase_left
  foo i := by
    obtain rfl | n := n; apply finZeroElim i
    induction i using Fin.induction with
    | zero =>
      sorry
    | succ i ih =>

  -- closure_eq i := (h.closure_eq i).symm

lemma IsUpperTriangular.dual (h : M.IsUpperTriangular a b) :
    M✶.IsUpperTriangular (a ∘ Fin.rev) (b ∘ Fin.rev) where
  inj_left := h.inj_left.comp Fin.rev_injective
  inj_right := h.inj_right.comp Fin.rev_injective
  disjoint := by
    rw [Fin.rev_surjective.range_comp, Fin.rev_surjective.range_comp]
    exact h.disjoint
  union_eq := by
    rw [Fin.rev_surjective.range_comp, Fin.rev_surjective.range_comp, dual_ground, h.union_eq]
  isBase_left := by
    rw [Fin.rev_surjective.range_comp, ← diff_diff_cancel_left (h.isBase_left.subset_ground),
      ← h.union_eq, union_diff_cancel_left h.disjoint.inter_eq.subset, h.union_eq]
    exact h.isBase_right.compl_isBase_dual
  isBase_right := by
    rw [Fin.rev_surjective.range_comp, ← diff_diff_cancel_left (h.isBase_right.subset_ground),
      ← h.union_eq, union_diff_cancel_right h.disjoint.inter_eq.subset, h.union_eq]
    exact h.isBase_left.compl_isBase_dual
  closure_eq i := by
    ext e

    -- rw [image_comp, Fin.rev_iio]

lemma IsUpperTriangular.image_left_indep (h : M.IsUpperTriangular a b) (I : Set (Fin n)) :
    M.Indep (a '' I) :=
  h.isBase_left.indep.subset <| image_subset_range ..

lemma IsUpperTriangular.image_left_coindep (h : M.IsUpperTriangular a b) (I : Set (Fin n)) :
    M.Coindep (a '' I) := by
  _

lemma IsUpperTriangular.minor (h : M.IsUpperTriangular a b) (φ : Fin m ↪o Fin n) :
    (M ／ (a '' (range φ)ᶜ) ＼ (b '' (range φ)ᶜ)).IsUpperTriangular (a ∘ φ) (b ∘ φ) where
  inj_left := h.inj_left.comp φ.injective
  inj_right := h.inj_right.comp φ.injective
  disjoint := h.disjoint.mono (range_comp_subset_range ..) (range_comp_subset_range ..)
  union_eq := by
    rw [range_comp, range_comp, contract_delete_ground, ← h.union_eq,
      ← diff_diff, union_diff_distrib, image_compl_eq_range_diff_image h.inj_left,
      diff_diff_cancel_left (image_subset_range ..), Disjoint.sdiff_eq_left (a := range b),
      union_diff_distrib, Disjoint.sdiff_eq_left, image_compl_eq_range_diff_image h.inj_right,
      diff_diff_cancel_left (image_subset_range ..)]
    · exact h.disjoint.mono (by simp) (by simp)
    exact h.disjoint.symm.mono (by simp) (by simp)
  isBase_left := by
    rw [Coindep.delete_isBase_iff, range_comp, and_iff_left (h.disjoint.mono (by simp) (by simp)),
      Indep.contract_isBase_iff]
  isBase_right := _
  closure_eq := _
