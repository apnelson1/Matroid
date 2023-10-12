import Mathlib.Logic.Equiv.LocalEquiv
import Mathlib.Data.Set.Card
import Mathlib.Data.Matrix.Basic

open Set Function

theorem diff_eq_diff_iff_inter_eq_inter {s t r : Set α} : s \ t = s \ r ↔ (t ∩ s = r ∩ s) := by
  rw [←diff_inter_self_eq_diff, ←diff_inter_self_eq_diff (t := r)] 
  refine' ⟨fun h ↦ _, fun h ↦ by rw [h]⟩
  rw [←diff_diff_cancel_left (inter_subset_right t s), h, 
    diff_diff_cancel_left (inter_subset_right r s)]

@[simp] theorem Set.diff_inter_diff_right {s t r : Set α} : (t \ s) ∩ (r \ s) = (t ∩ r) \ s := by
  simp only [diff_eq, inter_assoc, inter_comm sᶜ, inter_self]

theorem inter_diff_right_comm {s t r : Set α} : (s ∩ t) \ r = (s \ r) ∩ t := by  
  simp_rw [diff_eq, inter_right_comm]

theorem pair_diff_left {x y : α} (hne : x ≠ y) : ({x, y} : Set α) \ {x} = {y} := by 
  rw [insert_diff_of_mem _ (by exact rfl : x ∈ {x}), diff_singleton_eq_self (by simpa)]

theorem pair_diff_right {x y : α} (hne : x ≠ y) : ({x, y} : Set α) \ {y} = {x} := by 
  rw [pair_comm, pair_diff_left hne.symm]

lemma Set.InjOn.image_eq_image_iff_of_subset {f : α → β} (h : InjOn f s) (h₁ : s₁ ⊆ s) 
    (h₂ : s₂ ⊆ s) : f '' s₁ = f '' s₂ ↔ s₁ = s₂ := 
  ⟨fun h' ↦ by rw [←h.preimage_image_inter h₁, h', h.preimage_image_inter h₂], fun h' ↦ by rw [h']⟩
  
lemma Set.InjOn.image_subset_image_iff_of_subset {f : α → β} (h : InjOn f s) (h₁ : s₁ ⊆ s) 
    (h₂ : s₂ ⊆ s) : f '' s₁ ⊆ f '' s₂ ↔ s₁ ⊆ s₂ := by
  refine' ⟨fun h' ↦ _, image_subset _⟩   
  rw [←h.preimage_image_inter h₁, ←h.preimage_image_inter h₂]
  exact inter_subset_inter_left _ (preimage_mono h')

lemma Set.InjOn.image_diff' {f : α → β} (h : InjOn f s) : 
    f '' (s \ t) = f '' s \ f '' (s ∩ t) := by
  refine' Set.ext (fun y ↦ ⟨_,_⟩)
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx.1, rfl⟩, fun h' ↦ hx.2 (h.mem_of_mem_image (inter_subset_left _ _) hx.1 h').2⟩ 
  rintro ⟨⟨x, hx, rfl⟩,h'⟩
  exact ⟨x, ⟨hx,fun hxt ↦ h' ⟨x, ⟨hx,hxt⟩, rfl⟩⟩, rfl⟩ 
    
lemma Set.InjOn.image_diff {f : α → β} (h : InjOn f s) (hst : t ⊆ s) : 
    f '' (s \ t) = f '' s \ f '' t := by
  rw [h.image_diff', inter_eq_self_of_subset_right hst]

lemma Function.invFunOn_injOn_image_preimage [_root_.Nonempty α] (f : α → β) (S : Set α) : 
    InjOn f ((invFunOn f S) '' (f '' S)) := by
  rintro _ ⟨_,⟨x,hx, rfl⟩,rfl⟩ _ ⟨_,⟨y,hy,rfl⟩,rfl⟩ h
  rw [invFunOn_eq (f := f) ⟨x, hx, rfl⟩, invFunOn_eq (f := f) ⟨y,hy,rfl⟩] at h
  rw [h]

lemma Set.InjOn.exists_injOn_superset {f : α → β} {s t : Set α} (hinj : InjOn f s) (hst : s ⊆ t) : 
    ∃ r, s ⊆ r ∧ r ⊆ t ∧ InjOn f r ∧ f '' r = f '' t := by 
  
  obtain (hα | hα) := isEmpty_or_nonempty α
  · exact ⟨∅, by simp [eq_empty_of_isEmpty]⟩ 
  set d := t ∩ (f ⁻¹' (f '' t \ f '' s)) with hd
  set g := invFunOn f d with hg
  
  have hdj : Disjoint (f '' s) (f '' d)
  · rw [disjoint_iff_forall_ne]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ he  
    rw [hd, mem_inter_iff, mem_preimage, ←he] at hb
    exact hb.2.2 (mem_image_of_mem f ha)
  
  refine ⟨s ∪ g '' (f '' d), subset_union_left _ _, union_subset hst ?_, ?_, ?_⟩ 
  · exact (f.invFunOn_image_image_subset _).trans (inter_subset_left _ _)
  · rw [injOn_union, and_iff_right hinj, and_iff_right (invFunOn_injOn_image_preimage f _)]
    · rintro x hx _ ⟨_,⟨y,hy,rfl⟩,rfl⟩ he
      rw [hg, invFunOn_apply_eq (f := f) hy] at he
      rw [disjoint_iff_forall_ne] at hdj
      exact hdj (mem_image_of_mem f hx) (mem_image_of_mem f hy) he
    · exact disjoint_of_subset_right (f.invFunOn_image_image_subset _) hdj.of_image 
  rw [image_union, subset_antisymm_iff, union_subset_iff, and_iff_right (image_subset _ hst), 
    and_iff_right (image_subset _ _)]
  · rintro _ ⟨x, hxt, rfl⟩
    rw [mem_union]
    by_cases h : f x ∈ f '' s
    · left; assumption
    have hxd : x ∈ d
    · rw [hd, mem_inter_iff, and_iff_right hxt]
      exact ⟨mem_image_of_mem f hxt, h⟩  
    right
    
    refine ⟨g (f x), ⟨f x, ⟨g (f x), ?_, ?_⟩, rfl⟩, ?_⟩  
    · exact mem_of_mem_of_subset (invFunOn_apply_mem (f := f) hxd) Subset.rfl
    · rwa [invFunOn_apply_eq (f := f)]
    · rwa [invFunOn_apply_eq (f := f)]
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  exact mem_of_mem_of_subset (invFunOn_apply_mem (f := f) hx) (inter_subset_left _ _)

lemma Set.InjOn.exists_injOn_superset_image {f : α → β} {s s' : Set α} {t : Set β} 
    (hss' : s ⊆ s') (hinj : InjOn f s) (hst : f '' s ⊆ t) (ht : t ⊆ f '' s') : 
    ∃ r, s ⊆ r ∧ r ⊆ s' ∧ InjOn f r ∧ f '' r = t := by 
  rw [image_subset_iff] at hst
  obtain ⟨r, hsr, hrs', hinj, heq⟩ := hinj.exists_injOn_superset (subset_inter hss' hst)
  rw [subset_inter_iff] at hrs'
  refine ⟨r, hsr, hrs'.1, hinj, ?_⟩ 
  rw [heq, subset_antisymm_iff, image_subset_iff, and_iff_right (inter_subset_right _ _)]
  intro x hxt
  obtain ⟨y, hy, rfl⟩ := ht hxt 
  exact ⟨y, ⟨hy, hxt⟩, rfl⟩  

theorem Set.imageFactorization_injective (h : InjOn f s) : 
    Injective (s.imageFactorization f) := by 
  rintro ⟨x,hx⟩ ⟨y,hy⟩ h'
  simp_rw [imageFactorization, Subtype.mk.injEq, h.eq_iff hx hy] at h'  
  simp only [h']
section Lattice

lemma biUnion_insert_eq (hX : X.Nonempty) (Y : Set α) : ⋃ (x ∈ X), (insert x Y) = X ∪ Y := by
  have := hX.to_subtype
  simp_rw [←singleton_union, biUnion_eq_iUnion, ←iUnion_union, iUnion_singleton_eq_range, 
    Subtype.range_coe_subtype, setOf_mem_eq]
  
theorem Finite.exists_localEquiv_of_encard_eq [Nonempty α] [Nonempty β] {s : Set α} {t : Set β} 
    (hfin : s.Finite) (h : s.encard = t.encard) : 
    ∃ (e : LocalEquiv α β), e.source = s ∧ e.target = t := by 
  
  obtain ⟨f, hf⟩ := hfin.exists_bijOn_of_encard_eq h
  exact ⟨hf.toLocalEquiv, rfl, hf.toLocalEquiv_target⟩
  
end Lattice
section Matrix 

variable {m n R : Type} [Semiring R]

/-- For a semiring `R`, the modules `(n → R)` and `Matrix Unit n R` are linearly equivalent. -/
def Matrix.row_linearEquiv (n R : Type) [Semiring R] : (n → R) ≃ₗ[R] Matrix Unit n R where 
  toFun := Matrix.row 
  invFun A i := A () i
  map_add' := Matrix.row_add
  map_smul' := Matrix.row_smul
  left_inv := fun _ ↦ rfl 
  right_inv := fun _ ↦ rfl 

@[simp] theorem Matrix.row_linearEquiv_apply (f : n → R) :
    Matrix.row_linearEquiv n R x = Matrix.row x := rfl

@[simp] theorem Matrix.row_linearEquiv_apply_symm (A : Matrix Unit n R) :
    (Matrix.row_linearEquiv n R).symm A = A () := rfl

/-- For a semiring `R`, the modules `(m → R)` and `Matrix m Unit r` are linearly equivalent. -/
def Matrix.col_linearEquiv (m R : Type) [Semiring R] : (m → R) ≃ₗ[R] Matrix m Unit R where 
  toFun := Matrix.col 
  invFun A i := A i ()
  map_add' := Matrix.col_add
  map_smul' := Matrix.col_smul
  left_inv := fun _ ↦ rfl 
  right_inv := fun _ ↦ rfl 

@[simp] theorem Matrix.col_linearEquiv_apply (f : m → R) :
    Matrix.col_linearEquiv m R x = Matrix.col x := rfl

@[simp] theorem Matrix.col_linearEquiv_apply_symm (A : Matrix m Unit R) (i : m) :
    (Matrix.col_linearEquiv m R).symm A i = A i () := rfl