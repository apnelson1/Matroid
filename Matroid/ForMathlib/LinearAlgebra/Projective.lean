import Mathlib.LinearAlgebra.Projectivization.Independence
import Mathlib.LinearAlgebra.Projectivization.Subspace
import Matroid.ForMathlib.LinearAlgebra.LinearIndependent
import Matroid.ForMathlib.LinearAlgebra.Submodule

variable {ι K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]

open Set Function Projectivization

@[simp]
lemma Projectivization.independent_map_mk_iff (f : ι → V) (hf0 : ∀ i, f i ≠ 0) :
    Independent (fun i ↦ mk K (f i) (hf0 i)) ↔ LinearIndependent K f := by
  rw [independent_iff]
  choose c hc using fun i ↦ exists_smul_eq_mk_rep K (f i) (hf0 i)
  convert LinearIndependent.units_smul_iff _ (w := c)
  ext
  simp [← hc]

lemma Projectivization.Independent.linearIndependent {f : ι → V} {hf0 : ∀ i, f i ≠ 0}
    (h : Independent (fun i ↦ Projectivization.mk K (f i) (hf0 i))) : LinearIndependent K f := by
  simpa using h

lemma LinearIndependent.independent_map_projectivization_mk {f : ι → V}
    (h : LinearIndependent K f) :
    Independent (fun i ↦ Projectivization.mk K (f i) (h.ne_zero i)) := by
  simpa

@[simp]
theorem Projectivization.independent_subsingleton [Subsingleton ι] (f : ι → Projectivization K V) :
    Independent f := by
  simp [independent_iff, rep_nonzero]

lemma Projectivization.independent_equiv {ι' : Type*} (e : ι ≃ ι') {f : ι' → Projectivization K V} :
    Independent (f ∘ e) ↔ Independent f := by
  rw [independent_iff (f := f), ← linearIndependent_equiv e, independent_iff, comp_assoc]

lemma Projectivization.Independent.comp {ι' : Type*} {v : ι → Projectivization K V}
    (hv : Independent v) (f : ι' → ι) (hf : Injective f) : Independent (v ∘ f) := by
  rw [independent_iff] at hv ⊢
  exact hv.comp f hf

@[simp]
lemma Projectivization.mk_smul_eq {u : V} (hu : u ≠ 0) (c : Kˣ) :
    mk K (c • u) (by rwa [smul_ne_zero_iff_ne]) = mk K u hu :=
  (mk_eq_mk_iff ..).2 ⟨c, rfl⟩

lemma Projectivization.mk_smul_eq' {u : V} (hu : u ≠ 0) {c : K} (hc : c ≠ 0) :
    mk K (c • u) (by simp [hc, hu]) = mk K u hu :=
  (mk_eq_mk_iff' ..).2 ⟨c, rfl⟩

lemma Projectivization.exists_smul_mk_rep_eq (K : Type*) {V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] (v : V) (hv : v ≠ 0) : ∃ c : Kˣ, c • (mk K v hv).rep = v := by
  obtain ⟨c, hc⟩ := exists_smul_eq_mk_rep K v hv
  exact ⟨c⁻¹, by simp [← hc]⟩

lemma Projectivization.mem_submodule_iff (K : Type*) {V : Type*} [DivisionRing K] [AddCommGroup V]
    [Module K V] {v : V} {w : Projectivization K V} (hv : v ≠ 0) :
    v ∈ w.submodule ↔ mk K v hv = w := by
  obtain ⟨a, ha⟩ := exists_smul_eq_mk_rep K v hv
  rw [w.submodule_eq, Submodule.mem_span_singleton₀ hv, ← mk_eq_mk_iff _ _ _ hv w.rep_nonzero,
    mk_rep]

@[simp]
lemma Submodule.mk_rep_mem_iff_mem (K : Type*) {V : Type*} [DivisionRing K] [AddCommGroup V]
    [Module K V] {W : Submodule K V} {v : V} (hv : v ≠ 0) :
    (Projectivization.mk K v hv).rep ∈ W ↔ v ∈ W := by
   obtain ⟨c, hc⟩ := exists_smul_eq_mk_rep K v hv
   rw [← hc, Submodule.smul_mem_iff']

@[simp]
lemma Projectivization.independent_pair {u v : Projectivization K V} :
    Independent (fun x : ({u,v} : Set _) ↦ x.1) := by
  rw [independent_iff]
  obtain rfl | hne := eq_or_ne u v
  · simp [u.rep_nonzero]
  refine (linearIndependent_restrict_pair_iff (V := V) (K := K) (fun x ↦ x.rep) hne
    (rep_nonzero u)).2 fun c hc ↦ hne ?_
  have hc0 : c ≠ 0 := by rintro rfl; simpa [v.rep_nonzero] using hc.symm
  simpa [← hc, mk_smul_eq' u.rep_nonzero hc0] using v.mk_rep

@[simp]
lemma Projectivization.submodule_span_range_rep (K W : Type*) [DivisionRing K] [AddCommGroup W]
    [Module K W] : Submodule.span K (range (Projectivization.rep (K := K) (V := W))) = ⊤ := by
  have b := Basis.ofVectorSpace K W
  ext x
  simp only [Submodule.mem_top, iff_true]
  refine mem_of_mem_of_subset (b.mem_span x) (Submodule.span_le.2 ?_)
  rintro _ ⟨i, rfl⟩
  have hi0 := b.ne_zero i
  have hmem : b i ∈ Submodule.span K {(mk (K := K) (V := W) (b i) hi0).rep} := by
    rw [Submodule.mem_span_singleton₀ (b.ne_zero i), ← mk_eq_mk_iff _ _ _ hi0]
    · simp only [mk_rep]
    exact rep_nonzero (mk K (b i) hi0)
  exact mem_of_mem_of_subset hmem <| Submodule.span_mono <| by simp


variable {ι K V : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma Projectivization.Subspace.mem_span_iff_rep (K : Type*) {V : Type*} [Field K] [AddCommGroup V]
    [Module K V] (s : Set (Projectivization K V)) (b : Projectivization K V) :
    b ∈ Subspace.span s ↔ b.rep ∈ Submodule.span K (Projectivization.rep '' s) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · induction' h with x hxs x₁ x₂ hx₁0 hx₂0 hx₁x₂ hx₁ hx₂ hx₁' hx₂'
    · exact mem_of_mem_of_subset (mem_image_of_mem _ hxs) Submodule.subset_span
    simp only [Submodule.mk_rep_mem_iff_mem] at hx₁' hx₂' ⊢
    exact Submodule.add_mem _ hx₁' hx₂'
  suffices aux : ∀ ⦃a⦄ (hasp : a ∈ Submodule.span K (Projectivization.rep '' s)) (ha : a ≠ 0),
      Projectivization.mk K a ha ∈ Subspace.span s by
    simpa using aux h b.rep_nonzero
  refine fun a ↦ Submodule.span_induction
    (p := fun a ha ↦ ∀ ha0, Projectivization.mk K a ha0 ∈ Subspace.span s) ?_ (by simp) ?_ ?_
  · simpa [rep_nonzero] using fun _ h ↦ Subspace.subset_span _ h
  · intro x y hx hy hx' hy' hxy
    obtain rfl | hx0 := eq_or_ne x 0
    · simpa using hy' (by simpa using hxy)
    obtain rfl | hy0 := eq_or_ne y 0
    · simpa using hx' (by simpa using hxy)
    refine (Subspace.span s).mem_add _ _ hx0 hy0 hxy (hx' hx0) (hy' hy0)
  intro a x hx hx' ha0
  simp only [ne_eq, smul_eq_zero, not_or] at ha0
  simpa [mk_smul_eq' ha0.2 ha0.1] using hx' ha0.2

lemma Projectivization.Subspace.mem_span_image_rep_iff (K : Type*) {V : Type*} [Field K]
    [AddCommGroup V] [Module K V] (s : Set (Projectivization K V)) {a : V} (ha : a ≠ 0) :
    a ∈ Submodule.span K (Projectivization.rep '' s) ↔ Projectivization.mk K a ha ∈ span s := by
  simp [Subspace.mem_span_iff_rep]

lemma Projectivization.Subspace.rep_mem_span_image_iff (K : Type*) {V ι : Type*} [Field K]
    [AddCommGroup V] [Module K V] {f : ι → Projectivization K V} (s : Set ι)
    {x : Projectivization K V} :
    x.rep ∈ Submodule.span K ((Projectivization.rep ∘ f) '' s) ↔ x ∈ span (f '' s) := by
  rw [image_comp, ← Subspace.mem_span_iff_rep]

lemma Projectivization.Subspace.mem_span_image_iff (K : Type*) {V ι : Type*} [Field K]
    [AddCommGroup V] [Module K V] {f : ι → V} {hf : ∀ i, f i ≠ 0} (s : Set ι)
    {x : Projectivization K V} :
    x ∈ Projectivization.Subspace.span ((fun i ↦ Projectivization.mk K (f i) (hf i)) '' s) ↔
      x.rep ∈ Submodule.span K (f '' s) := by
  simp_rw [← Subspace.rep_mem_span_image_iff, comp_apply]
  convert Iff.rfl using 2
  simp only [le_antisymm_iff, Submodule.span_le, subset_def, mem_image, SetLike.mem_coe,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Submodule.mk_rep_mem_iff_mem]
  refine ⟨fun a has ↦ ?_, fun a has ↦ ?_⟩
  · have hmem : f a ∈ Submodule.span K {(Projectivization.mk K (f a) (hf a)).rep} := by
      rw [← submodule_eq, submodule_mk]
      exact Submodule.mem_span_singleton_self (f a)
    refine mem_of_mem_of_subset hmem (Submodule.span_mono ?_)
    simp only [singleton_subset_iff, mem_image]
    exact ⟨a, has, rfl⟩
  exact mem_of_mem_of_subset (mem_image_of_mem f has) Submodule.subset_span

/-- The projective subspace corresponding to a given submodule -/
def Submodule.toProjSubspace (W : Submodule K V) : Projectivization.Subspace K V where
  carrier := Projectivization.rep ⁻¹' W
  mem_add' := by
    intro v w hv hw hvw hv' hw'
    simp only [mem_preimage, SetLike.mem_coe, Submodule.mk_rep_mem_iff_mem] at hv' hw' ⊢
    exact Submodule.add_mem _ hv' hw'

@[simp]
lemma Submodule.mem_toProjSubspace_iff (W : Submodule K V) (x : Projectivization K V) :
    x ∈ W.toProjSubspace ↔ x.rep ∈ W := Iff.rfl

lemma Submodule.toProjSubspace_span_image_eq (K : Type*) {V ι : Type*} [Field K] [AddCommGroup V]
    [Module K V] {f : ι → V} {hf : ∀ i, f i ≠ 0} (s : Set ι) :
    (Submodule.span K (f '' s)).toProjSubspace =
    Subspace.span ((fun i ↦ Projectivization.mk K (f i) (hf i)) '' s) := by
  ext x
  exact (Subspace.mem_span_image_iff ..).symm

def Projectivization.Subspace.toSubmodule (W : Subspace K V) :=
  Submodule.span K (Projectivization.rep '' (W : Set (Projectivization K V)))

/-- The submodule corresponding to a given projective subspace -/
lemma Projectivization.Subspace.toSubmodule_coeSet_eq (W : Subspace K V) :
   (W.toSubmodule : Set V) = insert 0 (⋃ x ∈ W, Projectivization.submodule x) := by
  ext v
  obtain (rfl | hne) := eq_or_ne v 0
  · simp
  simp only [Subspace.toSubmodule, SetLike.mem_coe, Subspace.mem_span_image_rep_iff _ _ hne,
    Subspace.span_coe, mem_insert_iff, hne, mem_iUnion, exists_prop, false_or]
  exact ⟨fun h ↦ ⟨_, h,by simp [Submodule.mem_span_singleton_self]⟩,
    fun ⟨e, heW, hve⟩ ↦ by rwa [(mem_submodule_iff _ hne).1 hve] ⟩

lemma Projectivization.Subspace.mem_toSubmodule_iff (W : Subspace K V) (x : V) :
    x ∈ W.toSubmodule ↔ x = 0 ∨ ∃ hx : x ≠ 0, Projectivization.mk K x hx ∈ W := by
  obtain rfl | hne := eq_or_ne x 0
  · simp
  rw [← SetLike.mem_coe, toSubmodule_coeSet_eq]
  simp [mem_submodule_iff _ hne, hne]

lemma Projectivization.Subspace.toSubmodule_eq_span (W : Subspace K V) : W.toSubmodule
    = Submodule.span K (Projectivization.rep '' (W : Set (Projectivization K V))) := by
  ext x
  obtain rfl | hne := eq_or_ne x 0
  · simp
  simp [hne, mem_span_image_rep_iff _ _ hne, Subspace.mem_toSubmodule_iff]

@[simp]
lemma Submodule.toProjSubspace_toSubmodule (W : Submodule K V) :
    W.toProjSubspace.toSubmodule = W := by
  ext e
  by_cases he : e = 0 <;>
  simp [Subspace.mem_toSubmodule_iff, he]

@[simp]
lemma Projectivization.toSubmodule_toProjSubspace (W : Subspace K V) :
    W.toSubmodule.toProjSubspace = W := by
  ext
  simp [Subspace.mem_toSubmodule_iff, rep_nonzero]

/-- The natural isomorphism between the projective subspace lattice and the subspace lattice. -/
@[simps]
def Projectivization.subspace_orderIso_submodule (K V : Type*) [Field K] [AddCommGroup V]
    [Module K V] : (Subspace K V) ≃o (Submodule K V) where
  toFun := Subspace.toSubmodule
  invFun := Submodule.toProjSubspace
  left_inv := toSubmodule_toProjSubspace
  right_inv := Submodule.toProjSubspace_toSubmodule
  map_rel_iff' := by
    intro X₁ X₂
    simp only [Equiv.coe_fn_mk, SetLike.le_def, Subspace.mem_toSubmodule_iff, ne_eq, true_and,
      forall_eq_or_imp, not_true_eq_false, IsEmpty.exists_iff, or_false, forall_exists_index]
    exact ⟨fun h x hx₁ ↦ by simpa [x.rep_nonzero, hx₁] using h x.rep,
      fun h v hv hvX₁ ↦ .inr ⟨hv, h hvX₁⟩⟩

@[simp]
lemma Submodule.toProjSubspace_top_eq (K V : Type*) [Field K] [AddCommGroup V] [Module K V] :
    Submodule.toProjSubspace (⊤ : Submodule K V) = ⊤ := by
  simp [← subspace_orderIso_submodule_symm_apply]

@[simp]
lemma Projectivization.Subspace.toSubmodule_top_eq (K V : Type*) [Field K] [AddCommGroup V]
    [Module K V] : toSubmodule (⊤ : Projectivization.Subspace K V) = ⊤ := by
  simp [← subspace_orderIso_submodule_apply]

@[simp] lemma Submodule.toProjSubspace_eq_top_iff {W : Submodule K V} :
    W.toProjSubspace = ⊤ ↔ W = ⊤ := by
  rw [ ← subspace_orderIso_submodule_symm_apply, map_eq_top_iff]

@[simp] lemma Projectization.Subspace.toSubmodule_eq_top_iff {W : Projectivization.Subspace K V} :
    W.toSubmodule = ⊤ ↔ W = ⊤ := by
  rw [ ← subspace_orderIso_submodule_apply, map_eq_top_iff]

@[simp]
lemma Submodule.toProjSubspace_bot_eq (K V : Type*) [Field K] [AddCommGroup V] [Module K V] :
    Submodule.toProjSubspace (⊥ : Submodule K V) = ⊥ := by
  simp [← subspace_orderIso_submodule_symm_apply]

@[simp]
lemma Projectivization.Subspace.toSubmodule_bot_eq (K V : Type*) [Field K] [AddCommGroup V]
    [Module K V] : toSubmodule (⊥ : Projectivization.Subspace K V) = ⊥ := by
  simp [← subspace_orderIso_submodule_apply]

@[simp] lemma Submodule.toProjSubspace_eq_bot_iff {W : Submodule K V} :
    W.toProjSubspace = ⊥ ↔ W = ⊥ := by
  rw [ ← subspace_orderIso_submodule_symm_apply, map_eq_bot_iff]

@[simp] lemma Projectization.Subspace.toSubmodule_eq_bot_iff {W : Projectivization.Subspace K V} :
    W.toSubmodule = ⊥ ↔ W = ⊥ := by
  rw [ ← subspace_orderIso_submodule_apply, map_eq_bot_iff]

lemma Submodule.span_toProjSubspace (K : Type*) {V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (s : Set V) : (Submodule.span K s).toProjSubspace =
      Subspace.span (range (fun x : ↥(s \ {0}) ↦ Projectivization.mk K x.1 x.2.2)) := by
  ext e
  simp only [Subspace.mem_carrier_iff, mem_toProjSubspace_iff, Subspace.mem_span_iff_rep]
  convert Iff.rfl using 2
  simp only [le_antisymm_iff, Submodule.span_le, subset_def, mem_image, mem_range, Subtype.exists,
    mem_diff, mem_singleton_iff, SetLike.mem_coe, forall_exists_index, and_imp]
  constructor
  · rintro x e y ⟨hys, hy0⟩ rfl rfl
    simp only [Submodule.mk_rep_mem_iff_mem]
    exact Submodule.subset_span hys
  intro x hxs
  obtain rfl | hne := eq_or_ne x 0
  · simp
  simp_rw [Subspace.mem_span_image_rep_iff _ _ hne]
  exact Subspace.subset_span _ <| mem_range.2 ⟨⟨x, hxs, hne⟩, rfl⟩

lemma Projectivization.Subspace.span_toSubmodule {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] (s : Set (Projectivization K V)) :
    (span s).toSubmodule = Submodule.span K (Projectivization.rep '' s) := by
  refine (Submodule.span_eq_of_le _ ?_ ?_).symm
  · suffices ∀ a ∈ s, a ∈ span s by simpa [Subspace.mem_toSubmodule_iff, subset_def, rep_nonzero]
    exact fun a has ↦ subset_span _ has
  simp only [SetLike.le_def, mem_toSubmodule_iff, ne_eq, forall_eq_or_imp, Submodule.zero_mem,
    forall_exists_index, true_and]
  intro a ha hasp
  rwa [mem_span_image_rep_iff _ _ ha]
