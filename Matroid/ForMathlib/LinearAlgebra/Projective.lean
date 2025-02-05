import Mathlib.LinearAlgebra.Projectivization.Independence
import Mathlib.LinearAlgebra.Projectivization.Subspace
import Matroid.ForMathlib.LinearAlgebra.LinearIndependent
import Matroid.ForMathlib.LinearAlgebra.Submodule

variable {ι K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]

open Set Function Projectivization

namespace Projectivization

lemma linearIndependent_iff (f : ι → V) (hf0 : ∀ i, f i ≠ 0) :
    LinearIndependent K f ↔ Independent (fun i ↦ mk K (f i) (hf0 i)) := by
  rw [independent_iff]
  choose c hc using fun i ↦ exists_smul_eq_mk_rep K (f i) (hf0 i)
  convert LinearIndependent.units_smul_iff (w := fun i ↦ (c i)⁻¹)
  ext i
  simp [← hc]

@[simp]
theorem independent_subsingleton [Subsingleton ι] (f : ι → Projectivization K V) :
    Independent f := by
  simp [independent_iff, rep_nonzero]

lemma independent_equiv {ι' : Type*} (e : ι ≃ ι') {f : ι' → Projectivization K V} :
    Independent (f ∘ e) ↔ Independent f := by
  rw [independent_iff (f := f), ← linearIndependent_equiv e, independent_iff, comp_assoc]

@[simp]
lemma mk_smul_eq {u : V} (hu : u ≠ 0) (c : Kˣ) :
    mk K (c • u) (by rwa [smul_ne_zero_iff_ne]) = Projectivization.mk K u hu :=
  (mk_eq_mk_iff ..).2 ⟨c, rfl⟩

lemma mk_smul_eq' {u : V} (hu : u ≠ 0) {c : K} (hc : c ≠ 0) :
    mk K (c • u) (by simp [hc, hu]) = Projectivization.mk K u hu :=
  (mk_eq_mk_iff' ..).2 ⟨c, rfl⟩

lemma exists_smul_mk_rep_eq (K : Type*) {V : Type*} [DivisionRing K] [AddCommGroup V]
    [Module K V] (v : V) (hv : v ≠ 0) : ∃ c : Kˣ, c • (mk K v hv).rep = v := by
  obtain ⟨c, hc⟩ := exists_smul_eq_mk_rep K v hv
  exact ⟨c⁻¹, by simp [← hc]⟩

lemma mem_submodule_iff (K : Type*) {V : Type*} [DivisionRing K] [AddCommGroup V]
    [Module K V] {v : V} {w : Projectivization K V} (hv : v ≠ 0) :
    v ∈ w.submodule ↔ mk K v hv = w := by
  obtain ⟨a, ha⟩ := exists_smul_eq_mk_rep K v hv
  rw [w.submodule_eq, Submodule.mem_span_singleton₀ hv, ← mk_eq_mk_iff _ _ _ hv w.rep_nonzero,
    mk_rep]

@[simp]
lemma _root_.Submodule.mk_rep_mem_iff_mem (K : Type*) {V : Type*} [DivisionRing K] [AddCommGroup V]
    [Module K V] {W : Submodule K V} {v : V} (hv : v ≠ 0) :
    (mk K v hv).rep ∈ W ↔ v ∈ W := by
   obtain ⟨c, hc⟩ := exists_smul_eq_mk_rep K v hv
   rw [← hc, Submodule.smul_mem_iff']

@[simp]
lemma independent_pair {u v : Projectivization K V} :
    Independent (fun x : ({u,v} : Set _) ↦ x.1) := by
  rw [independent_iff]
  obtain rfl | hne := eq_or_ne u v
  · simp [u.rep_nonzero]
  refine (linearIndependent_restrict_pair_iff (V := V) (K := K) (fun x ↦ x.rep) hne
    (rep_nonzero u)).2 fun c hc ↦ hne ?_
  have hc0 : c ≠ 0 := by rintro rfl; simpa [v.rep_nonzero] using hc.symm
  simpa [← hc, mk_smul_eq' u.rep_nonzero hc0] using v.mk_rep

@[simp] lemma submodule_span_range_rep (𝔽 W : Type*) [DivisionRing 𝔽] [AddCommGroup W]
    [Module 𝔽 W] : Submodule.span 𝔽 (range (Projectivization.rep (K := 𝔽) (V := W))) = ⊤ := by
  have b := Basis.ofVectorSpace 𝔽 W
  ext x
  simp only [Submodule.mem_top, iff_true]
  refine mem_of_mem_of_subset (b.mem_span x) (Submodule.span_le.2 ?_)
  rintro _ ⟨i, rfl⟩
  have hi0 := b.ne_zero i
  have hmem : b i ∈ Submodule.span 𝔽 {(mk (K := 𝔽) (V := W) (b i) hi0).rep} := by
    rw [Submodule.mem_span_singleton₀ (b.ne_zero i), ← mk_eq_mk_iff _ _ _ hi0]
    · simp only [mk_rep]
    exact rep_nonzero (mk 𝔽 (b i) hi0)
  exact mem_of_mem_of_subset hmem <| Submodule.span_mono <| by simp


variable {ι K V : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma Subspace.mem_span_iff_rep (K : Type*) {V : Type*} [Field K] [AddCommGroup V]
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

lemma Subspace.mem_span_image_rep_iff (K : Type*) {V : Type*} [Field K] [AddCommGroup V]
    [Module K V] (s : Set (Projectivization K V)) {a : V} (ha : a ≠ 0) :
    a ∈ Submodule.span K (Projectivization.rep '' s) ↔ Projectivization.mk K a ha ∈ span s := by
  simp [Subspace.mem_span_iff_rep]

--x ∈ span ((fun a ↦ Projectivization.mk 𝔽 (v a) ⋯) '' X) ↔ x.rep ∈ Submodule.span 𝔽 (⇑v '' X)

lemma Subspace.rep_mem_span_image_iff (K : Type*) {V ι : Type*} [Field K] [AddCommGroup V]
    [Module K V] {f : ι → Projectivization K V} (s : Set ι) {x : Projectivization K V} :
    x.rep ∈ Submodule.span K ((Projectivization.rep ∘ f) '' s) ↔ x ∈ span (f '' s) := by
  rw [image_comp, ← Subspace.mem_span_iff_rep]

lemma Subspace.mem_span_image_iff (K : Type*) {V ι : Type*} [Field K] [AddCommGroup V]
    [Module K V] {f : ι → V} {hf : ∀ i, f i ≠ 0} (s : Set ι) {x : Projectivization K V} :
    x ∈ span ((fun i ↦ Projectivization.mk K (f i) (hf i)) '' s) ↔
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
def _root_.Submodule.toProjSubspace (W : Submodule K V) : Subspace K V where
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

def Subspace.toSubmodule (W : Subspace K V) :=
  Submodule.span K (Projectivization.rep '' (W : Set (Projectivization K V)))

/-- The submodule corresponding to a given projective subspace -/
lemma Subspace.toSubmodule_coeSet_eq (W : Subspace K V) :
   (W.toSubmodule : Set V) = insert 0 (⋃ x ∈ W, Projectivization.submodule x) := by
  ext v
  obtain (rfl | hne) := eq_or_ne v 0
  · simp
  simp only [Subspace.toSubmodule, SetLike.mem_coe, Subspace.mem_span_image_rep_iff _ _ hne,
    Subspace.span_coe, mem_insert_iff, hne, mem_iUnion, exists_prop, false_or]
  exact ⟨fun h ↦ ⟨_, h,by simp [Submodule.mem_span_singleton_self]⟩,
    fun ⟨e, heW, hve⟩ ↦ by rwa [(mem_submodule_iff _ hne).1 hve] ⟩

lemma Subspace.mem_toSubmodule_iff (W : Subspace K V) (x : V) :
    x ∈ W.toSubmodule ↔ x = 0 ∨ ∃ hx : x ≠ 0, Projectivization.mk K x hx ∈ W := by
  obtain rfl | hne := eq_or_ne x 0
  · simp
  rw [← SetLike.mem_coe, toSubmodule_coeSet_eq]
  simp [mem_submodule_iff _ hne, hne]

lemma Subspace.toSubmodule_eq_span (W : Subspace K V) : W.toSubmodule
    = Submodule.span K (Projectivization.rep '' (W : Set (Projectivization K V))) := by
  ext x
  obtain rfl | hne := eq_or_ne x 0
  · simp
  simp [hne, mem_span_image_rep_iff _ _ hne, Subspace.mem_toSubmodule_iff]

@[simp] lemma toProjSubspace_toSubmodule (W : Submodule K V) :
    W.toProjSubspace.toSubmodule = W := by
  ext e
  by_cases he : e = 0 <;>
  simp [Subspace.mem_toSubmodule_iff, he]

@[simp] lemma toSubmodule_toProjSubspace (W : Subspace K V) :
    W.toSubmodule.toProjSubspace = W := by
  ext
  simp [Subspace.mem_toSubmodule_iff, rep_nonzero]

/-- There is an order-preserving isomorphism between projective subspaces and submodules. -/
@[simps]
def Subspace.orderIso_submodule (K V : Type*) [Field K] [AddCommGroup V] [Module K V] :
    (Subspace K V) ≃o (Submodule K V) where
  toFun := Subspace.toSubmodule
  invFun := Submodule.toProjSubspace
  left_inv := toSubmodule_toProjSubspace
  right_inv := toProjSubspace_toSubmodule
  map_rel_iff' := by
    intro X₁ X₂
    simp only [Equiv.coe_fn_mk, SetLike.le_def, Subspace.mem_toSubmodule_iff, ne_eq, true_and,
      forall_eq_or_imp, not_true_eq_false, IsEmpty.exists_iff, or_false, forall_exists_index]
    exact ⟨fun h x hx₁ ↦ by simpa [x.rep_nonzero, hx₁] using h x.rep,
      fun h v hv hvX₁ ↦ .inr ⟨hv, h hvX₁⟩⟩

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

lemma Subspace.span_toSubmodule (K : Type*) {V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (s : Set (Projectivization K V)) :
    (span s).toSubmodule = Submodule.span K (Projectivization.rep '' s) := by
  refine (Submodule.span_eq_of_le _ ?_ ?_).symm
  · suffices ∀ a ∈ s, a ∈ span s by simpa [Subspace.mem_toSubmodule_iff, subset_def, rep_nonzero]
    exact fun a has ↦ subset_span _ has
  simp only [SetLike.le_def, mem_toSubmodule_iff, ne_eq, forall_eq_or_imp, Submodule.zero_mem,
    forall_exists_index, true_and]
  intro a ha hasp
  rwa [mem_span_image_rep_iff _ _ ha]
