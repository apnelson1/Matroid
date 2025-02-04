import Mathlib.LinearAlgebra.Projectivization.Independence
import Matroid.ForMathlib.LinearAlgebra.LinearIndependent

variable {ι K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    {f : ι → Projectivization K V}

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
