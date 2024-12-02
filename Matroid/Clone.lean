import Matroid.Equiv

namespace Matroid

open Set Equiv

variable {α : Type*} {M : Matroid α} {x y z : α}

def Clonal (M : Matroid α) (x y : α) :=
  ∃ f : α ≃ α, M = M.mapEquiv f ∧ f x = y ∧ f y = x ∧ ∀ ⦃z⦄, z ≠ x → z ≠ y → f z = z

lemma Clonal.eq_mapEquiv_swap [DecidableEq α] (h : M.Clonal x y) : M = M.mapEquiv (swap x y) := by
  obtain ⟨f, hfM, hfx, hfy, hf⟩ := h
  suffices h : f = swap x y by rwa [← h]
  ext z
  obtain (rfl | hzx) := eq_or_ne z x; simpa
  obtain (rfl | hzy) := eq_or_ne z y; simpa
  rw [hf hzx hzy, swap_apply_of_ne_of_ne hzx hzy]

lemma clonal_iff_eq_mapEquiv_swap [DecidableEq α] : M.Clonal x y ↔ M = M.mapEquiv (swap x y) :=
  ⟨Clonal.eq_mapEquiv_swap,
    fun h ↦ ⟨_, h, by simp, by simp, fun z h h' ↦ swap_apply_of_ne_of_ne h h'⟩⟩

lemma Clonal.refl : M.Clonal x x :=
  ⟨Equiv.refl α, by simp [ext_iff_indep]⟩

lemma Clonal.symm (h : M.Clonal x y) : M.Clonal y x := by
  obtain ⟨f, hfM, hfx, hfy, hf⟩ := h; exact ⟨f, hfM, hfy, hfx, by tauto⟩

-- lemma Clonal.trans (hxy : M.Clonal x y) (hyz : M.Clonal y z) : M.Clonal x z := by
--   obtain (rfl | hxyne) := eq_or_ne x y; assumption
--   obtain (rfl | hyzne) := eq_or_ne y z; assumption
--   obtain (rfl | hxzne) := eq_or_ne x z; exact Clonal.refl
--   obtain ⟨f, hfM, hfx, hfy, hf⟩ := hxy
--   obtain ⟨g, hgM, hgy, hgz, hg⟩ := hyz
--   refine ⟨(f.trans g).trans f, ?_⟩
--   simp [ext_iff_indep, hfM.symm, show f z = z from hf hxzne.symm hyzne.symm, hfx,
--     hgy, hgz, hfy]
--   simp only [mapEquiv_trans, hfM.symm, hgM.symm, trans_apply, hfx, hgy,
--     show f z = z from hf hxzne.symm hyzne.symm, hgz, hfy, ne_eq, true_and]
--   refine fun a hax haz ↦ ?_
--   obtain (rfl | hay) := eq_or_ne a y
--   · rw [hfy, hg hxyne hxzne, hfx]
--   rw [hf hax hay, hg hay haz, hf hax hay]

-- lemma foo (f : α ≃ α) (h : ∀ x, M.Clonal x (f x)) : M = M.mapEquiv f := by
