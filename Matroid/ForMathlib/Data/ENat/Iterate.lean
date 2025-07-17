import Matroid.ForMathlib.ENat
import Mathlib.Data.ENat.Lattice

namespace ENat

variable {α : Type*}


/--  Given a function from `f : α → α` and a proposition `P : α → Prop`,
the minimum number of iterations of `f` required to make `a : α` satisfy `P`,
or `⊤` if no number suffices. -/
noncomputable def iterateDepth (f : α → α) (P : α → Prop) (a : α) : ℕ∞ :=
  sInf ((↑) '' {i | P (f^[i] a)})

@[simp]
lemma iterateDepth_eq_zero {f : α → α} {P : α → Prop} {a : α} : iterateDepth f P a = 0 ↔ P a := by
  simp [iterateDepth, sInf_eq_zero]

lemma iterateDepth_apply_add_one (f : α → α) {P : α → Prop} {a : α} (ha : ¬ P a) :
    ENat.iterateDepth f P (f a) + 1 = ENat.iterateDepth f P a := by
  simp only [iterateDepth, le_antisymm_iff, le_sInf_iff, Set.mem_image, Set.mem_setOf_eq,
    forall_exists_index, and_imp]
  refine ⟨fun m n hP hnm hmn ↦ ?_, ?_⟩
  · grw [← hnm]
    cases n with
    | zero => simp [ha] at hP
    | succ n =>
    · simp only [Nat.cast_add, Nat.cast_one, add_one_le_add_one_iff]
      exact sInf_le <| by simpa using hP
  obtain he | hne := {i | P (f^[i] (f a))}.eq_empty_or_nonempty
  · simp [he]
  generalize hk : sInf ((↑) '' {i : ℕ | P (f^[i] (f a))} : Set ℕ∞) = k
  obtain ⟨k, hPk, rfl⟩ : ∃ x, P (f^[x] (f a)) ∧ ↑x = k :=
    by simpa [hk] using csInf_mem (hne.image ((↑) : ℕ → ℕ∞))
  refine sInf_le ⟨k+1, by simpa, by simp⟩

lemma iterateDepth_apply_le (f : α → α) {P : α → Prop} {a : α} (ha : ¬ P a) :
    iterateDepth f P (f a) ≤ iterateDepth f P a := by
  simp [← iterateDepth_apply_add_one f ha]

/-- If `d : α → ℕ∞` is a 'weight' function that drops by one whenever `f` is applied to an element
of nonzero weight, then `d` is equal to the `depth` for the property that `d = 0`. -/
lemma iterateDepth_eq_self_of_forall_apply_eq_add_one {f : α → α} (d : α → ℕ∞)
    (hdf : ∀ a, d a ≠ 0 → d a = d (f a) + 1) {a : α} :
    ENat.iterateDepth f (fun a ↦ d a = 0) a = d a := by
  refine le_antisymm ?_ (le_sInf ?_)
  · generalize hk : d a = k
    cases k with
    | top => simp
    | coe k =>
    · suffices d (f^[k] a) = 0 from sInf_le <| by simpa
      induction k generalizing a with
      | zero => simpa using hk
      | succ n IH =>
      · apply IH
        rwa [hdf _ (by simp [hk]), Nat.cast_add, Nat.cast_one,
          WithTop.add_right_inj (by simp)] at hk
  suffices ∀ k, d (f^[k] a) = 0 → d a ≤ k by simpa
  intro k hk
  induction k generalizing a with
  | zero => simpa using hk
  | succ n IH =>
  · simp at hk
    obtain h0 | hne := eq_or_ne (d a) 0
    · simp [h0]
    grw [hdf _ hne, IH hk, Nat.cast_add, Nat.cast_one]
