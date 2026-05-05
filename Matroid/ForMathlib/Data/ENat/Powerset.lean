import Mathlib.Data.ENat.Pow
import Mathlib.RingTheory.Binomial
import Mathlib.Data.Set.PowersetCard
import Mathlib.Data.Set.Card
import Matroid.ForMathlib.ENat

variable {n k a b r : ℕ∞} {α : Type*}

open ENat Set

namespace ENat

/-- The binomial coefficient for `ℕ∞`, satisfying `⊤ choose (r + 1) = ⊤`,
`n choose 0 = 1` for all `n`, `n choose r = 0` for all `n < r`,
and `(↑n) choose (↑r) = ↑(n choose r)` for all `r n : ℕ`.
Note that `⊤ choose ⊤ = ⊤`, so the identify `n choose n = 1` only holds for finite `n`. -/
def choose (n r : ℕ∞) : ℕ∞ :=
  match n, r with
  | ⊤, some 0 => 1
  | ⊤, some (_ + 1) => ⊤
  | ⊤, ⊤ => ⊤
  | some _, ⊤ => 0
  | some n, some r => Nat.choose n r

@[simp]
lemma top_choose_add_one (n : ℕ∞) : (⊤ : ℕ∞).choose (n + 1) = ⊤ := by
  cases n with rfl

@[simp]
lemma choose_zero_right (n : ℕ∞) : n.choose 0 = 1 := by
  cases n with
  | top => rfl
  | coe a => rw [← ENat.coe_zero]; simp [choose]

@[simp]
lemma choose_coe_coe (n r : ℕ) : (n : ℕ∞).choose r = n.choose r := rfl

@[simp]
lemma choose_top_top : (⊤ : ℕ∞).choose ⊤ = ⊤ := rfl

@[simp]
lemma choose_coe_top (n : ℕ) : (n : ℕ∞).choose ⊤ = 0 := rfl

lemma choose_top_right_of_ne (hn : n ≠ ⊤) : n.choose ⊤ = 0 := by
  lift n to ℕ using hn; simp

@[simp]
lemma choose_zero_top : (0 : ℕ∞).choose ⊤ = 0 := rfl

@[simp]
lemma choose_top_succ (n : ℕ) : (⊤ : ℕ∞).choose (n + 1) = ⊤ := rfl

lemma choose_succ_succ (n r : ℕ∞) : (n + 1).choose (r + 1) = n.choose r + n.choose (r + 1) := by
  cases n with
  | top => simp
  | coe n =>
    cases r with
    | top => simp_rw [← Nat.cast_add_one, top_add, choose_coe_top, zero_add]
    | coe r => simp_rw [← Nat.cast_add_one, choose_coe_coe, Nat.choose_succ_succ', Nat.cast_add]

lemma choose_eq_zero_of_lt (hrn : n < r) : n.choose r = 0 := by
  induction n using ENat.nat_induction' generalizing r with
  | zero =>
    cases r with
    | top => simp
    | coe r =>
      simp only [Nat.cast_pos] at hrn
      rwa [← ENat.coe_zero, ENat.choose_coe_coe, Nat.choose_eq_zero_of_lt]
  | succ n hn ih =>
    obtain rfl | ⟨r, rfl⟩ := r.eq_zero_or_exists_eq_add_one
    · simp at hrn
    rw [choose_succ_succ, ih (by simpa using hrn), ih, zero_add]
    grw [le_self_add (a := n) (b := 1)]
    exact hrn
  | top => simp at hrn

lemma choose_self (n : ℕ∞) (hn : n ≠ ⊤) : n.choose n = 1 := by
  lift n to ℕ using hn; simp

lemma choose_self_coe (n : ℕ) : (n : ℕ∞).choose n = 1 := by
  simp

@[simp]
lemma choose_zero_add_one (n) : choose 0 (n + 1) = 0 :=
  choose_eq_zero_of_lt (by simp)

@[simp]
lemma choose_one_right (n : ℕ∞) : n.choose 1 = n := by
  induction n with
  | top => exact choose_top_succ 0
  | coe n =>
    rw [← Nat.cast_one, choose_coe_coe, Nat.choose_one_right]

@[gcongr]
lemma choose_mono_left {m n : ℕ∞} (hmn : m ≤ n) (k : ℕ∞) : m.choose k ≤ n.choose k := by
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one; simp
  obtain ⟨d, rfl⟩ := exists_add_of_le hmn
  clear hmn
  induction d using ENat.nat_induction' with
  | zero => simp
  | succ d hd ih =>
    grw [← add_assoc, choose_succ_succ, ih]
    exact self_le_add_left ..
  | top => simp

end ENat

namespace Set

variable {s t : Set α} {k : ℕ∞} {x : α}

/-- The collection of subsets of `s` whose `encard` is equal to `k`. -/
def powersetENcard (s : Set α) (k : ℕ∞) : Set (Set α) := {x ⊆ s | x.encard = k}

@[simp]
lemma mem_powersetENcard_iff {x : Set α} : x ∈ s.powersetENcard k ↔ x ⊆ s ∧ x.encard = k := Iff.rfl

lemma powersetENcard_mono (hst : s ⊆ t) : powersetENcard s k ⊆ powersetENcard t k := by
  grind [powersetENcard]

lemma powersetENcard_of_gt (hst : s.encard < k) : powersetENcard s k = ∅ :=
  eq_empty_of_forall_notMem fun t ⟨hts, ht⟩ ↦ hst.not_ge <| by grw [← ht, hts]

lemma powersetENcard_subset_powerset (s : Set α) (k : ℕ∞) : s.powersetENcard k ⊆ s.powerset := by
  grind [powersetENcard]

@[simp]
lemma powersetENcard_zero (s : Set α) : s.powersetENcard 0 = {∅} := by
  grind [powersetENcard, encard_eq_zero]

lemma powersetENcard_succ_insert (hxs : x ∉ s) (k : ℕ∞) : (insert x s).powersetENcard (k + 1) =
      s.powersetENcard (k + 1) ∪ insert x '' (s.powersetENcard k) := by
  refine subset_antisymm ?_ (union_subset (powersetENcard_mono (subset_insert ..)) ?_)
  · refine fun t ⟨hts, ht⟩ ↦ ?_
    by_cases hxt : x ∈ t
    · refine .inr <| (mem_image ..).2 ⟨t \ {x}, ⟨by grind, ?_⟩, by grind⟩
      rw [← ENat.add_one_inj, ← ht, encard_diff_singleton_add_one hxt]
    exact .inl ⟨by grind, ht⟩
  rintro _ ⟨t, ⟨ht, ht'⟩, rfl⟩
  exact ⟨insert_subset_insert ht, by rw [encard_insert_of_notMem (by grind), ht']⟩

lemma powersetENcard_insert_disjoint (hxs : x ∉ s) {j k : ℕ∞} :
    Disjoint (s.powersetENcard j) (insert x '' (s.powersetENcard k)) := by
  grw [powersetENcard_subset_powerset, powersetENcard_subset_powerset]
  grind

lemma Infinite.powersetENcard_infinite (hs : s.Infinite) {k : ℕ∞} (hk : k ≠ 0) :
    (s.powersetENcard k).Infinite := by
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one; simp at hk
  rw [← encard_eq_top_iff, eq_top_iff_forall_ge]
  intro m
  induction m generalizing s k with
  | zero => simp
  | succ m ih =>
    obtain ⟨x, hx⟩ := hs.nonempty
    grw [← insert_diff_self_of_mem hx, powersetENcard_succ_insert (by simp),
      encard_union_eq (powersetENcard_insert_disjoint (by simp)), ← ih (hs.diff (by simp)) _ hk,
      ← one_le_encard_iff_nonempty.2, Nat.cast_add_one]
    exact image_nonempty.2 <| (s \ {x}).exists_subset_encard_eq (k := k) (by simp [hs.diff])

@[simp]
lemma encard_powersetENcard_eq (s : Set α) (k : ℕ∞) :
    (powersetENcard s k).encard = ENat.choose s.encard k := by
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one
  · simp
  obtain hs | hs := s.finite_or_infinite.symm
  · simpa [hs.encard_eq] using hs.powersetENcard_infinite (by simp)
  induction s, hs using Finite.induction_on generalizing k with
  | empty => simp [powersetENcard_of_gt]
  | @insert a s has hs ih =>
    rw [powersetENcard_succ_insert has, encard_union_eq (powersetENcard_insert_disjoint has),
      ih, InjOn.encard_image, encard_insert_of_notMem has, choose_succ_succ, add_comm]
    · obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one
      · simp
      rw [ih]
    exact (powerset_insert_injOn has).mono <| powersetENcard_subset_powerset ..

lemma sUnion_powersetENcard_eq (s : Set α) (hk : k ≠ 0) (hks : k ≤ s.encard) :
    ⋃₀ (s.powersetENcard k) = s := by
  refine subset_antisymm (sUnion_subset (by grind [powersetENcard])) fun x hxs ↦ ?_
  obtain ⟨r, hxr, hrs, rfl⟩ := exists_superset_subset_encard_eq (s := {x}) (t := s) (by simpa)
    (by simpa [ENat.one_le_iff_ne_zero]) hks
  exact mem_sUnion.2 ⟨r, ⟨hrs, rfl⟩, by simpa using hxr⟩
