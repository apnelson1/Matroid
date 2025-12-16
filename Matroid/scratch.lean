import Mathlib


/-- A wrapper for a set -/
structure SetWrap where
  val : Set ℕ

/-- The union of two wrapped sets -/
def SetWrap.union (a b : SetWrap) : SetWrap := ⟨a.val ∪ b.val⟩

/-- A reasonable simp lemma with `rfl` as the proof. -/
@[simp]
lemma SetWrap.union_val (a b : SetWrap) : (a.union b).val = a.val ∪ b.val := rfl

/-- A sequence of subsets of a set `s` -/
structure SubsetSeq (s : Set ℕ) where
  toFun : ℕ → Set ℕ
  subset : ∀ i, toFun i ⊆ s

/-- `SubsetSeq` is `FunLike` -/
instance {s : Set ℕ} : FunLike (SubsetSeq s) ℕ (Set ℕ) where
  coe := SubsetSeq.toFun
  coe_injective' := by rintro ⟨f,h⟩ ⟨f', h'⟩; simp

/-- If `f` is a subset sequence arising from a `SetWrap`, then its terms are empty. -/
@[simp]
lemma foo {a : SetWrap} (f : SubsetSeq (no_index a.val)) (i : ℕ) : (f i = ∅) := by
  sorry


/-- an easy lemma that follows directly from `foo` and should be proved by `simp`. -/
example {a b : SetWrap} {f : SubsetSeq (a.union b).val} {i : ℕ} : f i = ∅ := by
  /- The following `simp` succeeds with no visible change;
  it uses `SetWrap.union_val` to change the term `f i` from
  `@DFunLike.coe (SubsetSeq ((a.union b).val)) ℕ (fun x ↦ Set α) instFunLikeSubsetSeqNatSet f i`
  to
  `@DFunLike.coe (SubsetSeq (a.val ∪ b.val)) ℕ (fun x ↦ Set α) instFunLikeSubsetSeqNatSet f i`.
  This is not visible in the infoview without mouseover. -/
  simp -- succeeds with no visible change
  -- Now the next `simp` fails to resolve the goal using `foo`,
  -- because `f` does not match its argument.
  simp  -- fails


@[simp]
lemma foo' {a : SetWrap} (f : SubsetSeq a.val) (i : ℕ) : (f.toFun i = ∅) := by
  sorry

example {a b : SetWrap} {f : SubsetSeq (a.union b).val} {i : ℕ} : f.toFun i = ∅ := by
  simp only [SetWrap.union_val]
  simp
