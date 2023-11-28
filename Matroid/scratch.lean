import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Logic.Equiv.LocalEquiv

open Set SimpleGraph


section grow

variable {ι α β : Type*}

/-- given a family `xs i` of sets in `α` with union `univ`, and a family `fs i : xs i → β`
  construct a function from `α → β`.  -/
noncomputable def extend_partials {xs : ι → Set α} (h_def : ∀ a, ∃ i, a ∈ xs i)
    (fs : ∀ {i}, xs i → β) (a : α) : β := fs ⟨_, (h_def a).choose_spec⟩

/-- If the partial functions agree on every point, then `extend_partials` is well-defined. -/
theorem extend_partials_spec {xs : ι → Set α} (h_def : ∀ a, ∃ i, a ∈ xs i) (fs : ∀ {i}, xs i → β)
    (h_mono : ∀ {a : α} {i i' : ι} (ha : a ∈ xs i) (ha' : a ∈ xs i'), fs ⟨a,ha⟩ = fs ⟨a, ha'⟩)
    {i : ι} (a : α) (hai : a ∈ xs i) : extend_partials h_def fs a = fs ⟨a,hai⟩ :=
  h_mono (h_def a).choose_spec hai


theorem toSeq (β : ℕ → Type*) (P : ∀ {i}, β i → β (i+1) → Prop) (b0 : β 0)
    (h : ∀ i (b : β i), ∃ (b' : β (i+1)), P b b') :
    ∃ (bs : ∀ n, β n), ∀ i, P (bs i) (bs (i+1)) := by
  choose f hf using h
  refine ⟨fun t ↦ @Nat.recOn β t b0 f, fun i ↦ hf _ _⟩

end grow

variable {V : Type*}


def extensionProperty (G : SimpleGraph V) : Prop :=
  ∀ A B : Finset V, Disjoint A B →
    ∃ x, (A : Set V) ⊆ G.neighborSet x ∧ Disjoint (B : Set V) (G.neighborSet x)

-- structure partialIso (G H : SimpleGraph ℕ) (n : ℕ) where
--   (s : Set ℕ)
--   (t : Set ℕ)
--   (toIso : G.induce s ≃g H.induce t)
--   (hst : ∀ i, i < n → i ∈ s ∧ i ∈ t)

structure partialIso (G H : SimpleGraph ℕ) (n : ℕ) where
  (eqv : LocalEquiv ℕ ℕ)
  (h_source : ∀ {i}, i ≤ n → i ∈ eqv.source)
  (h_target : ∀ {j}, j ≤ n → j ∈ eqv.target)
  (toIso : G.induce eqv.source ≃g H.induce eqv.target)
  (h_eq : eqv.toEquiv = toIso.toEquiv)

-- def partialIso.subIso (G H : SimpleGraph ℕ) {n₁ n₂ : ℕ} (e₁ : partialIso G H n₁)
--     (e₂ : partialIso G H n₂) : Prop :=
--   ∃ (hs : e₁.s ⊆ e₂.s) (ht : e₁.t ⊆ e₂.t),
--       (∀ (i : e₁.s), (e₁.toIso i : ℕ) = e₂.toIso (inclusion hs i))
--     ∧ ∀ (j : e₁.t), (e₁.toIso.symm j : ℕ) = e₂.toIso.symm (inclusion ht j)

-- theorem partialIso.subIso.trans (G H : SimpleGraph ℕ) {n₁ n₂ n₃ : ℕ}
--     {e₁ : partialIso G H n₁} {e₂ : partialIso G H n₂} {e₃ : partialIso G H n₃}
--     (h₁₂ : e₁.subIso e₂) (h₂₃ : e₂.subIso e₃) : e₁.subIso e₃ := by
--   obtain ⟨hs₁₂, ht₁₂, hf₁₂, hg₁₂⟩ := h₁₂
--   obtain ⟨hs₂₃, ht₂₃, hf₂₃, hg₂₃⟩ := h₂₃
--   exact ⟨hs₁₂.trans hs₂₃, ht₁₂.trans ht₂₃,
--     fun i ↦ by rw [hf₁₂, hf₂₃]; rfl, fun j ↦ by rw [hg₁₂, hg₂₃]; rfl⟩

theorem foo_aux {G H : SimpleGraph ℕ} (hG : extensionProperty G) (hH : extensionProperty H) (n : ℕ)
  (e : partialIso G H n) : ∃ (e' : partialIso G H (n+1)), e.eqv = e'.eqv.restr e.eqv.source := sorry

theorem foo (G H : SimpleGraph ℕ) (hG : extensionProperty G) (hH : extensionProperty H) :
    Nonempty (G ≃g H) := by
  set e0 : partialIso G H 0 := sorry
  -- ⟨∅, ∅, ⟨Equiv.refl _, by simp⟩, by simp⟩
  obtain ⟨bs, hbs⟩ := toSeq (partialIso G H) (fun {i} e e' ↦ e.eqv = e'.eqv.restr e.eqv.source)
    e0 (foo_aux hG hH)
  set f := fun i ↦ (bs i).eqv i with hf_def
  set g := fun i ↦ (bs i).eqv.symm i

  have hf : ∀ {i j} (hij : i ≤ j), f i = (bs j).eqv i := by
    intro i j hij
    obtain ⟨d, rfl⟩ := exists_add_of_le hij
    induction' d with d IH
    · simp
    rw [IH (by simp), hbs, Nat.succ_eq_add_one, ← add_assoc]

  have hf' : ∀ i, f ((bs i).eqv.symm i) = i
  · intro i
    simp only

    convert (bs i).eqv.right_inv ((bs i).h_target rfl.le) using 1
    rw [hf]
    simp only

  -- have hg : ∀ {i j} (hij : i ≤ j), g i = (bs j).eqv.symm i := by
  --   set k := max i ( )
    -- intro i j hij
    -- obtain ⟨d, rfl⟩ := exists_add_of_le hij
    -- induction' d with d IH
    -- · simp
    -- rw [IH (by simp), hbs, Nat.succ_eq_add_one, ← add_assoc]

  have hf_inj : f.Injective
  · intro i j hij
    apply (bs (max i j)).eqv.injOn ((bs (max i j)).h_source (le_max_left i j))
       ((bs (max i j)).h_source (le_max_right i j))
    rwa [← hf (le_max_left i j), ← hf (le_max_right i j)]
  have hf_surj : f.Surjective
  · intro j
    set k := max j ((bs j).eqv.symm j)
    use (bs k).eqv.symm j

    -- rw [← (bs k).eqv.right_inv (x := j) ((bs k).h_target (le_max_left _ _)), ← hf']


    rw [hf (show _ ≤k from _ ), (bs k).eqv.right_inv ((bs k).h_target (le_max_left _ _))]


    -- sorry
    convert le_max_right _ _ using 2


    apply (bs k).eqv.injOn ((bs k).h_source ?_) ((bs k).h_source ?_)
    · rw [← hf (le_max_right _ _), (bs k).eqv.right_inv ((bs k).h_target (le_max_left _ _))]
      simp only

    -- · rw [LocalEquiv.right_inv]

    -- use (bs j).eqv.symm j
    -- rw [hf' (le_max_right j ((bs j).eqv.symm j))]



    -- simp only
    -- have := (bs j).h_target j rfl.le

  sorry

  -- have hg : ∀ {i j x}, i ≤ j → x ∈ (bs i).eqv.target → (bs i).eqv.symm x = (bs j).eqv.symm x
  -- · intro i j x hij
  --   obtain ⟨d, rfl⟩ := exists_add_of_le hij
  --   induction' d with d IH
  --   · simp
  --   intro hx
  --   rw [Nat.succ_eq_add_one, ← add_assoc, IH (Nat.le_add_right i d) hx, hbs]
  --   rfl
  -- set en : ℕ ≃ ℕ := {
  --   toFun := f
  --   invFun := g
  --   left_inv := by
  --     intro x

  --   right_inv := _
  -- }





  -- set en : ℕ ≃ ℕ :=
  --   { toFun := fun i ↦ (bs (i+1)).eqv i
  --     invFun := fun i ↦ (bs (i+1)).eqv.symm i
  --     left_inv := by
  --       intro x
  --       simp
  --     right_inv := _ }

  -- set f : ℕ → ℕ := fun i ↦ (bs (i+1)).eqv i
  -- set g : ℕ → ℕ := fun i ↦ (bs (i+1)).eqv.symm i

  -- set f : ℕ → ℕ := fun i ↦ (bs (i+1)).toIso ⟨i, ((bs (i+1)).hst i (lt_add_one i)).1⟩ with hf
  -- set g : ℕ → ℕ := fun i ↦ (bs (i+1)).toIso.symm ⟨i, ((bs (i+1)).hst i (lt_add_one i)).2⟩ with hg

  -- have hf' : ∀ {i j n} (hij : i ≤ j) (hn : n ∈



--   set down_closed : (∀ n, LocalEquiv ℕ ℕ) → Prop :=
--     fun es ↦ ∀ {i a b : ℕ}, a ≤ b →
--       (i ∈ (es a).source → es b i = es a i) ∧
--       (i ∈ (es a).target → (es b).symm i = (es a).symm i)
--   set mono : (∀ n, LocalEquiv ℕ ℕ) → Prop :=
--     fun es ↦ ∀ {a b : ℕ}, a ≤ b →
--       ((es a).source ⊆ (es b).source ∧ (es a).target ⊆ (es b).target)
--   set defined_on_lt : (∀ n, LocalEquiv ℕ ℕ) → Prop :=
--     fun es ↦ ∀ {i n : ℕ}, i < n → i ∈ (es n).source ∧ i ∈ (es n).target
--   set partial_iso : LocalEquiv ℕ ℕ → Prop :=
--     fun e ↦ ∀ {i j : ℕ}, i ∈ e.source → j ∈ e.source → ((G.Adj i j) ↔ (H.Adj (e i) (e j)))

--   have lem : ∃ (es : ∀ n, LocalEquiv ℕ ℕ), down_closed es ∧ mono es ∧ defined_on_lt es
--     ∧ ∀ n, partial_iso (es n)
--   ·

  -- set down_closed : (∀ n, ℕ → Option ℕ) → Prop :=
  --   fun fs ↦ ∀ {i j : ℕ} a, i ≤ j → fs i a ≠ none → fs j a = fs i a
  -- set defined_on_lt : (∀ n, ℕ → Option ℕ) → Prop :=
  --   fun fs ↦ ∀ {i n : ℕ}, i < n → fs n i ≠ none
  -- set partial_iso : ∀ (f g : ℕ → Option ℕ), Prop :=
  --   fun f g ↦ InvOn f g {(x : ℕ) | f x ≠ none}
    -- fun f g (∀ {i j a b : ℕ}, f i ∈ a → f j ∈ b → hG.adj i j ↔ hH.adj a b)



  -- have lem := ∃ (fs gs : ∀ n, ℕ → Option ℕ), down_closed fs ∧ down_closed gs
  --   ∧ defined_on_lt fs ∧ defined_on_lt gs ∧
