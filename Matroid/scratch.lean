import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Logic.Equiv.PartialEquiv

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

-- structure partialIso (G H : SimpleGraph ℕ) (n : ℕ) where
--   (eqv : PartialEquiv ℕ ℕ)
--   (h_source : ∀ {i}, i < n → i ∈ eqv.source)
--   (h_target : ∀ {j}, j < n → j ∈ eqv.target)
--   (toIso : G.induce eqv.source ≃g H.induce eqv.target)
--   (h_eq : eqv.toEquiv = toIso.toEquiv)

def partialIso (G H : SimpleGraph ℕ) (n : ℕ) :=
  {e : PartialEquiv ℕ ℕ // Iic n ⊆ e.source ∩ e.target ∧
    ∃ (φ : G.induce e.source ≃g H.induce e.target), φ.toEquiv = e.toEquiv }

theorem partialIso.mem_source {G H : SimpleGraph ℕ} {i n : ℕ} (e : partialIso G H (n+1)) (hin : i ≤ n) :
  i ∈ e.1.source := sorry

theorem partialIso.mem_target {G H : SimpleGraph ℕ} {i n : ℕ} (e : partialIso G H (n+1)) (hin : i ≤ n) :
  i ∈ e.1.target := sorry

-- def PartialEquiv.isPartialIso (e : PartialEquiv ℕ ℕ) (G H : SimpleGraph ℕ) (n : ℕ) : Prop :=
--   (Iic n ⊆ e.source ∩ e.target) ∧
--   ∃ (φ : G.induce e.source ≃g H.induce e.target), φ.toEquiv = e.toEquiv

def foo_ind {G H : SimpleGraph ℕ} (hG : extensionProperty G) (hH : extensionProperty H) {n : ℕ}
  (e : partialIso G H n) : ∃ e' : partialIso G H (n+1),
    e.1.source ⊆ e'.1.source ∧ ∀ x ∈ e.1.source, e'.1 x = e.1 x := sorry

theorem foo {G H : SimpleGraph ℕ} (hG : extensionProperty G) (hH : extensionProperty H)
    (e0 : partialIso G H 0) :
    ∃ (e : G ≃g H), ∀ i ∈ e0.1.source, e i = e0.1 i := by
  obtain ⟨es, hes⟩ := toSeq (partialIso G H) _ e0 (fun i ↦ foo_ind hG hH)

  have h_strong : ∀ {i j : ℕ}, i ≤ j → ((es (i+1)).1.source ⊆ (es (j+1)).1.source)
    ∧ (∀ n, n ∈ (es (i+1)).1.source → (es (i+1)).1 n = (es (j+1)).1 n)
  · intro i j hij
    obtain ⟨d, rfl⟩ := exists_add_of_le hij
    induction' d with d IH generalizing i
    · simp [Subset.rfl]
    simp only [le_add_iff_nonneg_right, zero_le, forall_true_left] at IH
    simp_rw [Nat.succ_eq_add_one]
    refine ⟨(hes _).1.trans (IH.1.trans ?_), fun n hn ↦ ?_⟩
    · rw [add_comm d 1, add_assoc, add_assoc, add_assoc]
      rfl
    rw [IH.2 n hn, ← (hes _).2, add_assoc, add_assoc, add_assoc]
    exact IH.1 hn

  set f := fun i ↦ (es (i+1)).1 i with hf_def

  have hfInj : f.Injective
  · intro i j hij
    simp only [hf_def] at hij
    rw [(h_strong (le_max_left i j)).2, (h_strong (le_max_right i j)).2] at hij
    · refine' (es (max i j + 1)).1.injOn _ _ hij <;> apply partialIso.mem_source <;> simp
    all_goals
    · apply partialIso.mem_source <;> simp

  have hfSurj : f.Surjective
  · intro j
    set k := max j <| (es (j+1)).1.symm j
    use (es (k+1)).1.symm j
    rw [hf_def]
    eta



  --   n ∈ (es (i+1)).1.source → (es (i+1)).1 n = (es (j+1)).1 n
  -- · intro i j n hij hn
  --   obtain ⟨d, rfl⟩ := exists_add_of_le hij
  --   induction' d with d IH
  --   · simp
  --   rw [Nat.succ_eq_add_one, ← add_assoc, IH (by simp)]
  --   induction' d with d IH'
  --   · simpa

  -- have hf₀ : ∀ {i j}, j ∈ (es (i+1)).1.source → f j = (es (i+1)).1 j
  -- · intro i j hij
  --   induction' i with i IH
  --   · induction' j with j IHj
  --     · simp
  --     rw [Nat.succ_eq_add_one, IHj]



  -- have hf : ∀ {i j} (hij : i ≤ j), f i = (es (j+1)).1 i
  -- · intro i j hij
  --   obtain ⟨d, rfl⟩ := exists_add_of_le hij
  --   induction' d with d IH
  --   · simp
  --   rw [IH (by simp), Nat.succ_eq_add_one, ← hes, add_assoc, add_assoc, add_assoc]
  --   exact partialIso.mem_source _ <| by simp
  -- have hf' : ∀ i, f ((es (i+1)).1.symm i) = i
  -- · intro i
  --   convert (es (i+1)).1.right_inv ((es (i+1)).mem_target rfl.le) using 1








  --   (fun {i} e e' ↦ ∀ x ∈ e.1.source, e.1 x = e'.1 x) ⟨e0, he0⟩
  --   (fun i ⟨e,he⟩ ↦

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

theorem foo {G H : SimpleGraph ℕ} (hG : extensionProperty G) (hH : extensionProperty H)
  (φ0 : partialIso G H 0) : ∃ (φ : G ≃g H), ∀ i ∈ φ0.eqv.
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

    -- · rw [PartialEquiv.right_inv]

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



--   set down_closed : (∀ n, PartialEquiv ℕ ℕ) → Prop :=
--     fun es ↦ ∀ {i a b : ℕ}, a ≤ b →
--       (i ∈ (es a).source → es b i = es a i) ∧
--       (i ∈ (es a).target → (es b).symm i = (es a).symm i)
--   set mono : (∀ n, PartialEquiv ℕ ℕ) → Prop :=
--     fun es ↦ ∀ {a b : ℕ}, a ≤ b →
--       ((es a).source ⊆ (es b).source ∧ (es a).target ⊆ (es b).target)
--   set defined_on_lt : (∀ n, PartialEquiv ℕ ℕ) → Prop :=
--     fun es ↦ ∀ {i n : ℕ}, i < n → i ∈ (es n).source ∧ i ∈ (es n).target
--   set partial_iso : PartialEquiv ℕ ℕ → Prop :=
--     fun e ↦ ∀ {i j : ℕ}, i ∈ e.source → j ∈ e.source → ((G.Adj i j) ↔ (H.Adj (e i) (e j)))

--   have lem : ∃ (es : ∀ n, PartialEquiv ℕ ℕ), down_closed es ∧ mono es ∧ defined_on_lt es
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
