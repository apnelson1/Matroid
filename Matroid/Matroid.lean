import Mathlib.Data.Set.Finite
import Matroid.ForMathlib.encard_stuff
import Mathlib.Order.Minimal
import Matroid.Init

open Set 

/-- A predicate `P` on sets satisfies the exchange property if, for all `X` and `Y` satisfying `P`
  and all `a ∈ X \ Y`, there exists `b ∈ Y \ X` so that swapping `a` for `b` in `X` maintains `P`.-/
def Matroid.exchange_property {α : Type _} (P : Set α → Prop) : Prop :=
  ∀ X Y, P X → P Y → ∀ a ∈ X \ Y, ∃ b ∈ Y \ X, P (insert b (X \ {a}))

/-- A set `X` has the maximal subset property for a predicate `P` if every subset of `X` satisfying
  `P` is contained in a maximal subset of `X` satisfying `P`.  -/
def Matroid.exists_maximal_subset_property {α : Type _} (P : Set α → Prop) (X : Set α) : Prop := 
  ∀ I, P I → I ⊆ X → (maximals (· ⊆ ·) {Y | P Y ∧ I ⊆ Y ∧ Y ⊆ X}).Nonempty 

/-- A `Matroid α` is a `ground` set of type `Set α`, and a nonempty collection of its subsets 
  satisfying the exchange property and the maximal subset property. Each such set is called a 
  `base` of `M`. -/
@[ext] structure Matroid (α : Type _) where
  (ground : Set α)
  (base : Set α → Prop)
  (exists_base' : ∃ B, base B)
  (base_exchange' : Matroid.exchange_property base)
  (maximality' : ∀ X, X ⊆ ground → 
    Matroid.exists_maximal_subset_property (fun I ↦ ∃ B, base B ∧ I ⊆ B) X)
  (subset_ground' : ∀ B, base B → B ⊆ ground)
  
namespace Matroid

variable {α : Type _} {M : Matroid α} 
--{I D J B B' B₁ B₂ X Y : Set α} {e f : α}

section exchange

/-- A family of sets with the exchange property is an antichain. -/
theorem antichain_of_exch {base : Set α → Prop} (exch : exchange_property base) 
    (hB : base B) (hB' : base B') (h : B ⊆ B') : B = B' := 
  h.antisymm (fun x hx ↦ by_contra 
    (fun hxB ↦ by obtain ⟨y, hy, -⟩ := exch B' B hB' hB x ⟨hx, hxB⟩; exact hy.2 $ h hy.1))

theorem encard_diff_le_aux {base : Set α → Prop} (exch : exchange_property base) 
    {B₁ B₂ : Set α} (hB₁ : base B₁) (hB₂ : base B₂) : (B₁ \ B₂).encard ≤ (B₂ \ B₁).encard := by
  obtain (hinf | hfin₂) := (B₂ \ B₁).finite_or_infinite.symm
  · rw [hinf.encard_eq]; apply le_top
  obtain (he | ⟨e,he⟩) := (B₂ \ B₁).eq_empty_or_nonempty
  · simp [antichain_of_exch exch hB₂ hB₁ (diff_eq_empty.mp he)] 
  obtain ⟨f, hf, hB'⟩ := exch B₂ B₁ hB₂ hB₁ e he
  
  have : ncard (insert f (B₂ \ {e}) \ B₁) < ncard (B₂ \ B₁) := by 
    ( rw [insert_diff_of_mem _ hf.1, diff_diff_comm]; 
      exact ncard_diff_singleton_lt_of_mem he hfin₂)

  have hencard := encard_diff_le_aux exch hB₁ hB'
  rw [insert_diff_of_mem _ hf.1, diff_diff_comm, ←union_singleton, ←diff_diff, diff_diff_right,
    inter_singleton_eq_empty.mpr he.2, union_empty] at hencard

  rw [←encard_diff_singleton_add_one he, ←encard_diff_singleton_add_one hf]
  exact add_le_add_right hencard 1
termination_by _ => (B₂ \ B₁).ncard

/-- For any two sets `B₁,B₂` in a family with the exchange property, the differences `B₁ \ B₂` and
  `B₂ \ B₁` have the same `ℕ∞`-cardinality. -/
theorem encard_diff_eq_of_exch {base : Set α → Prop} (exch : exchange_property base)
    (hB₁ : base B₁) (hB₂ : base B₂) : (B₁ \ B₂).encard = (B₂ \ B₁).encard := 
(encard_diff_le_aux exch hB₁ hB₂).antisymm (encard_diff_le_aux exch hB₂ hB₁)

/-- Any two sets `B₁,B₂` in a family with the exchange property have the same `ℕ∞`-cardinality. -/
theorem encard_base_eq_of_exch {base : Set α → Prop} (exch : exchange_property base)
    (hB₁ : base B₁) (hB₂ : base B₂) : B₁.encard = B₂.encard := by 
rw [←encard_diff_add_encard_inter B₁ B₂, encard_diff_eq_of_exch exch hB₁ hB₂, inter_comm, 
     encard_diff_add_encard_inter]

end exchange

section defs

/-- We write `M.E` for the ground set of a matroid `M`-/
def E (M : Matroid α) : Set α := M.ground

@[simp] theorem ground_eq_E (M : Matroid α) : M.ground = M.E := rfl 

/-- A set is independent if it is contained in a base.  -/
def indep (M : Matroid α) (I : Set α) : Prop := ∃ B, M.base B ∧ I ⊆ B

/-- A subset of `M.E` is dependent if it is not independent . -/
def dep (M : Matroid α) (D : Set α) : Prop := ¬M.indep D ∧ D ⊆ M.E   

/-- A basis for a set `X ⊆ M.E` is a maximal independent subset of `X`
  (Often in the literature, the word 'basis' is used to refer to what we call a 'base'). -/
def basis (M : Matroid α) (I X : Set α) : Prop := 
  I ∈ maximals (· ⊆ ·) {A | M.indep A ∧ A ⊆ X} ∧ X ⊆ M.E  

/-- A circuit is a minimal dependent set -/
def circuit (M : Matroid α) (C : Set α) : Prop := C ∈ minimals (· ⊆ ·) {X | M.dep X}

/-- A coindependent set is a subset of `M.E` that is disjoint from some base -/
def coindep (M : Matroid α) (I : Set α) : Prop := (∃ B, M.base B ∧ Disjoint I B) ∧ I ⊆ M.E

end defs

/-- Typeclass for a matroid having finite ground set. This is just a wrapper for `[M.E.Finite]`-/
class Finite (M : Matroid α) : Prop := (ground_finite : M.E.Finite)

theorem ground_Finite (M : Matroid α) [M.Finite] : M.E.Finite := ‹M.Finite›.ground_finite   

theorem set_Finite (M : Matroid α) [M.Finite] (X : Set α) (hX : X ⊆ M.E := by aesop) : X.Finite :=
  M.ground_Finite.subset hX 

instance Finite_of_Finite [@_root_.Finite α] {M : Matroid α} : Finite M := 
  ⟨Set.toFinite _⟩ 

/-- A `Finite_rk` matroid is one with a finite basis -/
class Finite_rk (M : Matroid α) : Prop := (exists_finite_base : ∃ B, M.base B ∧ B.Finite) 

instance Finite_rk_of_finite (M : Matroid α) [Finite M] : Finite_rk M := 
  ⟨ M.exists_base'.imp (fun B hB ↦ ⟨hB, M.set_Finite B (M.subset_ground' _ hB)⟩) ⟩ 

/-- An `Infinite_rk` matroid is one whose bases are infinite. -/
class Infinite_rk (M : Matroid α) : Prop := (exists_infinite_base : ∃ B, M.base B ∧ B.Infinite)

/-- A `Finitary` matroid is one whose circuits are finite -/
class Finitary (M : Matroid α) : Prop := (cct_finite : ∀ (C : Set α), M.circuit C → C.Finite) 

/-- A `Rk_pos` matroid is one in which the empty set is not a basis -/
class Rk_pos (M : Matroid α) : Prop := (empty_not_base : ¬M.base ∅)

section aesop

macro (name := aesop_mat) "aesop_mat" c:Aesop.tactic_clause* : tactic =>
`(tactic|
  aesop $c* (options := { introsTransparency? := some .default, terminal := true })
  (rule_sets [$(Lean.mkIdent `matroid):ident]))

@[aesop unsafe (rule_sets [Matroid])] 
private theorem inter_right_subset_ground {X Y : Set α} {M : Matroid α} (hX : X ⊆ M.E) : 
    X ∩ Y ⊆ M.E := (inter_subset_left _ _).trans hX 

@[aesop unsafe (rule_sets [Matroid])]
private theorem inter_left_subset_ground {X Y : Set α} {M : Matroid α} (hX : X ⊆ M.E) :
    Y ∩ X ⊆ M.E := (inter_subset_right _ _).trans hX 

@[aesop norm (rule_sets [Matroid])]
private theorem diff_subset_ground {X Y : Set α} {M : Matroid α} (hX : X ⊆ M.E) : X \ Y ⊆ M.E :=      
  (diff_subset _ _).trans hX 

@[aesop norm (rule_sets [Matroid])]
private theorem ground_diff_subset_ground {X : Set α} {M : Matroid α} : M.E \ X ⊆ M.E :=
  diff_subset_ground rfl.subset 

@[aesop norm (rule_sets [Matroid])]
private theorem singleton_subset_ground {e : α} {M : Matroid α} (he : e ∈ M.E) : {e} ⊆ M.E := 
  singleton_subset_iff.mpr he
   
attribute [aesop norm (rule_sets [Matroid])] mem_of_mem_of_subset empty_subset union_subset

end aesop
section base

@[aesop norm (rule_sets [Matroid])]
theorem base.subset_ground (hB : M.base B) : B ⊆ M.E :=
  M.subset_ground' B hB 

theorem exists_base (M : Matroid α) : ∃ B, M.base B := M.exists_base'

theorem base.exchange (hB₁ : M.base B₁) (hB₂ : M.base B₂) (hx : e ∈ B₁ \ B₂) :
    ∃ y ∈ B₂ \ B₁, M.base (insert y (B₁ \ {e}))  :=
  M.base_exchange' B₁ B₂ hB₁ hB₂ _ hx

theorem base.exchange_mem (hB₁ : M.base B₁) (hB₂ : M.base B₂) (hxB₁ : e ∈ B₁) (hxB₂ : e ∉ B₂) :
    ∃ y, (y ∈ B₂ ∧ y ∉ B₁) ∧ M.base (insert y (B₁ \ {e})) :=
  by simpa using hB₁.exchange hB₂ ⟨hxB₁, hxB₂⟩

theorem base.eq_of_subset_base (hB₁ : M.base B₁) (hB₂ : M.base B₂) (hB₁B₂ : B₁ ⊆ B₂) :
    B₁ = B₂ :=
  antichain_of_exch M.base_exchange' hB₁ hB₂ hB₁B₂

theorem base.encard_diff_comm (hB₁ : M.base B₁) (hB₂ : M.base B₂) :
    (B₁ \ B₂).encard = (B₂ \ B₁).encard :=
  encard_diff_eq_of_exch (M.base_exchange') hB₁ hB₂ 

theorem base.card_diff_comm (hB₁ : M.base B₁) (hB₂ : M.base B₂) :
    (B₁ \ B₂).ncard = (B₂ \ B₁).ncard := by
  rw [←encard_toNat_eq, hB₁.encard_diff_comm hB₂, encard_toNat_eq]

theorem base.encard_eq_encard_of_base (hB₁ : M.base B₁) (hB₂ : M.base B₂) :
    B₁.encard = B₂.encard := by
  rw [encard_base_eq_of_exch M.base_exchange' hB₁ hB₂]

theorem base.card_eq_card_of_base (hB₁ : M.base B₁) (hB₂ : M.base B₂) : B₁.ncard = B₂.ncard := by
  rw [←encard_toNat_eq B₁, hB₁.encard_eq_encard_of_base hB₂, encard_toNat_eq]

theorem base.Finite_of_Finite (hB : M.base B) (h : B.Finite) (hB' : M.base B') : B'.Finite :=
  (Finite_iff_Finite_of_encard_eq_encard (hB.encard_eq_encard_of_base hB')).mp h  

theorem base.Infinite_of_Infinite (hB : M.base B) (h : B.Infinite) (hB₁ : M.base B₁) :
    B₁.Infinite :=
  by_contra (fun hB_inf ↦ (hB₁.Finite_of_Finite (not_infinite.mp hB_inf) hB).not_infinite h)

theorem base.Finite [Finite_rk M] (hB : M.base B) : B.Finite := 
  let ⟨B₀,hB₀⟩ := ‹Finite_rk M›.exists_finite_base
  hB₀.1.Finite_of_Finite hB₀.2 hB

theorem base.Infinite [Infinite_rk M] (hB : M.base B) : B.Infinite :=
  let ⟨B₀,hB₀⟩ := ‹Infinite_rk M›.exists_infinite_base
  hB₀.1.Infinite_of_Infinite hB₀.2 hB

theorem base.Finite_rk_of_Finite (hB : M.base B) (hfin : B.Finite) : Finite_rk M := 
  ⟨⟨B, hB, hfin⟩⟩   

theorem base.Infinite_rk_of_Infinite (hB : M.base B) (h : B.Infinite) : Infinite_rk M := 
  ⟨⟨B, hB, h⟩⟩ 

theorem not_Finite_rk (M : Matroid α) [Infinite_rk M] : ¬ Finite_rk M := by
  intro h; obtain ⟨B,hB⟩ := M.exists_base; exact hB.Infinite hB.Finite

theorem not_Infinite_rk (M : Matroid α) [Finite_rk M] : ¬ Infinite_rk M := by
  intro h; obtain ⟨B,hB⟩ := M.exists_base; exact hB.Infinite hB.Finite

theorem finite_or_Infinite_rk (M : Matroid α) : Finite_rk M ∨ Infinite_rk M :=
  let ⟨B, hB⟩ := M.exists_base
  B.finite_or_infinite.elim 
  (Or.inl ∘ hB.Finite_rk_of_Finite) (Or.inr ∘ hB.Infinite_rk_of_Infinite)

instance Finite_rk_of_Finite {M : Matroid α} [Finite M] : Finite_rk M := 
  let ⟨B, hB⟩ := M.exists_base
  ⟨⟨B, hB, (M.ground_Finite).subset hB.subset_ground⟩⟩ 

instance Finitary_of_Finite_rk {M : Matroid α} [Finite_rk M] : Finitary M := 
⟨ by
  intros C hC
  obtain (rfl | ⟨e,heC⟩) := C.eq_empty_or_nonempty; exact finite_empty
  have hi : M.indep (C \ {e}) :=
  by_contra (fun h ↦ (hC.2 ⟨h, (diff_subset _ _).trans hC.1.2⟩ (diff_subset C {e}) heC).2 rfl)
  obtain ⟨B, hB, hCB⟩ := hi 
  convert (hB.Finite.subset hCB).insert e
  rw [insert_diff_singleton, insert_eq_of_mem heC] ⟩  

theorem base.diff_finite_comm (hB₁ : M.base B₁) (hB₂ : M.base B₂) :
    (B₁ \ B₂).Finite ↔ (B₂ \ B₁).Finite := 
  Finite_iff_Finite_of_encard_eq_encard (hB₁.encard_diff_comm hB₂)

theorem base.diff_infinite_comm (hB₁ : M.base B₁) (hB₂ : M.base B₂) : 
    (B₁ \ B₂).Infinite ↔ (B₂ \ B₁).Infinite := 
  Infinite_iff_Infinite_of_encard_eq_encard (hB₁.encard_diff_comm hB₂)

theorem base.ncard_eq_ncard_of_base (hB₁ : M.base B₁) (hB₂ : M.base B₂) : B₁.ncard = B₂.ncard :=
by rw [←encard_toNat_eq, hB₁.encard_eq_encard_of_base hB₂, encard_toNat_eq]

end base

end Matroid 
-- private theorem encard_eq_of_exch {base : Set α → Prop} (exch : exchange_property base)
-- (hB₁ : base B₁) (hB₂ : base B₂) : B₁.encard = B₂.encard :=
-- by rw [←encard_diff_add_encard_inter B₁ B₂, encard_diff_eq_of_exch exch hB₁ hB₂, inter_comm, 
--     encard_diff_add_encard_inter]

-- -- private theorem finite_of_finite_of_exch {base : Set α → Prop} (exch : exchange_property base) 
-- -- (hB : base B) (hB' : base B') (h : B.Finite) : 
-- --   B'.Finite :=
-- -- begin
-- --   rw [←inter_union_diff B' B], 
-- --   exact finite.union (h.subset (inter_subset_right _ _)) 
-- --     (diff_aux_of_exch exch hB hB' (h.diff _)).1, 
-- -- end 

-- -- private theorem card_eq_card_of_exchange {base : Set α → Prop} (exch : exchange_property base)
-- -- (hB₁ : base B₁) (hB₂ : base B₂) :
-- --   B₁.ncard = B₂.ncard :=
-- -- begin 
-- --   obtain (hB₁' | hB₁') := B₁.Finite_or_infinite.symm,
-- --   { rw [hB₁'.ncard, infinite.ncard (λ h, hB₁' (finite_of_finite_of_exch exch hB₂ hB₁ h))] },
-- --   have hdcard := (diff_aux_of_exch exch hB₁ hB₂ (hB₁'.diff _)).2,
-- --   have hB₂' := finite_of_finite_of_exch exch hB₁ hB₂ hB₁', 
-- --   rw [←ncard_inter_add_ncard_diff_eq_ncard B₁ B₂ hB₁', ←hdcard, inter_comm, 
-- --     ncard_inter_add_ncard_diff_eq_ncard B₂ B₁ hB₂'],
-- -- end

-- end prelim

-- /-- A `matroid` is a nonempty collection of sets satisfying the exchange property and the maximal
--   subset property. Each such set is called a `base` of the matroid. -/

-- @[ext] structure Matroid (α : Type*) :=
--   (ground : Set α)
--   (base : Set α → Prop)
--   (exists_base' : ∃ B, base B)
--   (base_exchange' : exchange_property base)
--   (maximality : exists_maximal_subset_property (λ I, ∃ B, base B ∧ I ⊆ B))
--   (subset_ground' : ∀ B, base B → B ⊆ ground)

-- -- instance {E : Type*} [finite E] : finite (Matroid α) :=
-- -- finite.of_injective (λ M, M.base) (λ M₁ M₂ h, (by { ext, dsimp only at h, rw h }))

-- -- instance {E : Type*} : nonempty (Matroid α) :=
-- --   ⟨⟨@eq _ ∅, ⟨_,rfl⟩, by { rintro _ _ rfl rfl a h, exfalso, exact not_mem_empty a h.1 }, 
-- --     exists_maximal_subset_property_of_bounded 
-- --     ⟨0, by { rintro I ⟨B, rfl, hIB⟩, rw subset_empty_iff.mp hIB, simp }⟩⟩⟩
-- namespace Matroid 

-- def E (M : Matroid α) : Set α := M.ground

-- @[simp] theorem ground_eq_E (M : Matroid α) : M.ground = M.E := rfl 

-- section tac

-- @[user_attribute]
-- meta def ssE_rules : user_attribute :=
-- { name := `ssE_rules,
--   descr := "theorems usable to prove subset of ground set" }

-- @[user_attribute]
-- meta def ssE_finish_rules : user_attribute :=
-- { name := `ssE_finish_rules,
--   descr := "finishing theorems usable to prove subset of ground set" }

-- meta def ssE_finish : tactic unit := `[solve_by_elim with ssE_finish_rules {max_depth := 2}] 

-- meta def ssE : tactic unit := `[solve_by_elim with ssE_rules 
--   {max_depth := 3, discharger := ssE_finish}]

-- -- @[ssE_rules] private theorem empty_subset_ground {M : Matroid α} : ∅ ⊆ M.E := empty_subset _

-- -- @[ssE_rules] private theorem ground_subset_ground {M : Matroid α} : M.E ⊆ M.E := subset.rfl

-- -- @[ssE_rules] private theorem union_subset_ground {M : Matroid α} {X Y : Set α} 
-- --   (hX : X ⊆ M.E) (hY : Y ⊆ M.E) : X ∪ Y ⊆ M.E := union_subset hX hY 

-- @[ssE_rules] private theorem inter_right_subset_ground {X Y : Set α} {M : Matroid α} 
-- (hX : X ⊆ M.E) : X ∩ Y ⊆ M.E := (inter_subset_left _ _).trans hX 

-- @[ssE_rules] private theorem inter_left_subset_ground {X Y : Set α} {M : Matroid α}
-- (hX : X ⊆ M.E) : Y ∩ X ⊆ M.E := (inter_subset_right _ _).trans hX 

-- @[ssE_rules] private theorem diff_subset_ground {X Y : Set α} {M : Matroid α}
-- (hX : X ⊆ M.E) : X \ Y ⊆ M.E := (diff_subset _ _).trans hX 

-- -- @[ssE_rules] private theorem ground_diff_subset_ground {X : Set α} {M : Matroid α} : 
-- --   M.E \ X ⊆ M.E := diff_subset_ground subset.rfl 

-- @[simp] theorem ground_inter_right {M : Matroid α} (hXE : X ⊆ M.E . ssE) : M.E ∩ X = X :=
-- inter_eq_self_of_subset_right hXE 

-- @[simp] theorem ground_inter_left {M : Matroid α} (hXE : X ⊆ M.E . ssE) : X ∩ M.E = X :=
-- inter_eq_self_of_subset_left hXE 

-- @[ssE_rules] private theorem insert_subset_ground {e : α} {X : Set α} {M : Matroid α} 
-- (he : e ∈ M.E) (hX : X ⊆ M.E) : insert e X ⊆ M.E := insert_subset.mpr ⟨he, hX⟩  

-- @[ssE_rules] private theorem singleton_subset_ground {e : α} {M : Matroid α} (he : e ∈ M.E) :
--   {e} ⊆ M.E := 
-- singleton_subset_iff.mpr he

-- attribute [ssE_rules] mem_of_mem_of_subset empty_subset subset.rfl union_subset

-- end tac

-- section defs

-- /-- A set is independent if it is contained in a base.  -/
-- def indep (M : Matroid α) (I : Set α) : Prop := ∃ B, M.base B ∧ I ⊆ B

-- /-- A subset of `M.E` is dependent if it is not independent . -/
-- def dep (M : Matroid α) (D : Set α) : Prop := ¬M.indep D ∧ D ⊆ M.E   

-- /-- A basis for a set `X ⊆ M.E` is a maximal independent subset of `X`
--   (Often in the literature, the word 'basis' is used to refer to what we call a 'base'). -/
-- def basis (M : Matroid α) (I X : Set α) : Prop := 
--   I ∈ maximals (⊆) {A | M.indep A ∧ A ⊆ X} ∧ X ⊆ M.E  

-- /-- A circuit is a minimal dependent set -/
-- def circuit (M : Matroid α) (C : Set α) : Prop := C ∈ minimals (⊆) {X | M.dep X}

-- /-- A coindependent set is a subset of `M.E` that is disjoint from some base -/
-- def coindep (M : Matroid α) (I : Set α) : Prop := I ⊆ M.E ∧ (∃ B, M.base B ∧ disjoint I B)  

-- section properties

-- /-- Typeclass for a matroid having finite ground set. This is just a wrapper for `[M.E.Finite]`-/
-- class finite (M : Matroid α) : Prop := (ground_finite : M.E.Finite)

-- theorem ground_finite (M : Matroid α) [M.Finite] : M.E.Finite := ‹M.Finite›.ground_finite   

-- theorem set_finite (M : Matroid α) [M.Finite] (X : Set α) (hX : X ⊆ M.E . ssE) : X.Finite :=
-- M.ground_finite.subset hX 

-- instance finite_of_finite [@_root_.Finite α] {M : Matroid α} : finite M := 
-- ⟨set.to_finite _⟩ 

-- class Finite_rk (M : Matroid α) : Prop := (exists_finite_base : ∃ B, M.base B ∧ B.Finite) 

-- -- instance Finite_rk_of_finite (M : Matroid α) [finite M] : Finite_rk M := 
-- -- ⟨M.exists_base'.imp (λ B hB, ⟨hB, M.set_finite B (M.subset_ground' _ hB)⟩) ⟩ 

-- class Infinite_rk (M : Matroid α) : Prop := (exists_infinite_base : ∃ B, M.base B ∧ B.infinite)

-- class finitary (M : Matroid α) : Prop := (cct_finite : ∀ (C : Set α), M.circuit C → C.Finite) 

-- class rk_pos (M : Matroid α) : Prop := (empty_not_base : ¬M.base ∅)

-- class dual_rk_pos (M : Matroid α) : Prop := (univ_not_base : ¬M.base univ)

-- end properties

-- end defs

-- variables {M : Matroid α}

-- section base

-- @[ssE_finish_rules] theorem base.subset_ground (hB : M.base B) : B ⊆ M.E :=
-- M.subset_ground' B hB 

-- theorem exists_base (M : Matroid α) : ∃ B, M.base B := M.exists_base'

-- theorem base.exchange (hB₁ : M.base B₁) (hB₂ : M.base B₂) (hx : e ∈ B₁ \ B₂) :
--   ∃ y ∈ B₂ \ B₁, M.base (insert y (B₁ \ {e}))  :=
-- M.base_exchange' B₁ B₂ hB₁ hB₂ _ hx

-- theorem base.exchange_mem (hB₁ : M.base B₁) (hB₂ : M.base B₂) (hxB₁ : e ∈ B₁) (hxB₂ : e ∉ B₂) :
--   ∃ y, (y ∈ B₂ ∧ y ∉ B₁) ∧ M.base (insert y (B₁ \ {e})) :=
-- by simpa using hB₁.exchange hB₂ ⟨hxB₁, hxB₂⟩

-- theorem base.eq_of_subset_base (hB₁ : M.base B₁) (hB₂ : M.base B₂) (hB₁B₂ : B₁ ⊆ B₂) :
--   B₁ = B₂ :=
-- antichain_of_exch M.base_exchange' hB₁ hB₂ hB₁B₂

-- theorem base.encard_diff_comm (hB₁ : M.base B₁) (hB₂ : M.base B₂) :
--   (B₁ \ B₂).encard = (B₂ \ B₁).encard := encard_diff_eq_of_exch (M.base_exchange') hB₁ hB₂ 

-- theorem base.card_diff_comm (hB₁ : M.base B₁) (hB₂ : M.base B₂) :
--   (B₁ \ B₂).ncard = (B₂ \ B₁).ncard := 
-- by rw [←encard_to_nat_eq, hB₁.encard_diff_comm hB₂, encard_to_nat_eq]

-- theorem base.encard_eq_encard_of_base (hB₁ : M.base B₁) (hB₂ : M.base B₂) : 
--   B₁.encard = B₂.encard :=
-- by rw [encard_eq_of_exch M.base_exchange' hB₁ hB₂]

-- theorem base.card_eq_card_of_base (hB₁ : M.base B₁) (hB₂ : M.base B₂) : 
--   B₁.ncard = B₂.ncard :=
-- by rw [←encard_to_nat_eq B₁, hB₁.encard_eq_encard_of_base hB₂, encard_to_nat_eq]

-- theorem base.Finite_of_finite (hB : M.base B) (h : B.Finite) (hB' : M.base B') : B'.Finite :=
-- (finite_iff_finite_of_encard_eq_encard (hB.encard_eq_encard_of_base hB')).mp h  
-- -- finite_of_finite_of_exch M.base_exchange' hB hB' h

-- theorem base.infinite_of_infinite (hB : M.base B) (h : B.infinite) (hB₁ : M.base B₁) :
--   B₁.infinite :=
-- by_contra (λ hB_inf, (hB₁.Finite_of_finite (not_infinite.mp hB_inf) hB).not_infinite h)

-- theorem base.Finite [Finite_rk M] (hB : M.base B) : B.Finite := 
-- let ⟨B₀,hB₀⟩ := ‹Finite_rk M›.exists_finite_base in hB₀.1.Finite_of_finite hB₀.2 hB

-- theorem base.infinite [Infinite_rk M] (hB : M.base B) : B.infinite :=
-- let ⟨B₀,hB₀⟩ := ‹Infinite_rk M›.exists_infinite_base in hB₀.1.infinite_of_infinite hB₀.2 hB

-- theorem base.Finite_rk_of_finite (hB : M.base B) (hfin : B.Finite) : Finite_rk M := ⟨⟨B, hB, hfin⟩⟩   

-- theorem base.Infinite_rk_of_infinite (hB : M.base B) (h : B.infinite) : Infinite_rk M := ⟨⟨B, hB, h⟩⟩ 

-- theorem not_Finite_rk (M : Matroid α) [Infinite_rk M] : ¬ Finite_rk M := 
-- by { introI h, obtain ⟨B,hB⟩ := M.exists_base, exact hB.infinite hB.Finite }

-- theorem not_Infinite_rk (M : Matroid α) [Finite_rk M] : ¬ Infinite_rk M := 
-- by { introI h, obtain ⟨B,hB⟩ := M.exists_base, exact hB.infinite hB.Finite }

-- theorem finite_or_Infinite_rk (M : Matroid α) : Finite_rk M ∨ Infinite_rk M :=
-- let ⟨B, hB⟩ := M.exists_base in B.Finite_or_infinite.elim 
--   (or.inl ∘ hB.Finite_rk_of_finite) (or.inr ∘ hB.Infinite_rk_of_infinite)

-- instance Finite_rk_of_finite {M : Matroid α} [finite M] : Finite_rk M := 
-- let ⟨B, hB⟩ := M.exists_base in ⟨⟨B, hB, (M.ground_finite).subset hB.subset_ground⟩⟩ 

-- instance finitary_of_Finite_rk {M : Matroid α} [Finite_rk M] : finitary M := 
-- ⟨ begin
--   intros C hC, 
--   obtain (rfl | ⟨e,heC⟩) := C.eq_empty_or_nonempty, exact finite_empty, 
--   have hi : M.indep (C \ {e}), 
--   from by_contra (λ h, (hC.2 ⟨h, (diff_subset _ _).trans hC.1.2⟩ (diff_subset C {e}) heC).2 rfl),
--   obtain ⟨B, hB, hCB⟩ := hi, 
--   convert (hB.Finite.subset hCB).insert e, 
--   rw [insert_diff_singleton, insert_eq_of_mem heC],
-- end ⟩  

-- -- theorem base.card_eq_card_of_base (hB₁ : M.base B₁) (hB₂ : M.base B₂) : B₁.ncard = B₂.ncard :=
-- -- card_eq_card_of_exchange M.base_exchange' hB₁ hB₂ 

-- theorem base.diff_finite_comm (hB₁ : M.base B₁) (hB₂ : M.base B₂) :
--   (B₁ \ B₂).Finite ↔ (B₂ \ B₁).Finite := 
-- finite_iff_finite_of_encard_eq_encard (hB₁.encard_diff_comm hB₂)
-- -- ⟨λ h, (diff_aux_of_exch M.base_exchange' hB₁ hB₂ h).1, 
-- --   λ h, (diff_aux_of_exch M.base_exchange' hB₂ hB₁ h).1⟩

-- theorem base.diff_infinite_comm (hB₁ : M.base B₁) (hB₂ : M.base B₂) : 
--   (B₁ \ B₂).infinite ↔ (B₂ \ B₁).infinite := 
-- infinite_iff_infinite_of_encard_eq_encard (hB₁.encard_diff_comm hB₂)

--   -- obtain (h | h) := (B₁ \ B₂).Finite_or_infinite, 
--   -- { rw (diff_aux_of_exch M.base_exchange' hB₁ hB₂ h).2 },
--   -- rw [h.ncard, infinite.ncard (λ h', h (diff_aux_of_exch M.base_exchange' hB₂ hB₁ h').1)], 


-- theorem base.ncard_eq_ncard_of_base (hB₁ : M.base B₁) (hB₂ : M.base B₂) : B₁.ncard = B₂.ncard :=
-- by rw [←encard_to_nat_eq, hB₁.encard_eq_encard_of_base hB₂, encard_to_nat_eq]

-- end base

-- section dep_indep

-- theorem indep_iff_subset_base : M.indep I ↔ ∃ B, M.base B ∧ I ⊆ B := iff.rfl

-- theorem dep_iff : M.dep D ↔ ¬M.indep D ∧ D ⊆ M.E := iff.rfl  

-- @[ssE_finish_rules] theorem indep.subset_ground (hI : M.indep I) : I ⊆ M.E := 
-- by { obtain ⟨B, hB, hIB⟩ := hI, exact hIB.trans hB.subset_ground } 

-- @[ssE_finish_rules] theorem dep.subset_ground (hD : M.dep D) : D ⊆ M.E :=
-- hD.2 

-- @[ssE_finish_rules] theorem coindep.subset_ground (hX : M.coindep X) : X ⊆ M.E :=
-- hX.1

-- theorem indep_or_dep (hX : X ⊆ M.E . ssE) : M.indep X ∨ M.dep X := 
-- by { rw [dep, and_iff_left hX], apply em }

-- theorem indep.not_dep (hI : M.indep I) : ¬ M.dep I := 
-- λ h, h.1 hI   

-- theorem dep.not_indep (hD : M.dep D) : ¬ M.indep D := 
-- hD.1  

-- theorem dep_of_not_indep (hD : ¬ M.indep D) (hDE : D ⊆ M.E . ssE) : M.dep D := 
-- ⟨hD, hDE⟩ 

-- theorem indep_of_not_dep (hI : ¬ M.dep I) (hIE : I ⊆ M.E . ssE) : M.indep I := 
-- by_contra (λ h, hI ⟨h, hIE⟩)

-- @[simp] theorem not_dep_iff (hX : X ⊆ M.E . ssE) : ¬ M.dep X ↔ M.indep X := 
-- by rw [dep, and_iff_left hX, not_not]

-- @[simp] theorem not_indep_iff (hX : X ⊆ M.E . ssE) : ¬ M.indep X ↔ M.dep X := 
-- by rw [dep, and_iff_left hX]  

-- theorem indep.exists_base_supset (hI : M.indep I) : ∃ B, M.base B ∧ I ⊆ B :=
-- hI

-- theorem indep.subset (hJ : M.indep J) (hIJ : I ⊆ J) : M.indep I :=
-- by {obtain ⟨B, hB, hJB⟩ := hJ, exact ⟨B, hB, hIJ.trans hJB⟩}

-- theorem dep.supset (hD : M.dep D) (hDX : D ⊆ X) (hXE : X ⊆ M.E . ssE) : M.dep X := 
-- dep_of_not_indep (λ hI, (hI.subset hDX).not_dep hD)

-- @[simp] theorem empty_indep (M : Matroid α) : M.indep ∅ :=
-- exists.elim M.exists_base (λ B hB, ⟨_, hB, B.empty_subset⟩)

-- theorem indep.Finite [Finite_rk M] (hI : M.indep I) : I.Finite := 
-- let ⟨B, hB, hIB⟩ := hI in hB.Finite.subset hIB  

-- theorem indep.inter_right (hI : M.indep I) (X : Set α) : M.indep (I ∩ X) :=
-- hI.subset (inter_subset_left _ _)

-- theorem indep.inter_left (hI : M.indep I) (X : Set α) : M.indep (X ∩ I) :=
-- hI.subset (inter_subset_right _ _)

-- theorem indep.diff (hI : M.indep I) (X : Set α) : M.indep (I \ X) := hI.subset (diff_subset _ _)

-- theorem base.indep (hB : M.base B) : M.indep B := ⟨B, hB, subset_rfl⟩

-- theorem base.eq_of_subset_indep (hB : M.base B) (hI : M.indep I) (hBI : B ⊆ I) : B = I :=
-- let ⟨B', hB', hB'I⟩ := hI in hBI.antisymm (by rwa hB.eq_of_subset_base hB' (hBI.trans hB'I))

-- theorem base_iff_maximal_indep : M.base B ↔ M.indep B ∧ ∀ I, M.indep I → B ⊆ I → B = I :=
-- begin
--   refine ⟨λ h, ⟨h.indep, λ _, h.eq_of_subset_indep ⟩,λ h, _⟩,
--   obtain ⟨⟨B', hB', hBB'⟩, h⟩ := h,
--   rwa h _ hB'.indep hBB',
-- end

-- theorem base_iff_mem_maximals : M.base B ↔ B ∈ maximals (⊆) {I | M.indep I} := 
-- begin
--   rw [base_iff_maximal_indep, maximals], 
--   exact ⟨λ h, ⟨h.1,λ I hI hBI, (h.2 I hI hBI).symm.subset⟩,
--     λ h, ⟨h.1, λ I hI hBI, hBI.antisymm (h.2 hI hBI)⟩⟩,  
-- end  

-- theorem indep.base_of_maximal (hI : M.indep I) (h : ∀ J, M.indep J → I ⊆ J → I = J) : M.base I := 
-- base_iff_maximal_indep.mpr ⟨hI,h⟩

-- theorem base.dep_of_ssubset (hB : M.base B) (h : B ⊂ X) (hX : X ⊆ M.E . ssE) : M.dep X :=
-- ⟨λ hX, h.ne (hB.eq_of_subset_indep hX h.subset), hX⟩

-- theorem base.dep_of_insert (hB : M.base B) (heB : e ∉ B) (he : e ∈ M.E . ssE) : M.dep (insert e B) :=
-- hB.dep_of_ssubset (ssubset_insert heB)

-- theorem base.exchange_base_of_indep (hB : M.base B) (he : e ∈ B) (hf : f ∉ B)
-- (hI : M.indep (insert f (B \ {e}))) : M.base (insert f (B \ {e})) :=
-- begin
--   obtain ⟨B', hB', hIB'⟩ := hI,
--   have hBeB' := (subset_insert _ _).trans hIB',
--   have heB' : e ∉ B',
--   { intro heB',
--     have hBB' : B ⊆ B',
--     { refine subset_trans _ (insert_subset.mpr ⟨heB',hIB'⟩),
--       rw [insert_comm, insert_diff_singleton],
--       refine (subset_insert _ _).trans (subset_insert _ _)},
--     rw ←hB.eq_of_subset_indep hB'.indep hBB' at hIB',
--     exact hf (hIB' (mem_insert _ _))},
--   obtain ⟨y,hy,hy'⟩ := hB.exchange hB' ⟨he,heB'⟩,
--   rw ←hy'.eq_of_subset_base hB' (insert_subset.mpr ⟨hy.1, hBeB'⟩) at hIB',
--   have : f = y,
--   { exact (mem_insert_iff.mp (hIB' (mem_insert _ _))).elim id
--       (λ h', (hf (diff_subset _ _ h')).elim)},
--   rwa this,
-- end

-- theorem base.exchange_base_of_indep' (hB : M.base B) (he : e ∈ B) (hf : f ∉ B) 
-- (hI : M.indep (insert f B \ {e})) : 
--   M.base (insert f B \ {e}) := 
-- begin
--   have hfe : f ≠ e, { rintro rfl, exact hf he }, 
--   rw [←insert_diff_singleton_comm hfe] at *, 
--   exact hB.exchange_base_of_indep he hf hI, 
-- end 

-- /-- If the difference of two bases is a singleton, then they differ by an insertion/removal -/
-- theorem base.eq_exchange_of_diff_eq_singleton (hB : M.base B) (hB' : M.base B') (h : B \ B' = {e}) : 
--   ∃ f ∈ B' \ B, B' = (insert f B) \ {e} :=
-- begin
--   obtain ⟨f, hf, hb⟩ := hB.exchange hB' (h.symm.subset (mem_singleton e)), 
--   have hne : f ≠ e, 
--   { rintro rfl, exact hf.2 (h.symm.subset (mem_singleton f)).1 },
--   rw insert_diff_singleton_comm hne at hb, 
--   refine ⟨f, hf, (hb.eq_of_subset_base hB' _).symm⟩, 
--   rw [diff_subset_iff, insert_subset, union_comm, ←diff_subset_iff, h, and_iff_left subset.rfl],
--   exact or.inl hf.1,
-- end  

-- theorem basis.indep (hI : M.basis I X) : M.indep I := hI.1.1.1

-- theorem basis.subset (hI : M.basis I X) : I ⊆ X := hI.1.1.2

-- @[ssE_finish_rules] theorem basis.subset_ground (hI : M.basis I X) : X ⊆ M.E :=
-- hI.2 

-- theorem basis.basis_inter_ground (hI : M.basis I X) : M.basis I (X ∩ M.E) := 
-- by { convert hI, rw [inter_eq_self_of_subset_left hI.subset_ground] }

-- @[ssE_finish_rules] theorem basis.subset_ground_left (hI : M.basis I X) : I ⊆ M.E := 
-- hI.indep.subset_ground

-- theorem basis.eq_of_subset_indep (hI : M.basis I X) (hJ : M.indep J) (hIJ : I ⊆ J) (hJX : J ⊆ X) :
--   I = J :=
-- hIJ.antisymm (hI.1.2 ⟨hJ, hJX⟩ hIJ)

-- theorem basis.Finite (hI : M.basis I X) [Finite_rk M] : I.Finite := hI.indep.Finite 

-- theorem basis_iff' : 
--   M.basis I X ↔ (M.indep I ∧ I ⊆ X ∧ ∀ J, M.indep J → I ⊆ J → J ⊆ X → I = J) ∧ X ⊆ M.E :=
-- begin
--   simp_rw [basis, and.congr_left_iff, maximals, mem_set_of_eq, and_imp, sep_set_of, 
--     mem_set_of_eq, and_assoc, and.congr_right_iff],   
--   intros hXE hI hIX, 
--   exact ⟨λ h J hJ hIJ hJX, hIJ.antisymm (h hJ hJX hIJ), 
--     λ h J hJ hIJ hJX, (h J hJ hJX hIJ).symm.subset⟩,
-- end 

-- theorem basis_iff (hX : X ⊆ M.E . ssE) : 
--   M.basis I X ↔ (M.indep I ∧ I ⊆ X ∧ ∀ J, M.indep J → I ⊆ J → J ⊆ X → I = J) :=
-- by rw [basis_iff', and_iff_left hX]

-- theorem basis_iff_mem_maximals (hX : X ⊆ M.E . ssE): 
--   M.basis I X ↔ I ∈ maximals (⊆) (λ (I : Set α), M.indep I ∧ I ⊆ X) :=
-- begin
--   simp_rw [basis_iff, mem_maximals_prop_iff, and_assoc, and_imp, and.congr_right_iff], 
--   exact λ hI hIX, ⟨λ h J hJ hJX hIJ, h J hJ hIJ hJX, λ h J hJ hJX hIJ, h hJ hIJ hJX⟩, 
-- end 

-- theorem indep.basis_of_maximal_subset (hI : M.indep I) (hIX : I ⊆ X)
-- (hmax : ∀ ⦃J⦄, M.indep J → I ⊆ J → J ⊆ X → J ⊆ I) (hX : X ⊆ M.E . ssE) : M.basis I X :=
-- begin 
--   rw [basis_iff (by ssE : X ⊆ M.E), and_iff_right hI, and_iff_right hIX], 
--   exact λ J hJ hIJ hJX, hIJ.antisymm (hmax hJ hIJ hJX), 
-- end 

-- theorem basis.basis_subset (hI : M.basis I X) (hIY : I ⊆ Y) (hYX : Y ⊆ X) : M.basis I Y :=
-- begin
--   rw [basis_iff (hYX.trans hI.subset_ground), and_iff_right hI.indep, and_iff_right hIY], 
--   exact λ J hJ hIJ hJY, hI.eq_of_subset_indep hJ hIJ (hJY.trans hYX), 
-- end 

-- @[simp] theorem basis_empty_iff (M : Matroid α) :
--   M.basis I ∅ ↔ I = ∅ :=
-- begin
--   refine ⟨λ h, subset_empty_iff.mp h.subset, _⟩,
--   rintro rfl,
--   rw [basis_iff, and_iff_right M.empty_indep, and_iff_right (empty_subset _)], 
--   exact λ _ _, subset_antisymm, 
-- end

-- theorem basis.dep_of_ssubset (hI : M.basis I X) {Y : Set α} (hIY : I ⊂ Y) (hYX : Y ⊆ X) : M.dep Y :=
-- begin
--   rw [←not_indep_iff (hYX.trans hI.subset_ground)], 
--   exact λ hY, hIY.ne (hI.eq_of_subset_indep hY hIY.subset hYX), 
-- end 

-- theorem basis.insert_dep (hI : M.basis I X) (he : e ∈ X \ I) : M.dep (insert e I) :=
-- hI.dep_of_ssubset (ssubset_insert he.2) (insert_subset.mpr ⟨he.1,hI.subset⟩)

-- theorem basis.mem_of_insert_indep (hI : M.basis I X) (he : e ∈ X) (hIe : M.indep (insert e I)) : 
--   e ∈ I :=
-- by_contra (λ heI, (hI.insert_dep ⟨he, heI⟩).not_indep hIe) 

-- theorem basis.not_basis_of_ssubset (hI : M.basis I X) (hJI : J ⊂ I) : ¬ M.basis J X :=
-- λ h, hJI.ne (h.eq_of_subset_indep hI.indep hJI.subset hI.subset)

-- theorem indep.subset_basis_of_subset (hI : M.indep I) (hIX : I ⊆ X) (hX : X ⊆ M.E . ssE) : 
--   ∃ J, M.basis J X ∧ I ⊆ J :=
-- begin
--   obtain ⟨J, ⟨(hJ : M.indep J),hIJ,hJX⟩, hJmax⟩ := M.maximality I X hI hIX, 
--   use J, 
--   rw [and_iff_left hIJ, basis_iff, and_iff_right hJ, and_iff_right hJX], 
--   exact λ K hK hJK hKX, hJK.antisymm (hJmax ⟨hK, hIJ.trans hJK, hKX⟩ hJK),  
-- end


-- theorem exists_basis (M : Matroid α) (X : Set α) (hX : X ⊆ M.E . ssE) : ∃ I, M.basis I X :=
-- let ⟨I, hI, _⟩ := M.empty_indep.subset_basis_of_subset (empty_subset X) in ⟨_,hI⟩

-- theorem exists_basis_subset_basis (M : Matroid α) (hXY : X ⊆ Y) (hY : Y ⊆ M.E . ssE) :
--   ∃ I J, M.basis I X ∧ M.basis J Y ∧ I ⊆ J :=
-- begin
--   obtain ⟨I, hI⟩ := M.exists_basis X (hXY.trans hY), 
--   obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_basis_of_subset (hI.subset.trans hXY), 
--   exact ⟨_, _, hI, hJ, hIJ⟩, 
-- end    

-- theorem basis.exists_basis_inter_eq_of_supset (hI : M.basis I X) (hXY : X ⊆ Y) (hY : Y ⊆ M.E . ssE) :
--   ∃ J, M.basis J Y ∧ J ∩ X = I :=
-- begin
--   obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_basis_of_subset (hI.subset.trans hXY), 
--   refine ⟨J, hJ, subset_antisymm _ (subset_inter hIJ hI.subset)⟩,  
--   exact λ e he, hI.mem_of_insert_indep he.2 (hJ.indep.subset (insert_subset.mpr ⟨he.1, hIJ⟩)), 
-- end   

-- theorem exists_basis_union_inter_basis (M : Matroid α) (X Y : Set α) (hX : X ⊆ M.E . ssE) 
--   (hY : Y ⊆ M.E . ssE) : ∃ I, M.basis I (X ∪ Y) ∧ M.basis (I ∩ Y) Y := 
-- begin
--   obtain ⟨J, hJ⟩ := M.exists_basis Y, 
--   exact (hJ.exists_basis_inter_eq_of_supset (subset_union_right X Y)).imp 
--     (λ I hI, ⟨hI.1, by rwa hI.2⟩), 
-- end 

-- theorem indep.eq_of_basis (hI : M.indep I) (hJ : M.basis J I) : J = I :=
-- hJ.eq_of_subset_indep hI hJ.subset subset.rfl

-- theorem indep.basis_self (hI : M.indep I) : M.basis I I := 
-- begin
--   rw [basis_iff', and_iff_left hI.subset_ground, and_iff_right hI, and_iff_right subset.rfl], 
--   exact λ _ _, subset_antisymm, 
-- end 

-- @[simp] theorem basis_self_iff_indep : M.basis I I ↔ M.indep I := ⟨basis.indep, indep.basis_self⟩

-- theorem basis.exists_base (hI : M.basis I X) : ∃ B, M.base B ∧ I = B ∩ X :=
-- begin
--   obtain ⟨B,hB, hIB⟩ := hI.indep,
--   refine ⟨B, hB, subset_antisymm (subset_inter hIB hI.subset) _⟩,
--   rw hI.eq_of_subset_indep (hB.indep.inter_right X) (subset_inter hIB hI.subset)
--     (inter_subset_right _ _),
-- end

-- theorem base_iff_basis_ground : M.base B ↔ M.basis B M.E :=
-- begin
--   rw [base_iff_maximal_indep, basis_iff, and_congr_right], 
--   intro hB, 
--   rw [and_iff_right hB.subset_ground], 
--   exact ⟨λ h J hJ hBJ hJE, h _ hJ hBJ, λ h I hI hBI, h I hI hBI hI.subset_ground⟩,
-- end 

-- theorem base.basis_ground (hB : M.base B) : M.basis B M.E := base_iff_basis_ground.mp hB

-- theorem indep.basis_of_forall_insert (hI : M.indep I) 
--   (hIX : I ⊆ X) (he : ∀ e ∈ X \ I, ¬ M.indep (insert e I)) (hX : X ⊆ M.E . ssE) : M.basis I X :=
-- begin
--   rw [basis_iff, and_iff_right hI, and_iff_right hIX], 
--   refine λJ hJ hIJ hJX, hIJ.antisymm (λ e heJ, by_contra (λ heI, he e ⟨hJX heJ, heI⟩ _)),  
--   exact hJ.subset (insert_subset.mpr ⟨heJ, hIJ⟩), 
-- end 

-- theorem basis.Union_basis_Union {ι : Type*} (X I : ι → Set α) (hI : ∀ i, M.basis (I i) (X i)) 
-- (h_ind : M.indep (⋃ i, I i)) : M.basis (⋃ i, I i) (⋃ i, X i) :=
-- begin
   
--   refine h_ind.basis_of_forall_insert 
--     (Union_subset_iff.mpr (λ i, (hI i).subset.trans (subset_Union _ _))) (λ e he hi, _)
--     (Union_subset (λ i, (hI i).subset_ground)), 
--   simp only [mem_diff, mem_Union, not_exists] at he, 
--   obtain ⟨i, heXi⟩ := he.1, 
--   exact he.2 i ((hI i).mem_of_insert_indep heXi 
--     (hi.subset (insert_subset_insert (subset_Union _ _)))), 
-- end 

-- theorem basis.basis_Union {ι : Type*} [nonempty ι] (X : ι → Set α) (hI : ∀ i, M.basis I (X i)) : 
--   M.basis I (⋃ i, X i) :=
-- begin
--   convert basis.Union_basis_Union X (λ _, I) (λ i, hI i) _, 
--   all_goals { rw Union_const },
--   exact (hI (‹nonempty ι›.some)).indep, 
-- end 

-- theorem basis.union_basis_union (hIX : M.basis I X) (hJY : M.basis J Y) (h : M.indep (I ∪ J)) : 
--   M.basis (I ∪ J) (X ∪ Y) :=
-- begin 
--   rw [union_eq_Union, union_eq_Union], 
--   refine basis.Union_basis_Union _ _ _ _,   
--   { simp only [bool.forall_bool, bool.cond_ff, bool.cond_tt], exact ⟨hJY, hIX⟩ }, 
--   rwa [←union_eq_Union], 
-- end 

-- theorem basis.basis_union (hIX : M.basis I X) (hIY : M.basis I Y) : M.basis I (X ∪ Y) :=
-- by { convert hIX.union_basis_union hIY _; rw union_self, exact hIX.indep }

-- theorem basis.basis_union_of_subset (hI : M.basis I X) (hJ : M.indep J) (hIJ : I ⊆ J) : 
--   M.basis J (J ∪ X) :=
-- begin
--   convert hJ.basis_self.union_basis_union hI (by rwa union_eq_left_iff_subset.mpr hIJ), 
--   rw union_eq_left_iff_subset.mpr hIJ, 
-- end 

-- theorem basis.insert_basis_insert (hI : M.basis I X) (h : M.indep (insert e I)) : 
--   M.basis (insert e I) (insert e X) :=
-- begin
--   convert hI.union_basis_union 
--     (indep.basis_self (h.subset (singleton_subset_iff.mpr (mem_insert _ _)))) _, 
--   simp, simp, simpa, 
-- end 

-- theorem base.insert_dep (hB : M.base B) (h : e ∉ B) : ¬ M.indep (insert e B) :=
--   λ h', (insert_ne_self.mpr h).symm ((base_iff_maximal_indep.mp hB).2 _ h' (subset_insert _ _))

-- theorem base.ssubset_dep (hB : M.base B) (h : B ⊂ X) : ¬ M.indep X :=
--   λ h', h.ne ((base_iff_maximal_indep.mp hB).2 _ h' h.subset)

-- theorem indep.exists_insert_of_not_base (hI : M.indep I) (hI' : ¬M.base I) (hB : M.base B) : 
--   ∃ e ∈ B \ I, M.indep (insert e I) :=
-- begin
--   obtain ⟨B', hB', hIB'⟩ := hI, 
--   obtain ⟨x, hxB', hx⟩ := exists_of_ssubset (hIB'.ssubset_of_ne (by { rintro rfl, exact hI' hB' })), 
--   obtain (hxB | hxB) := em (x ∈ B), 
--   { exact ⟨x, ⟨hxB, hx⟩ , ⟨B', hB', insert_subset.mpr ⟨hxB',hIB'⟩⟩⟩ },
--   obtain ⟨e,he, hbase⟩ := hB'.exchange hB ⟨hxB',hxB⟩,    
--   exact ⟨e, ⟨he.1, not_mem_subset hIB' he.2⟩, 
--     ⟨_, hbase, insert_subset_insert (subset_diff_singleton hIB' hx)⟩⟩,  
-- end  

-- theorem basis.inter_eq_of_subset_indep (hIX : M.basis I X) (hIJ : I ⊆ J) (hJ : M.indep J) : 
--   J ∩ X = I := 
-- (subset_inter hIJ hIX.subset).antisymm' 
--   (λ e he, hIX.mem_of_insert_indep he.2 (hJ.subset (insert_subset.mpr ⟨he.1, hIJ⟩))) 

-- theorem base.exists_insert_of_ssubset (hB : M.base B) (hIB : I ⊂ B) (hB' : M.base B') : 
--   ∃ e ∈ B' \ I, M.indep (insert e I) :=
-- (hB.indep.subset hIB.subset).exists_insert_of_not_base 
--     (λ hI, hIB.ne (hI.eq_of_subset_base hB hIB.subset)) hB'

-- theorem base.base_of_basis_supset (hB : M.base B) (hBX : B ⊆ X) (hIX : M.basis I X) : M.base I :=
-- begin
--   by_contra h, 
--   obtain ⟨e,heBI,he⟩ := hIX.indep.exists_insert_of_not_base h hB, 
--   exact heBI.2 (hIX.mem_of_insert_indep (hBX heBI.1) he), 
-- end 

-- theorem base.basis_of_subset (hX : X ⊆ M.E . ssE) (hB : M.base B) (hBX : B ⊆ X) : M.basis B X :=
-- begin
--   rw [basis_iff, and_iff_right hB.indep, and_iff_right hBX], 
--   exact λ J hJ hBJ hJX, hB.eq_of_subset_indep hJ hBJ, 
-- end 

-- theorem indep.exists_base_subset_union_base (hI : M.indep I) (hB : M.base B) : 
--   ∃ B', M.base B' ∧ I ⊆ B' ∧ B' ⊆ I ∪ B :=
-- begin
--   obtain ⟨B', hB', hIB'⟩ := hI.subset_basis_of_subset (subset_union_left I B),  
--   exact ⟨B', hB.base_of_basis_supset (subset_union_right _ _) hB', hIB', hB'.subset⟩, 
-- end  

-- theorem eq_of_base_iff_base_forall {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E) 
-- (h : ∀ B ⊆ M₁.E, (M₁.base B ↔ M₂.base B)) : M₁ = M₂ :=
-- begin
--   apply Matroid.ext _ _ hE, 
--   ext B, 
--   refine ⟨λ h', (h _ h'.subset_ground).mp h', 
--     λ h', (h _ (h'.subset_ground.trans_eq hE.symm)).mpr h'⟩,
-- end 

-- theorem eq_of_indep_iff_indep_forall {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E) 
-- (h : ∀ I ⊆ M₁.E, (M₁.indep I ↔ M₂.indep I)) :
--   M₁ = M₂ :=
-- begin
--   refine eq_of_base_iff_base_forall hE (λ B hB, _), 
--   rw [base_iff_maximal_indep, base_iff_maximal_indep], 
--   split, 
--   { rintro ⟨hBi, hmax⟩, 
--     rw [←h _ hB, and_iff_right hBi],
--     refine λ I hI hBI, hmax I _ hBI, 
--     rwa h,  
--     rw [hE], 
--     exact hI.subset_ground },
--   rintro ⟨hBi, hmax⟩, 
--   rw [h _ hB, and_iff_right hBi], 
--   refine λ I hI hBI,  hmax I _ hBI, 
--   rwa ←h, 
--   exact hI.subset_ground, 
-- end

-- theorem eq_iff_indep_iff_indep_forall {M₁ M₂ : Matroid α} : 
--   M₁ = M₂ ↔ (M₁.E = M₂.E) ∧ ∀ I ⊆ M₁.E , M₁.indep I ↔ M₂.indep I :=
-- ⟨λ h, by { subst h, simp }, λ h, eq_of_indep_iff_indep_forall h.1 h.2⟩  


-- -- theorem eq_iff_indep_iff_indep_forall {M₁ M₂ : Matroid α} : M₁ = M₂ ↔ ∀ I, M₁.indep I ↔ M₂.indep I :=  
-- -- ⟨λ h I, by rw h, eq_of_indep_iff_indep_forall⟩  

-- -- theorem eq_iff_set_of_indep_eq_set_of_indep {M₁ M₂ : Matroid α} : 
-- --   M₁ = M₂ ↔ {I | M₁.indep I} = {I | M₂.indep I} :=
-- -- by { rw [eq_iff_indep_iff_indep_forall, set.ext_iff], refl }

-- end dep_indep


-- section from_axioms

-- def matroid_of_base {α : Type*} (E : Set α) (base : Set α → Prop) 
-- (exists_base : ∃ B, base B) (base_exchange : exchange_property base) 
-- (maximality : exists_maximal_subset_property (λ I, ∃ B, base B ∧ I ⊆ B))
-- (support : ∀ B, base B → B ⊆ E) : Matroid α := 
-- ⟨E, base, exists_base, base_exchange, maximality, support⟩

-- @[simp] theorem matroid_of_base_apply {α : Type*} (E : Set α) (base : Set α → Prop) 
-- (exists_base : ∃ B, base B) (base_exchange : exchange_property base) 
-- (maximality : exists_maximal_subset_property (λ I, ∃ B, base B ∧ I ⊆ B))
-- (support : ∀ B, base B → B ⊆ E) :
-- (matroid_of_base E base exists_base base_exchange maximality support).base = base := rfl 

-- /-- A collection of bases with the exchange property and at least one finite member is a matroid -/
-- def matroid_of_exists_finite_base {α : Type*} (E : Set α) (base : Set α → Prop) 
-- (exists_finite_base : ∃ B, base B ∧ B.Finite) (base_exchange : exchange_property base) 
-- (support : ∀ B, base B → B ⊆ E) : 
--   Matroid α := 
-- matroid_of_base E base (let ⟨B,h⟩ := exists_finite_base in ⟨B,h.1⟩) base_exchange
-- (begin
--   obtain ⟨B, hB, hfin⟩ := exists_finite_base,  
--   apply exists_maximal_subset_property_of_bounded ⟨B.ncard, _⟩,
--   rintro I ⟨B', hB', hIB'⟩,   
--   have hB'fin : B'.Finite, 
--   { rwa [finite_iff_finite_of_encard_eq_encard (encard_eq_of_exch base_exchange hB' hB)] },
--   rw [←encard_to_nat_eq B, encard_eq_of_exch base_exchange hB hB', encard_to_nat_eq], 
--   exact ⟨hB'fin.subset hIB', ncard_le_of_subset hIB' hB'fin⟩, 
-- end) 
-- support 

-- @[simp] theorem matroid_of_exists_finite_base_apply {α : Type*} (E : Set α) (base : Set α → Prop) 
-- (exists_finite_base : ∃ B, base B ∧ B.Finite) (base_exchange : exchange_property base) 
-- (support : ∀ B, base B → B ⊆ E) : 
-- (matroid_of_exists_finite_base E base exists_finite_base base_exchange support).base = base := rfl 

-- /-- A matroid constructed with a finite base is `Finite_rk` -/
-- instance {E : Set α} {base : Set α → Prop} {exists_finite_base : ∃ B, base B ∧ B.Finite} 
-- {base_exchange : exchange_property base} {support : ∀ B, base B → B ⊆ E} : 
--   Matroid.Finite_rk (matroid_of_exists_finite_base E base exists_finite_base base_exchange support) := 
-- ⟨exists_finite_base⟩  

-- def matroid_of_base_of_finite {E : Set α} (hE : E.Finite) (base : Set α → Prop)
-- (exists_base : ∃ B, base B) (base_exchange : exchange_property base)
-- (support : ∀ B, base B → B ⊆ E) : 
--   Matroid α :=
-- matroid_of_exists_finite_base E base (let ⟨B,hB⟩ := exists_base in ⟨B,hB, hE.subset (support _ hB)⟩) 
-- base_exchange support

-- @[simp] theorem matroid_of_base_of_finite_apply {E : Set α} (hE : E.Finite) (base : Set α → Prop)
-- (exists_base : ∃ B, base B) (base_exchange : exchange_property base)
-- (support : ∀ B, base B → B ⊆ E) : 
-- (matroid_of_base_of_finite hE base exists_base base_exchange support).base = base := rfl 

-- /-- A version of the independence axioms that avoids cardinality -/
-- def matroid_of_indep (E : Set α) (indep : Set α → Prop) (h_empty : indep ∅) 
-- (h_subset : ∀ ⦃I J⦄, indep J → I ⊆ J → indep I) 
-- (h_aug : ∀⦃I B⦄, indep I → I ∉ maximals (⊆) indep → B ∈ maximals (⊆) indep → 
--   ∃ x ∈ B \ I, indep (insert x I))
-- (h_maximal : exists_maximal_subset_property indep) 
-- (h_support : ∀ I, indep I → I ⊆ E) : 
--   Matroid α :=
-- matroid_of_base E (λ B, B ∈ maximals (⊆) indep)
-- (begin
--   obtain ⟨B, ⟨hB,-,-⟩, hB₁⟩ :=  h_maximal ∅ univ h_empty (subset_univ _),  
--   exact ⟨B, ⟨hB,λ B' hB' hBB', hB₁ ⟨hB', empty_subset _,subset_univ _⟩ hBB'⟩⟩,  
-- end)
-- (begin
--   rintros B B' ⟨hB,hBmax⟩ ⟨hB',hB'max⟩ e he, 
--   obtain ⟨f,hf,hfB⟩ :=  h_aug (h_subset hB (diff_subset B {e})) _ ⟨hB',hB'max⟩, 
--   simp only [mem_diff, mem_singleton_iff, not_and, not_not] at hf, 
--   have hfB' : f ∉ B, 
--   { intro hfB, have := hf.2 hfB, subst this, exact he.2 hf.1 }, 
--   { refine ⟨f, ⟨hf.1, hfB'⟩, by_contra (λ hnot, _)⟩,
--     obtain ⟨x,hxB, hind⟩ :=  h_aug hfB hnot ⟨hB, hBmax⟩, 
--     simp only [mem_diff, mem_insert_iff, mem_singleton_iff, not_or_distrib, not_and, not_not] 
--       at hxB, 
--     have := hxB.2.2 hxB.1, subst this, 
--     rw [insert_comm, insert_diff_singleton, insert_eq_of_mem he.1] at hind, 
--     exact not_mem_subset (hBmax hind (subset_insert _ _)) hfB' (mem_insert _ _) },
--   simp only [maximals, mem_sep_iff, diff_singleton_subset_iff, not_and, not_forall, exists_prop],
--   exact λ _, ⟨B, hB, subset_insert _ _, λ hss, (hss he.1).2 rfl⟩, 
-- end)
-- (begin
--   rintro I X ⟨B, hB,  hIB⟩ hIX, 
--   obtain ⟨J, ⟨hJ, hIJ, hJX⟩, hJmax⟩ := h_maximal I X (h_subset hB.1 hIB) hIX, 
--   obtain ⟨BJ, hBJ⟩ := h_maximal J univ hJ (subset_univ _), 
--   refine ⟨J, ⟨⟨BJ,_, hBJ.1.2.1⟩ ,hIJ,hJX⟩, _⟩,  
--   { exact ⟨hBJ.1.1, λ B' hB' hBJB', hBJ.2 ⟨hB',hBJ.1.2.1.trans hBJB', subset_univ _⟩ hBJB'⟩ },
--   simp only [mem_set_of_eq, and_imp, forall_exists_index], 
--   rintro A B' ⟨(hB'i : indep _), hB'max⟩ hB'' hIA hAX hJA, 
--   exact hJmax ⟨h_subset hB'i hB'', hIA, hAX⟩ hJA,
-- end )
-- (λ B hB, h_support B hB.1)

-- @[simp] theorem matroid_of_indep_apply (E : Set α) (indep : Set α → Prop) (h_empty : indep ∅) 
-- (h_subset : ∀ ⦃I J⦄, indep J → I ⊆ J → indep I) 
-- (h_aug : ∀⦃I B⦄, indep I → I ∉ maximals (⊆) indep → B ∈ maximals (⊆) indep → 
--   ∃ x ∈ B \ I, indep (insert x I))
-- (h_maximal : exists_maximal_subset_property indep) 
-- (h_support : ∀ I, indep I → I ⊆ E)  : 
-- (matroid_of_indep E indep h_empty h_subset h_aug h_maximal h_support).indep = indep :=
-- begin
--   ext I, 
--   simp only [Matroid.indep, matroid_of_indep], 
--   refine ⟨λ ⟨B, hB, hIB⟩, h_subset hB.1 hIB, λ hI, _⟩, 
--   obtain ⟨B, ⟨hB, hIB, -⟩, hBmax⟩ :=  h_maximal I univ hI (subset_univ _), 
--   exact ⟨B, ⟨hB, λ B' hB' hBB', hBmax ⟨hB', hIB.trans hBB', subset_univ _⟩ hBB'⟩, hIB⟩, 
-- end 

-- /-- If there is an absolute upper bound on the size of an independent set, then the maximality axiom isn't needed to define a matroid by independent sets. -/
-- def matroid_of_indep_of_bdd (E : Set α) (indep : Set α → Prop) (h_empty : indep ∅) 
-- (h_subset : ∀ ⦃I J⦄, indep J → I ⊆ J → indep I) 
-- (h_aug : ∀⦃I B⦄, indep I → I ∉ maximals (⊆) indep → B ∈ maximals (⊆) indep → 
--   ∃ x ∈ B \ I, indep (insert x I))
-- (h_bdd : ∃ n, ∀ I, indep I → I.Finite ∧ I.ncard ≤ n )
-- (h_support : ∀ I, indep I → I ⊆ E) : Matroid α :=
-- matroid_of_indep E indep h_empty h_subset h_aug (exists_maximal_subset_property_of_bounded h_bdd) 
-- h_support 

-- @[simp] theorem matroid_of_indep_of_bdd_apply (E : Set α) (indep : Set α → Prop) (h_empty : indep ∅) 
-- (h_subset : ∀ ⦃I J⦄, indep J → I ⊆ J → indep I) 
-- (h_aug : ∀⦃I B⦄, indep I → I ∉ maximals (⊆) indep → B ∈ maximals (⊆) indep → 
--   ∃ x ∈ B \ I, indep (insert x I))
-- (h_bdd : ∃ n, ∀ I, indep I → I.Finite ∧ I.ncard ≤ n ) 
-- (h_support : ∀ I, indep I → I ⊆ E) : 
-- (matroid_of_indep_of_bdd E indep h_empty h_subset h_aug h_bdd h_support).indep = indep := 
-- by simp [matroid_of_indep_of_bdd]

-- instance (E : Set α) (indep : Set α → Prop) (h_empty : indep ∅) 
-- (h_subset : ∀ ⦃I J⦄, indep J → I ⊆ J → indep I) 
-- (h_aug : ∀⦃I B⦄, indep I → I ∉ maximals (⊆) indep → B ∈ maximals (⊆) indep → 
--   ∃ x ∈ B \ I, indep (insert x I)) (h_bdd : ∃ n, ∀ I, indep I → I.Finite ∧ I.ncard ≤ n ) 
-- (h_support : ∀ I, indep I → I ⊆ E) : 
-- Matroid.Finite_rk (matroid_of_indep_of_bdd E indep h_empty h_subset h_aug h_bdd h_support) := 
-- begin
--   obtain ⟨B, hB⟩ := 
--     (matroid_of_indep_of_bdd E indep h_empty h_subset h_aug h_bdd h_support).exists_base, 
--   obtain ⟨h, h_bdd⟩ := h_bdd,  
--   refine hB.Finite_rk_of_finite (h_bdd B _).1,
--   rw [←matroid_of_indep_of_bdd_apply E indep, Matroid.indep], 
--   exact ⟨_, hB, subset.rfl⟩,  
-- end 

-- def matroid_of_indep_of_bdd' (E : Set α) (indep : Set α → Prop) (h_empty : indep ∅) 
-- (h_subset : ∀ ⦃I J⦄, indep J → I ⊆ J → indep I) 
-- (ind_aug : ∀ ⦃I J⦄, indep I → indep J → I.ncard < J.ncard →
--   ∃ e ∈ J, e ∉ I ∧ indep (insert e I)) (h_bdd : ∃ n, ∀ I, indep I → I.Finite ∧ I.ncard ≤ n )
-- (h_support : ∀ I, indep I → I ⊆ E) : Matroid α :=
-- matroid_of_indep_of_bdd E indep h_empty h_subset 
-- (begin
--   intros I J hI hIn hJ, 
--   by_contra' h', 
--   obtain (hlt | hle) := lt_or_le I.ncard J.ncard, 
--   { obtain ⟨e,heJ,heI, hi⟩ :=  ind_aug hI hJ.1 hlt, 
--     exact h' e ⟨heJ,heI⟩ hi },
--   obtain (h_eq | hlt) := hle.eq_or_lt, 
--   { refine hIn ⟨hI, λ K (hK : indep K) hIK, hIK.ssubset_or_eq.elim (λ hss, _) 
--       (λ h, h.symm.subset)⟩,
--     obtain ⟨f, hfK, hfJ, hi⟩ := ind_aug hJ.1 hK (h_eq.trans_lt (ncard_lt_ncard hss _)), 
--     { exact (hfJ (hJ.2 hi (subset_insert _ _) (mem_insert f _))).elim },
--     obtain ⟨n, hn⟩ := h_bdd, 
--     exact (hn K hK).1 },
--   obtain ⟨e,heI, heJ, hi⟩ := ind_aug hJ.1 hI hlt, 
--     exact heJ (hJ.2 hi (subset_insert _ _) (mem_insert e _)), 
-- end) h_bdd h_support 

-- @[simp] theorem matroid_of_indep_of_bdd'_apply (E : Set α) (indep : Set α → Prop) (h_empty : indep ∅) 
-- (h_subset : ∀ ⦃I J⦄, indep J → I ⊆ J → indep I) 
-- (ind_aug : ∀ ⦃I J⦄, indep I → indep J → I.ncard < J.ncard →
--   ∃ e ∈ J, e ∉ I ∧ indep (insert e I)) (h_bdd : ∃ n, ∀ I, indep I → I.Finite ∧ I.ncard ≤ n )
-- (h_support : ∀ I, indep I → I ⊆ E) : 
-- (matroid_of_indep_of_bdd' E indep h_empty h_subset ind_aug h_bdd h_support).indep = indep :=
-- by simp [matroid_of_indep_of_bdd']

-- /-- A collection of sets in a finite type satisfying the usual independence axioms determines a matroid -/
-- def matroid_of_indep_of_finite {E : Set α} (hE : E.Finite) (indep : Set α → Prop)
-- (h_empty : indep ∅)
-- (ind_mono : ∀ ⦃I J⦄, indep J → I ⊆ J → indep I)
-- (ind_aug : ∀ ⦃I J⦄, indep I → indep J → I.ncard < J.ncard → ∃ e ∈ J, e ∉ I ∧ indep (insert e I)) 
-- (h_support : ∀ ⦃I⦄, indep I → I ⊆ E) :
--   Matroid α := 
-- matroid_of_indep_of_bdd' E indep h_empty ind_mono ind_aug 
--   ⟨E.ncard, λ I hI, ⟨hE.subset (h_support hI), ncard_le_of_subset (h_support hI) hE⟩⟩ h_support 

-- @[simp] theorem matroid_of_indep_of_finite_apply {E : Set α} (hE : E.Finite) (indep : Set α → Prop)
-- (h_empty : indep ∅)
-- (ind_mono : ∀ ⦃I J⦄, indep J → I ⊆ J → indep I)
-- (ind_aug : ∀ ⦃I J⦄, indep I → indep J → I.ncard < J.ncard → ∃ e ∈ J, e ∉ I ∧ indep (insert e I)) 
-- (h_support : ∀ ⦃I⦄, indep I → I ⊆ E) :
--   (matroid_of_indep_of_finite hE indep h_empty ind_mono ind_aug h_support).indep = indep :=
-- by simp [matroid_of_indep_of_finite]

-- end from_axioms 

-- section dual

-- /-- This is really an order-theory theorem. Not clear where to put it, though.  -/
-- theorem base_compl_iff_mem_maximals_disjoint_base : 
--   M.base Bᶜ ↔ B ∈ maximals (⊆) {I | ∃ B, M.base B ∧ disjoint I B} :=
-- begin
--   simp_rw ←subset_compl_iff_disjoint_left, 
--   refine ⟨λ h, ⟨⟨Bᶜ,h,subset.rfl⟩, _⟩, _⟩,
--   { rintro X ⟨B', hB', hXB'⟩ hBX, 
--     rw [←compl_subset_compl] at ⊢ hBX,
--     rwa ←hB'.eq_of_subset_base h (hXB'.trans hBX) },
--   rintro ⟨⟨B',hB',hBB'⟩,h⟩, 
--   rw subset_compl_comm at hBB', 
--   rwa [hBB'.antisymm (h ⟨_, hB', _⟩ hBB'), compl_compl],   
--   rw compl_compl, 
-- end 

-- theorem base_compl_iff_mem_maximals_disjoint_base' (hB : B ⊆ M.E . ssE) : 
--   M.base (M.E \ B) ↔ B ∈ maximals (⊆) {I | I ⊆ M.E ∧ ∃ B, M.base B ∧ disjoint I B} := 
-- begin
--   refine ⟨λ h, ⟨⟨hB,_,h,disjoint_sdiff_right⟩,_⟩, λ h, _⟩, 
--   { rintro X ⟨hXE,B', hB', hXB'⟩ hBX,
--     rw [hB'.eq_of_subset_base h (subset_diff.mpr ⟨hB'.subset_ground,_⟩), 
--       ←subset_compl_iff_disjoint_right, diff_eq, compl_inter, compl_compl] at hXB', 
--     { refine (subset_inter hXE hXB').trans _, 
--       rw [inter_distrib_left, inter_compl_self, empty_union],
--       exact inter_subset_right _ _ },
--     exact (disjoint_of_subset_left hBX hXB').symm },
--   obtain ⟨⟨-, B', hB', hIB'⟩, h⟩ := h, 
--   suffices : B' = M.E \ B, rwa ←this, 
--   rw [subset_antisymm_iff, subset_diff, disjoint.comm, and_iff_left hIB', 
--     and_iff_right hB'.subset_ground, diff_subset_iff], 

--   intros e he, 
--   rw [mem_union, or_iff_not_imp_right], 
--   intros heB', 
--   refine h ⟨insert_subset.mpr ⟨he, hB⟩, ⟨B', hB', _⟩⟩ 
--     (subset_insert _ _) (mem_insert e B), 
--   rw [←union_singleton, disjoint_union_left, disjoint_singleton_left], 
--   exact ⟨hIB', heB'⟩, 
-- end 

-- def dual (M : Matroid α) : Matroid α := 
-- matroid_of_indep M.E (λ I, I ⊆ M.E ∧ ∃ B, M.base B ∧ disjoint I B) 
-- ⟨empty_subset M.E, M.exists_base.imp (λ B hB, ⟨hB, empty_disjoint _⟩)⟩ 
-- (begin
--   rintro I J ⟨hJE, B, hB, hJB⟩ hIJ, 
--   exact ⟨hIJ.trans hJE, ⟨B, hB, disjoint_of_subset_left hIJ hJB⟩⟩, 
-- end) 
-- (begin
--   rintro I X ⟨hIE, B, hB, hIB⟩ hI_not_max hX_max,  
--   have hXE := hX_max.1.1, 
--   have hB' := (base_compl_iff_mem_maximals_disjoint_base' hXE).mpr hX_max,
  
--   set B' := M.E \ X with hX, 
--   have hI := (not_iff_not.mpr (base_compl_iff_mem_maximals_disjoint_base')).mpr hI_not_max, 
--   obtain ⟨B'', hB'', hB''₁, hB''₂⟩ := (hB'.indep.diff I).exists_base_subset_union_base hB, 
--   rw [←compl_subset_compl, ←hIB.sdiff_eq_right, ←union_diff_distrib, diff_eq, compl_inter, 
--     compl_compl, union_subset_iff, compl_subset_compl] at hB''₂, 
  
--   have hssu := (subset_inter (hB''₂.2) hIE).ssubset_of_ne 
--     (by { rintro rfl, apply hI, convert hB'', simp }),
--   obtain ⟨e, ⟨(heB'' : e ∉ _), heE⟩, heI⟩ := exists_of_ssubset hssu, 
--   use e, 
--   rw [mem_diff, insert_subset, and_iff_left heI, and_iff_right heE, and_iff_right hIE], 
--   refine ⟨by_contra (λ heX, heB'' (hB''₁ ⟨_, heI⟩)), ⟨B'', hB'', _⟩⟩, 
--   { rw [hX], exact ⟨heE, heX⟩ },
--   rw [←union_singleton, disjoint_union_left, disjoint_singleton_left, and_iff_left heB''], 
--   exact disjoint_of_subset_left hB''₂.2 disjoint_compl_left,
-- end) 
-- (begin
--   rintro I' X ⟨hI'E, B, hB, hI'B⟩ hI'X, 
--   obtain ⟨I, hI⟩ :=  M.exists_basis (M.E \ X) ,
--   obtain ⟨B', hB', hIB', hB'IB⟩ := hI.indep.exists_base_subset_union_base hB, 
--   refine ⟨(X \ B') ∩ M.E, 
--     ⟨_,subset_inter (subset_diff.mpr _) hI'E, (inter_subset_left _ _).trans (diff_subset _ _)⟩, _⟩, 
--   { simp only [inter_subset_right, true_and], 
--     exact ⟨B', hB', disjoint_of_subset_left (inter_subset_left _ _) disjoint_sdiff_left⟩ },
--   { rw [and_iff_right hI'X],
--     refine disjoint_of_subset_right hB'IB _, 
--     rw [disjoint_union_right, and_iff_left hI'B], 
--     exact disjoint_of_subset hI'X hI.subset disjoint_sdiff_right },
--   simp only [mem_set_of_eq, subset_inter_iff, and_imp, forall_exists_index], 
--   intros J hJE B'' hB'' hdj hI'J hJX hssJ,
--   rw [and_iff_left hJE],  
--   rw [diff_eq, inter_right_comm, ←diff_eq, diff_subset_iff] at hssJ, 
  
--   have hI' : (B'' ∩ X) ∪ (B' \ X) ⊆ B',
--   { rw [union_subset_iff, and_iff_left (diff_subset _ _),
--      ←inter_eq_self_of_subset_left hB''.subset_ground, inter_right_comm, inter_assoc],
--     calc _ ⊆ _ : inter_subset_inter_right _ hssJ 
--        ... ⊆ _ : by rw [inter_distrib_left, hdj.symm.inter_eq, union_empty] 
--        ... ⊆ _ : inter_subset_right _ _ },
  
--   obtain ⟨B₁,hB₁,hI'B₁,hB₁I⟩ := (hB'.indep.subset hI').exists_base_subset_union_base hB'',
--   rw [union_comm, ←union_assoc, union_eq_self_of_subset_right (inter_subset_left _ _)] at hB₁I, 
  
--   have : B₁ = B', 
--   { refine hB₁.eq_of_subset_indep hB'.indep (λ e he, _), 
--     refine (hB₁I he).elim (λ heB'',_) (λ h, h.1), 
--     refine (em (e ∈ X)).elim (λ heX, hI' (or.inl ⟨heB'', heX⟩)) (λ heX, hIB' _), 
--     refine hI.mem_of_insert_indep ⟨hB₁.subset_ground he, heX⟩ 
--       (hB₁.indep.subset (insert_subset.mpr ⟨he, _⟩)), 
--     refine (subset_union_of_subset_right (subset_diff.mpr ⟨hIB',_⟩) _).trans hI'B₁, 
--     refine disjoint_of_subset_left hI.subset disjoint_sdiff_left }, 

--   subst this, 

--   refine subset_diff.mpr ⟨hJX, by_contra (λ hne, _)⟩, 
--   obtain ⟨e, heJ, heB'⟩ := not_disjoint_iff.mp hne,
--   obtain (heB'' | ⟨heB₁,heX⟩ ) := hB₁I heB', 
--   { exact hdj.ne_of_mem heJ heB'' rfl },
--   exact heX (hJX heJ), 
-- end) 
-- (by tauto)

-- /-- A notation typeclass for matroid duality, denoted by the `﹡` symbol. -/
-- @[class] structure has_matroid_dual (β : Type*) := (dual : β → β)

-- postfix `﹡`:(max+1) := has_matroid_dual.dual 

-- instance Matroid_dual {α : Type*} : has_matroid_dual (Matroid α) := ⟨Matroid.dual⟩ 

-- theorem dual_indep_iff_exists' : (M﹡.indep I) ↔ I ⊆ M.E ∧ (∃ B, M.base B ∧ disjoint I B) := 
-- by simp [has_matroid_dual.dual, dual]

-- theorem dual_indep_iff_exists (hI : I ⊆ M.E . ssE) : 
--   (M﹡.indep I) ↔ (∃ B, M.base B ∧ disjoint I B) := 
-- by rw [dual_indep_iff_exists', and_iff_right hI]

-- @[simp] theorem dual_ground : M﹡.E = M.E := rfl 

-- theorem dual_dep_iff_forall : (M﹡.dep I) ↔ I ⊆ M.E ∧ ∀ B, M.base B → (I ∩ B).nonempty :=
-- begin
--   simp_rw [dep_iff, dual_indep_iff_exists', and_comm, dual_ground, and.congr_right_iff, not_and, 
--     not_exists, not_and, not_disjoint_iff_nonempty_inter], 
--   exact λ hIE, by rw [imp_iff_right hIE], 
-- end   

-- instance dual_finite [M.Finite] : M﹡.Finite := 
-- ⟨M.ground_finite⟩  

-- theorem set.subset_ground_dual (hX : X ⊆ M.E) : X ⊆ M﹡.E := hX 

-- theorem dual_base_iff (hB : B ⊆ M.E . ssE) : M﹡.base B ↔ M.base (M.E \ B) := 
-- begin
--   rw [base_compl_iff_mem_maximals_disjoint_base', base_iff_maximal_indep, dual_indep_iff_exists', 
--     mem_maximals_set_of_iff],
--   simp [dual_indep_iff_exists'],
-- end 

-- theorem dual_base_iff' : M﹡.base B ↔ M.base (M.E \ B) ∧ B ⊆ M.E := 
-- begin
--   obtain (h | h) := em (B ⊆ M.E), 
--   { rw [dual_base_iff, and_iff_left h] },
--   rw [iff_false_intro h, and_false, iff_false], 
--   exact λ h', h h'.subset_ground,  
-- end  

-- theorem base.compl_base_of_dual (h : M﹡.base B) : M.base (M.E \ B) := 
-- (dual_base_iff (by { exact h.subset_ground })).mp h

-- @[simp] theorem dual_dual (M : Matroid α) : M﹡﹡ = M := 
-- begin
--   refine eq_of_base_iff_base_forall rfl (λ B hB, _), 
--   rw [dual_base_iff, dual_base_iff], 
--   rw [dual_ground] at *, 
--   simp only [sdiff_sdiff_right_self, inf_eq_inter, ground_inter_right], 
-- end 

-- theorem dual_indep_iff_coindep : M﹡.indep X ↔ M.coindep X := dual_indep_iff_exists'

-- theorem base.compl_base_dual (hB : M.base B) : M﹡.base (M.E \ B) := 
-- by { haveI := fact.mk hB.subset_ground, simpa [dual_base_iff] }

-- theorem base.compl_inter_basis_of_inter_basis (hB : M.base B) (hBX : M.basis (B ∩ X) X) :
--   M﹡.basis ((M.E \ B) ∩ (M.E \ X)) (M.E \ X) := 
-- begin
--   rw basis_iff, 
--   refine ⟨(hB.compl_base_dual.indep.subset (inter_subset_left _ _)), inter_subset_right _ _, 
--     λ J hJ hBCJ hJX, hBCJ.antisymm (subset_inter _ hJX)⟩, 
  
--   obtain ⟨-, B', hB', hJB'⟩ := dual_indep_iff_coindep.mp hJ, 

--   obtain ⟨B'', hB'', hsB'', hB''s⟩  := hBX.indep.exists_base_subset_union_base hB', 
--   have hB'ss : B' ⊆ B ∪ X, 
--   { rw [←diff_subset_diff_iff M.E (by ssE : B ∪ X ⊆ M.E) hB'.subset_ground, subset_diff,
--       and_iff_right (diff_subset _ _)],
--     rw [diff_inter_diff] at hBCJ, 
--     exact disjoint_of_subset_left hBCJ hJB' },
  
--   have hB''ss : B'' ⊆ B, 
--   { refine λ e he, (hB''s he).elim and.left (λ heB', (hB'ss heB').elim id (λ heX, _)), 
--      exact (hBX.mem_of_insert_indep heX (hB''.indep.subset (insert_subset.mpr ⟨he,hsB''⟩))).1 }, 
  
--   have := (hB''.eq_of_subset_indep hB.indep hB''ss).symm, subst this,
--   rw subset_diff at *, 
--   exact ⟨hJX.1, disjoint_of_subset_right hB''s (disjoint_union_right.mpr 
--     ⟨disjoint_of_subset_right (inter_subset_right _ _) hJX.2, hJB'⟩)⟩, 
-- end 

-- theorem base.inter_basis_iff_compl_inter_basis_dual (hB : M.base B) (hX : X ⊆ M.E . ssE): 
--   M.basis (B ∩ X) X ↔ M﹡.basis ((M.E \ B) ∩ (M.E \ X)) (M.E \ X) :=
-- begin
--   refine ⟨hB.compl_inter_basis_of_inter_basis, λ h, _⟩, 
--   simpa using hB.compl_base_dual.compl_inter_basis_of_inter_basis h, 
-- end 
  
-- theorem dual_inj {M₁ M₂ : Matroid α} (h : M₁﹡ = M₂﹡) : M₁ = M₂ :=
-- by rw [←dual_dual M₁, h, dual_dual]

-- @[simp] theorem dual_inj_iff {M₁ M₂ : Matroid α} : M₁﹡ = M₂﹡ ↔ M₁ = M₂ := ⟨dual_inj, congr_arg _⟩

-- theorem eq_dual_comm {M₁ M₂ : Matroid α} : M₁ = M₂﹡ ↔ M₂ = M₁﹡ := 
-- by rw [←dual_inj_iff, dual_dual, eq_comm]

-- theorem dual_eq_comm {M₁ M₂ : Matroid α} : M₁﹡ = M₂ ↔ M₂﹡ = M₁ := 
-- by rw [←dual_inj_iff, dual_dual, eq_comm]

-- theorem coindep_iff_exists (hX : X ⊆ M.E . ssE) : M.coindep X ↔ ∃ B, M.base B ∧ disjoint X B := 
-- by rw [coindep, and_iff_right hX]

-- theorem coindep.exists_disjoint_base (hX : M.coindep X) : ∃ B, M.base B ∧ disjoint X B := hX.2

-- theorem coindep.base_of_basis_compl (hX : M.coindep X) (hB : M.basis B Xᶜ) : M.base B :=
-- begin
--   obtain ⟨B',hB'⟩ := hX.exists_disjoint_base, 
--   exact hB'.1.base_of_basis_supset (subset_compl_iff_disjoint_left.mpr hB'.2) hB, 
-- end 

-- theorem base_iff_dual_base_compl (hB : B ⊆ M.E . ssE) : M.base B ↔ M﹡.base (M.E \ B) :=
-- by simp [dual_base_iff]

-- end dual 

-- end Matroid 
