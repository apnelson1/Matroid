import Mathlib.Data.Set.Finite
import Matroid.ForMathlib.encard_stuff
import Mathlib.Order.Minimal
import Matroid.Init
import Matroid.ForMathlib.Minimal

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
  `Base` of `M`. -/
@[ext] structure Matroid (α : Type _) where
  (ground : Set α)
  (Base : Set α → Prop)
  (exists_Base' : ∃ B, Base B)
  (Base_exchange' : Matroid.exchange_property Base)
  (maximality' : ∀ X, X ⊆ ground → 
    Matroid.exists_maximal_subset_property (fun I ↦ ∃ B, Base B ∧ I ⊆ B) X)
  (subset_ground' : ∀ B, Base B → B ⊆ ground)
  
namespace Matroid

variable {α : Type _} {M : Matroid α} 
--{I D J B B' B₁ B₂ X Y : Set α} {e f : α}

section exchange

/-- A family of sets with the exchange property is an antichain. -/
theorem antichain_of_exch {Base : Set α → Prop} (exch : exchange_property Base) 
    (hB : Base B) (hB' : Base B') (h : B ⊆ B') : B = B' := 
  h.antisymm (fun x hx ↦ by_contra 
    (fun hxB ↦ by obtain ⟨y, hy, -⟩ := exch B' B hB' hB x ⟨hx, hxB⟩; exact hy.2 $ h hy.1))

theorem encard_diff_le_aux {Base : Set α → Prop} (exch : exchange_property Base) 
    {B₁ B₂ : Set α} (hB₁ : Base B₁) (hB₂ : Base B₂) : (B₁ \ B₂).encard ≤ (B₂ \ B₁).encard := by
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
theorem encard_diff_eq_of_exch {Base : Set α → Prop} (exch : exchange_property Base)
    (hB₁ : Base B₁) (hB₂ : Base B₂) : (B₁ \ B₂).encard = (B₂ \ B₁).encard := 
(encard_diff_le_aux exch hB₁ hB₂).antisymm (encard_diff_le_aux exch hB₂ hB₁)

/-- Any two sets `B₁,B₂` in a family with the exchange property have the same `ℕ∞`-cardinality. -/
theorem encard_Base_eq_of_exch {Base : Set α → Prop} (exch : exchange_property Base)
    (hB₁ : Base B₁) (hB₂ : Base B₂) : B₁.encard = B₂.encard := by 
rw [←encard_diff_add_encard_inter B₁ B₂, encard_diff_eq_of_exch exch hB₁ hB₂, inter_comm, 
     encard_diff_add_encard_inter]

end exchange

section defs

/-- We write `M.E` for the ground set of a matroid `M`-/
def E (M : Matroid α) : Set α := M.ground

@[simp] theorem ground_eq_E (M : Matroid α) : M.ground = M.E := rfl 

/-- A set is Independent if it is contained in a Base.  -/
def Indep (M : Matroid α) (I : Set α) : Prop := ∃ B, M.Base B ∧ I ⊆ B

/-- A subset of `M.E` is Dependent if it is not Independent . -/
def Dep (M : Matroid α) (D : Set α) : Prop := ¬M.Indep D ∧ D ⊆ M.E   

/-- A Basis for a set `X ⊆ M.E` is a maximal Independent subset of `X`
  (Often in the literature, the word 'Basis' is used to refer to what we call a 'Base'). -/
def Basis (M : Matroid α) (I X : Set α) : Prop := 
  I ∈ maximals (· ⊆ ·) {A | M.Indep A ∧ A ⊆ X} ∧ X ⊆ M.E  

/-- A Circuit is a minimal Dependent set -/
def Circuit (M : Matroid α) (C : Set α) : Prop := C ∈ minimals (· ⊆ ·) {X | M.Dep X}

/-- A Coindependent set is a subset of `M.E` that is disjoint from some Base -/
def Coindep (M : Matroid α) (I : Set α) : Prop := (∃ B, M.Base B ∧ Disjoint I B) ∧ I ⊆ M.E

end defs

/-- Typeclass for a matroid having finite ground set. This is just a wrapper for `[M.E.Finite]`-/
class Finite (M : Matroid α) : Prop := (ground_finite : M.E.Finite)

theorem ground_Finite (M : Matroid α) [M.Finite] : M.E.Finite := ‹M.Finite›.ground_finite   

theorem Set_Finite (M : Matroid α) [M.Finite] (X : Set α) (hX : X ⊆ M.E := by aesop) : X.Finite :=
  M.ground_Finite.subset hX 

instance Finite_of_Finite [@_root_.Finite α] {M : Matroid α} : Finite M := 
  ⟨Set.toFinite _⟩ 

/-- A `Finite_rk` matroid is one with a finite Basis -/
class Finite_rk (M : Matroid α) : Prop := (exists_finite_Base : ∃ B, M.Base B ∧ B.Finite) 

instance Finite_rk_of_finite (M : Matroid α) [Finite M] : Finite_rk M := 
  ⟨ M.exists_Base'.imp (fun B hB ↦ ⟨hB, M.Set_Finite B (M.subset_ground' _ hB)⟩) ⟩ 

/-- An `Infinite_rk` matroid is one whose Bases are infinite. -/
class Infinite_rk (M : Matroid α) : Prop := (exists_infinite_Base : ∃ B, M.Base B ∧ B.Infinite)

/-- A `Finitary` matroid is one whose Circuits are finite -/
class Finitary (M : Matroid α) : Prop := (cct_finite : ∀ (C : Set α), M.Circuit C → C.Finite) 

/-- A `Rk_pos` matroid is one in which the empty set is not a Basis -/
class Rk_pos (M : Matroid α) : Prop := (empty_not_Base : ¬M.Base ∅)

section aesop

/-- The `aesop_mat` tactic attempts to prove a set is contained in the ground set of a matroid. 
  It uses a `[Matroid]` ruleset, and is allowed to fail. -/
macro (name := aesop_mat) "aesop_mat" c:Aesop.tactic_clause* : tactic =>
`(tactic|
  aesop $c* (options := { terminal := true })
  (rule_sets [$(Lean.mkIdent `Matroid):ident]))

@[aesop unsafe 10% (rule_sets [Matroid])] 
private theorem inter_right_subset_ground (hX : X ⊆ M.E) : 
    X ∩ Y ⊆ M.E := (inter_subset_left _ _).trans hX 

@[aesop unsafe 10% (rule_sets [Matroid])]
private theorem inter_left_subset_ground (hX : X ⊆ M.E) :
    Y ∩ X ⊆ M.E := (inter_subset_right _ _).trans hX 

@[aesop unsafe 10% (rule_sets [Matroid])]
private theorem diff_subset_ground (hX : X ⊆ M.E) : X \ Y ⊆ M.E :=      
  (diff_subset _ _).trans hX 

@[aesop unsafe 10% (rule_sets [Matroid])]
private theorem ground_diff_subset_ground : M.E \ X ⊆ M.E :=
  diff_subset_ground rfl.subset 

@[aesop unsafe 10% (rule_sets [Matroid])]
private theorem singleton_subset_ground (he : e ∈ M.E) : {e} ⊆ M.E := 
  singleton_subset_iff.mpr he

@[aesop unsafe 10% (rule_sets [Matroid])]
private theorem subset_ground_of_subset (hXY : X ⊆ Y) (hY : Y ⊆ M.E) : X ⊆ M.E := 
  hXY.trans hY

@[aesop safe (rule_sets [Matroid])]
private theorem insert_subset_ground {e : α} {X : Set α} {M : Matroid α} 
    (he : e ∈ M.E) (hX : X ⊆ M.E) : insert e X ⊆ M.E := 
    insert_subset.mpr ⟨he, hX⟩ 
   
attribute [aesop safe (rule_sets [Matroid])] empty_subset union_subset 


end aesop
section Base

@[aesop unsafe 10% (rule_sets [Matroid])]
theorem Base.subset_ground (hB : M.Base B) : B ⊆ M.E :=
  M.subset_ground' B hB 

theorem exists_Base (M : Matroid α) : ∃ B, M.Base B := M.exists_Base'

theorem Base.exchange (hB₁ : M.Base B₁) (hB₂ : M.Base B₂) (hx : e ∈ B₁ \ B₂) :
    ∃ y ∈ B₂ \ B₁, M.Base (insert y (B₁ \ {e}))  :=
  M.Base_exchange' B₁ B₂ hB₁ hB₂ _ hx

theorem Base.exchange_mem (hB₁ : M.Base B₁) (hB₂ : M.Base B₂) (hxB₁ : e ∈ B₁) (hxB₂ : e ∉ B₂) :
    ∃ y, (y ∈ B₂ ∧ y ∉ B₁) ∧ M.Base (insert y (B₁ \ {e})) :=
  by simpa using hB₁.exchange hB₂ ⟨hxB₁, hxB₂⟩

theorem Base.eq_of_subset_Base (hB₁ : M.Base B₁) (hB₂ : M.Base B₂) (hB₁B₂ : B₁ ⊆ B₂) :
    B₁ = B₂ :=
  antichain_of_exch M.Base_exchange' hB₁ hB₂ hB₁B₂

theorem Base.encard_diff_comm (hB₁ : M.Base B₁) (hB₂ : M.Base B₂) :
    (B₁ \ B₂).encard = (B₂ \ B₁).encard :=
  encard_diff_eq_of_exch (M.Base_exchange') hB₁ hB₂ 

theorem Base.card_diff_comm (hB₁ : M.Base B₁) (hB₂ : M.Base B₂) :
    (B₁ \ B₂).ncard = (B₂ \ B₁).ncard := by
  rw [←encard_toNat_eq, hB₁.encard_diff_comm hB₂, encard_toNat_eq]

theorem Base.encard_eq_encard_of_Base (hB₁ : M.Base B₁) (hB₂ : M.Base B₂) :
    B₁.encard = B₂.encard := by
  rw [encard_Base_eq_of_exch M.Base_exchange' hB₁ hB₂]

theorem Base.card_eq_card_of_Base (hB₁ : M.Base B₁) (hB₂ : M.Base B₂) : B₁.ncard = B₂.ncard := by
  rw [←encard_toNat_eq B₁, hB₁.encard_eq_encard_of_Base hB₂, encard_toNat_eq]

theorem Base.Finite_of_Finite (hB : M.Base B) (h : B.Finite) (hB' : M.Base B') : B'.Finite :=
  (Finite_iff_Finite_of_encard_eq_encard (hB.encard_eq_encard_of_Base hB')).mp h  

theorem Base.Infinite_of_Infinite (hB : M.Base B) (h : B.Infinite) (hB₁ : M.Base B₁) :
    B₁.Infinite :=
  by_contra (fun hB_inf ↦ (hB₁.Finite_of_Finite (not_infinite.mp hB_inf) hB).not_infinite h)

theorem Base.Finite [Finite_rk M] (hB : M.Base B) : B.Finite := 
  let ⟨B₀,hB₀⟩ := ‹Finite_rk M›.exists_finite_Base
  hB₀.1.Finite_of_Finite hB₀.2 hB

theorem Base.Infinite [Infinite_rk M] (hB : M.Base B) : B.Infinite :=
  let ⟨B₀,hB₀⟩ := ‹Infinite_rk M›.exists_infinite_Base
  hB₀.1.Infinite_of_Infinite hB₀.2 hB

theorem Base.Finite_rk_of_Finite (hB : M.Base B) (hfin : B.Finite) : Finite_rk M := 
  ⟨⟨B, hB, hfin⟩⟩   

theorem Base.Infinite_rk_of_Infinite (hB : M.Base B) (h : B.Infinite) : Infinite_rk M := 
  ⟨⟨B, hB, h⟩⟩ 

theorem not_Finite_rk (M : Matroid α) [Infinite_rk M] : ¬ Finite_rk M := by
  intro h; obtain ⟨B,hB⟩ := M.exists_Base; exact hB.Infinite hB.Finite

theorem not_Infinite_rk (M : Matroid α) [Finite_rk M] : ¬ Infinite_rk M := by
  intro h; obtain ⟨B,hB⟩ := M.exists_Base; exact hB.Infinite hB.Finite

theorem Finite_or_Infinite_rk (M : Matroid α) : Finite_rk M ∨ Infinite_rk M :=
  let ⟨B, hB⟩ := M.exists_Base
  B.finite_or_infinite.elim 
  (Or.inl ∘ hB.Finite_rk_of_Finite) (Or.inr ∘ hB.Infinite_rk_of_Infinite)

instance Finite_rk_of_Finite {M : Matroid α} [Finite M] : Finite_rk M := 
  let ⟨B, hB⟩ := M.exists_Base
  ⟨⟨B, hB, (M.ground_Finite).subset hB.subset_ground⟩⟩ 

instance Finitary_of_Finite_rk {M : Matroid α} [Finite_rk M] : Finitary M := 
⟨ by
  intros C hC
  obtain (rfl | ⟨e,heC⟩) := C.eq_empty_or_nonempty; exact finite_empty
  have hi : M.Indep (C \ {e}) :=
  by_contra (fun h ↦ (hC.2 ⟨h, (diff_subset _ _).trans hC.1.2⟩ (diff_subset C {e}) heC).2 rfl)
  obtain ⟨B, hB, hCB⟩ := hi 
  convert (hB.Finite.subset hCB).insert e
  rw [insert_diff_singleton, insert_eq_of_mem heC] ⟩  

theorem Base.diff_finite_comm (hB₁ : M.Base B₁) (hB₂ : M.Base B₂) :
    (B₁ \ B₂).Finite ↔ (B₂ \ B₁).Finite := 
  Finite_iff_Finite_of_encard_eq_encard (hB₁.encard_diff_comm hB₂)

theorem Base.diff_infinite_comm (hB₁ : M.Base B₁) (hB₂ : M.Base B₂) : 
    (B₁ \ B₂).Infinite ↔ (B₂ \ B₁).Infinite := 
  Infinite_iff_Infinite_of_encard_eq_encard (hB₁.encard_diff_comm hB₂)

theorem Base.ncard_eq_ncard_of_Base (hB₁ : M.Base B₁) (hB₂ : M.Base B₂) : B₁.ncard = B₂.ncard :=
by rw [←encard_toNat_eq, hB₁.encard_eq_encard_of_Base hB₂, encard_toNat_eq]

end Base


section Dep_Indep

theorem Indep_iff_subset_Base : M.Indep I ↔ ∃ B, M.Base B ∧ I ⊆ B := Iff.rfl

theorem Dep_iff : M.Dep D ↔ ¬M.Indep D ∧ D ⊆ M.E := Iff.rfl  

@[aesop unsafe 15% (rule_sets [Matroid])]
theorem Indep.subset_ground (hI : M.Indep I) : I ⊆ M.E := by 
  obtain ⟨B, hB, hIB⟩ := hI
  exact hIB.trans hB.subset_ground 

@[aesop unsafe 10% (rule_sets [Matroid])]
theorem Dep.subset_ground (hD : M.Dep D) : D ⊆ M.E :=
  hD.2 

@[aesop unsafe 10% (rule_sets [Matroid])]
theorem Coindep.subset_ground (hX : M.Coindep X) : X ⊆ M.E :=
  hX.2

theorem Indep_or_Dep (hX : X ⊆ M.E := by aesop_mat) : M.Indep X ∨ M.Dep X := by 
  rw [Dep, and_iff_left hX]
  apply em

theorem Indep.not_Dep (hI : M.Indep I) : ¬ M.Dep I := 
  fun h ↦ h.1 hI   

theorem Dep.not_Indep (hD : M.Dep D) : ¬ M.Indep D := 
  hD.1  

theorem Dep_of_not_Indep (hD : ¬ M.Indep D) (hDE : D ⊆ M.E := by aesop_mat) : M.Dep D := 
  ⟨hD, hDE⟩ 

theorem Indep_of_not_Dep (hI : ¬ M.Dep I) (hIE : I ⊆ M.E := by aesop_mat) : M.Indep I := 
  by_contra (fun h ↦ hI ⟨h, hIE⟩)

@[simp] theorem not_Dep_iff (hX : X ⊆ M.E := by aesop_mat) : ¬ M.Dep X ↔ M.Indep X := by
  rw [Dep, and_iff_left hX, not_not]

@[simp] theorem not_Indep_iff (hX : X ⊆ M.E := by aesop_mat) : ¬ M.Indep X ↔ M.Dep X := by
  rw [Dep, and_iff_left hX]  

theorem Indep.exists_Base_supset (hI : M.Indep I) : ∃ B, M.Base B ∧ I ⊆ B :=
  hI

theorem Indep.subset (hJ : M.Indep J) (hIJ : I ⊆ J) : M.Indep I :=
  let ⟨B, hB, hJB⟩ := hJ
  ⟨B, hB, hIJ.trans hJB⟩

theorem Dep.supset (hD : M.Dep D) (hDX : D ⊆ X) (hXE : X ⊆ M.E := by aesop_mat) : M.Dep X := 
  Dep_of_not_Indep (fun hI ↦ (hI.subset hDX).not_Dep hD)

@[simp] theorem empty_Indep (M : Matroid α) : M.Indep ∅ :=
  Exists.elim M.exists_Base (fun B hB ↦ ⟨_, hB, B.empty_subset⟩)

theorem Indep.Finite [Finite_rk M] (hI : M.Indep I) : I.Finite := 
  let ⟨_, hB, hIB⟩ := hI
  hB.Finite.subset hIB  

theorem Indep.inter_right (hI : M.Indep I) (X : Set α) : M.Indep (I ∩ X) :=
  hI.subset (inter_subset_left _ _)

theorem Indep.inter_left (hI : M.Indep I) (X : Set α) : M.Indep (X ∩ I) :=
  hI.subset (inter_subset_right _ _)

theorem Indep.diff (hI : M.Indep I) (X : Set α) : M.Indep (I \ X) :=
  hI.subset (diff_subset _ _)

theorem Base.Indep (hB : M.Base B) : M.Indep B :=
  ⟨B, hB, subset_rfl⟩

theorem Base.eq_of_subset_Indep (hB : M.Base B) (hI : M.Indep I) (hBI : B ⊆ I) : B = I :=
  let ⟨B', hB', hB'I⟩ := hI
  hBI.antisymm (by rwa [hB.eq_of_subset_Base hB' (hBI.trans hB'I)])

theorem Base_iff_maximal_Indep : M.Base B ↔ M.Indep B ∧ ∀ I, M.Indep I → B ⊆ I → B = I := by
  refine' ⟨fun h ↦ ⟨h.Indep, fun _ ↦ h.eq_of_subset_Indep ⟩, fun h ↦ _⟩
  obtain ⟨⟨B', hB', hBB'⟩, h⟩ := h
  rwa [h _ hB'.Indep hBB']

theorem Base_iff_mem_maximals : M.Base B ↔ B ∈ maximals (· ⊆ ·) {I | M.Indep I} := by
  rw [Base_iff_maximal_Indep, mem_maximals_setOf_iff]
  
theorem Indep.Base_of_maximal (hI : M.Indep I) (h : ∀ J, M.Indep J → I ⊆ J → I = J) : M.Base I := 
  Base_iff_maximal_Indep.mpr ⟨hI,h⟩

theorem Base.Dep_of_ssubset (hB : M.Base B) (h : B ⊂ X) (hX : X ⊆ M.E := by aesop_mat) : M.Dep X :=
  ⟨λ hX ↦ h.ne (hB.eq_of_subset_Indep hX h.subset), hX⟩

theorem Base.Dep_of_insert (hB : M.Base B) (heB : e ∉ B) (he : e ∈ M.E := by aesop_mat) : 
    M.Dep (insert e B) := hB.Dep_of_ssubset (ssubset_insert heB)

/-- If the difference of two Bases is a singleton, then they differ by an insertion/removal -/
theorem Base.eq_exchange_of_diff_eq_singleton (hB : M.Base B) (hB' : M.Base B') (h : B \ B' = {e}) : 
  ∃ f ∈ B' \ B, B' = (insert f B) \ {e} := by
  obtain ⟨f, hf, hb⟩ := hB.exchange hB' (h.symm.subset (mem_singleton e))
  have hne : f ≠ e := by rintro rfl; exact hf.2 (h.symm.subset (mem_singleton f)).1
  rw [insert_diff_singleton_comm hne] at hb
  refine ⟨f, hf, (hb.eq_of_subset_Base hB' ?_).symm⟩
  rw [diff_subset_iff, insert_subset, union_comm, ←diff_subset_iff, h, and_iff_left rfl.subset]
  exact Or.inl hf.1

theorem Base.exchange_Base_of_Indep (hB : M.Base B) (hf : f ∉ B) 
    (hI : M.Indep (insert f (B \ {e}))) : M.Base (insert f (B \ {e})) := by
  obtain ⟨B', hB', hIB'⟩ := hI
  have hcard := hB'.encard_diff_comm hB
  rw [insert_subset, ←diff_eq_empty, diff_diff_comm, diff_eq_empty, subset_singleton_iff_eq] at hIB'
  obtain ⟨hfB, (h | h)⟩ := hIB'
  · rw [h, encard_empty, encard_eq_zero, eq_empty_iff_forall_not_mem] at hcard
    exact (hcard f ⟨hfB, hf⟩).elim
  rw [h, encard_singleton, encard_eq_one] at hcard
  obtain ⟨x, hx⟩ := hcard
  obtain (rfl : f = x) := hx.subset ⟨hfB, hf⟩
  simp_rw [←h, ←singleton_union, ←hx, sdiff_sdiff_right_self, inf_eq_inter, inter_comm B, 
    diff_union_inter]
  exact hB'

theorem Base.exchange_Base_of_Indep' (hB : M.Base B) (he : e ∈ B) (hf : f ∉ B) 
    (hI : M.Indep (insert f B \ {e})) : M.Base (insert f B \ {e}) := by
  have hfe : f ≠ e := by rintro rfl; exact hf he
  rw [←insert_diff_singleton_comm hfe] at *
  exact hB.exchange_Base_of_Indep hf hI

end Dep_Indep

section Basis

theorem Basis.Indep (hI : M.Basis I X) : M.Indep I := hI.1.1.1

theorem Basis.subset (hI : M.Basis I X) : I ⊆ X := hI.1.1.2

@[aesop unsafe 15% (rule_sets [Matroid])]
theorem Basis.subset_ground (hI : M.Basis I X) : X ⊆ M.E :=
  hI.2 

theorem Basis.Basis_inter_ground (hI : M.Basis I X) : M.Basis I (X ∩ M.E) := by
  convert hI
  rw [inter_eq_self_of_subset_left hI.subset_ground]

@[aesop unsafe 15% (rule_sets [Matroid])]
theorem Basis.left_subset_ground (hI : M.Basis I X) : I ⊆ M.E := 
  hI.Indep.subset_ground

theorem Basis.eq_of_subset_Indep (hI : M.Basis I X) (hJ : M.Indep J) (hIJ : I ⊆ J) (hJX : J ⊆ X) :
    I = J :=
  hIJ.antisymm (hI.1.2 ⟨hJ, hJX⟩ hIJ)

theorem Basis.Finite (hI : M.Basis I X) [Finite_rk M] : I.Finite := hI.Indep.Finite 

theorem Basis_iff' : 
    M.Basis I X ↔ (M.Indep I ∧ I ⊆ X ∧ ∀ J, M.Indep J → I ⊆ J → J ⊆ X → I = J) ∧ X ⊆ M.E := by
  simp [Basis, mem_maximals_setOf_iff, and_assoc, and_congr_left_iff, and_imp, 
    and_congr_left_iff, and_congr_right_iff, @Imp.swap (_ ⊆ X)]

theorem Basis_iff (hX : X ⊆ M.E := by aesop_mat) : 
  M.Basis I X ↔ (M.Indep I ∧ I ⊆ X ∧ ∀ J, M.Indep J → I ⊆ J → J ⊆ X → I = J) :=
by rw [Basis_iff', and_iff_left hX]

theorem Basis_iff_mem_maximals (hX : X ⊆ M.E := by aesop_mat): 
    M.Basis I X ↔ I ∈ maximals (· ⊆ ·) {I | M.Indep I ∧ I ⊆ X} := by
  rw [Basis, and_iff_left hX]

theorem Indep.Basis_of_maximal_subset (hI : M.Indep I) (hIX : I ⊆ X)
    (hmax : ∀ ⦃J⦄, M.Indep J → I ⊆ J → J ⊆ X → J ⊆ I) (hX : X ⊆ M.E := by aesop_mat) : M.Basis I X := by
  rw [Basis_iff (by aesop_mat : X ⊆ M.E), and_iff_right hI, and_iff_right hIX]
  exact fun J hJ hIJ hJX ↦ hIJ.antisymm (hmax hJ hIJ hJX)

theorem Basis.Basis_subset (hI : M.Basis I X) (hIY : I ⊆ Y) (hYX : Y ⊆ X) : M.Basis I Y := by
  rw [Basis_iff (hYX.trans hI.subset_ground), and_iff_right hI.Indep, and_iff_right hIY] 
  exact fun J hJ hIJ hJY ↦ hI.eq_of_subset_Indep hJ hIJ (hJY.trans hYX) 

@[simp] theorem Basis_self_iff_Indep : M.Basis I I ↔ M.Indep I := by
  rw [Basis_iff', and_iff_right rfl.subset, and_assoc, and_iff_left_iff_imp] 
  exact fun hi ↦ ⟨fun _ _ ↦ subset_antisymm, hi.subset_ground⟩ 
  
theorem Indep.Basis_self (h : M.Indep I) : M.Basis I I :=
  Basis_self_iff_Indep.mpr h

@[simp] theorem Basis_empty_iff (M : Matroid α) : M.Basis I ∅ ↔ I = ∅ :=
  ⟨fun h ↦ subset_empty_iff.mp h.subset, fun h ↦ by (rw [h]; exact M.empty_Indep.Basis_self)⟩
  
theorem Basis.Dep_of_ssubset (hI : M.Basis I X) (hIY : I ⊂ Y) (hYX : Y ⊆ X) : M.Dep Y := by
  have : X ⊆ M.E := by aesop_mat 
  rw [←not_Indep_iff]
  exact fun hY ↦ hIY.ne (hI.eq_of_subset_Indep hY hIY.subset hYX)

theorem Basis.insert_Dep (hI : M.Basis I X) (he : e ∈ X \ I) : M.Dep (insert e I) :=
  hI.Dep_of_ssubset (ssubset_insert he.2) (insert_subset.mpr ⟨he.1,hI.subset⟩)

theorem Basis.mem_of_insert_Indep (hI : M.Basis I X) (he : e ∈ X) (hIe : M.Indep (insert e I)) : 
    e ∈ I :=
  by_contra (fun heI ↦ (hI.insert_Dep ⟨he, heI⟩).not_Indep hIe) 

theorem Basis.not_Basis_of_ssubset (hI : M.Basis I X) (hJI : J ⊂ I) : ¬ M.Basis J X :=
  fun h ↦ hJI.ne (h.eq_of_subset_Indep hI.Indep hJI.subset hI.subset)

theorem Indep.subset_Basis_of_subset (hI : M.Indep I) (hIX : I ⊆ X) (hX : X ⊆ M.E := by aesop_mat) : 
    ∃ J, M.Basis J X ∧ I ⊆ J := by
  obtain ⟨J, ⟨(hJ : M.Indep J),hIJ,hJX⟩, hJmax⟩ := M.maximality' X hX I hI hIX
  use J
  rw [and_iff_left hIJ, Basis_iff, and_iff_right hJ, and_iff_right hJX]
  exact fun K hK hJK hKX ↦ hJK.antisymm (hJmax ⟨hK, hIJ.trans hJK, hKX⟩ hJK)

theorem exists_Basis (M : Matroid α) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    ∃ I, M.Basis I X :=
  let ⟨I, hI, _⟩ := M.empty_Indep.subset_Basis_of_subset (empty_subset X) 
  ⟨_,hI⟩

theorem exists_Basis_subset_Basis (M : Matroid α) (hXY : X ⊆ Y) (hY : Y ⊆ M.E := by aesop_mat) :
    ∃ I J, M.Basis I X ∧ M.Basis J Y ∧ I ⊆ J := by
  obtain ⟨I, hI⟩ := M.exists_Basis X (hXY.trans hY)
  obtain ⟨J, hJ, hIJ⟩ := hI.Indep.subset_Basis_of_subset (hI.subset.trans hXY)
  exact ⟨_, _, hI, hJ, hIJ⟩ 

theorem Basis.exists_Basis_inter_eq_of_supset (hI : M.Basis I X) (hXY : X ⊆ Y) 
    (hY : Y ⊆ M.E := by aesop_mat) : ∃ J, M.Basis J Y ∧ J ∩ X = I := by
  obtain ⟨J, hJ, hIJ⟩ := hI.Indep.subset_Basis_of_subset (hI.subset.trans hXY)
  refine ⟨J, hJ, subset_antisymm ?_ (subset_inter hIJ hI.subset)⟩
  exact fun e he ↦ hI.mem_of_insert_Indep he.2 (hJ.Indep.subset (insert_subset.mpr ⟨he.1, hIJ⟩))


-- theorem exists_Basis_union_inter_Basis (M : Matroid α) (X Y : Set α) (hX : X ⊆ M.E := by aesop_mat) 
--   (hY : Y ⊆ M.E := by aesop_mat) : ∃ I, M.Basis I (X ∪ Y) ∧ M.Basis (I ∩ Y) Y := 
-- begin
--   obtain ⟨J, hJ⟩ := M.exists_Basis Y, 
--   exact (hJ.exists_Basis_inter_eq_of_supset (subset_union_right X Y)).imp 
--     (λ I hI, ⟨hI.1, by rwa hI.2⟩), 
-- end 

-- theorem Indep.eq_of_Basis (hI : M.Indep I) (hJ : M.Basis J I) : J = I :=
-- hJ.eq_of_subset_Indep hI hJ.subset subset.rfl

-- theorem Indep.Basis_self (hI : M.Indep I) : M.Basis I I := 
-- begin
--   rw [Basis_iff', and_iff_left hI.subset_ground, and_iff_right hI, and_iff_right subset.rfl], 
--   exact λ _ _, subset_antisymm, 
-- end 

-- @[simp] theorem Basis_self_iff_Indep : M.Basis I I ↔ M.Indep I := ⟨Basis.Indep, Indep.Basis_self⟩

-- theorem Basis.exists_Base (hI : M.Basis I X) : ∃ B, M.Base B ∧ I = B ∩ X :=
-- begin
--   obtain ⟨B,hB, hIB⟩ := hI.Indep,
--   refine ⟨B, hB, subset_antisymm (subset_inter hIB hI.subset) _⟩,
--   rw hI.eq_of_subset_Indep (hB.Indep.inter_right X) (subset_inter hIB hI.subset)
--     (inter_subset_right _ _),
-- end



end Basis




end Matroid 


-- theorem exists_Basis (M : Matroid α) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) : ∃ I, M.Basis I X :=
-- let ⟨I, hI, _⟩ := M.empty_Indep.subset_Basis_of_subset (empty_subset X) in ⟨_,hI⟩

-- theorem exists_Basis_subset_Basis (M : Matroid α) (hXY : X ⊆ Y) (hY : Y ⊆ M.E := by aesop_mat) :
--   ∃ I J, M.Basis I X ∧ M.Basis J Y ∧ I ⊆ J :=
-- begin
--   obtain ⟨I, hI⟩ := M.exists_Basis X (hXY.trans hY), 
--   obtain ⟨J, hJ, hIJ⟩ := hI.Indep.subset_Basis_of_subset (hI.subset.trans hXY), 
--   exact ⟨_, _, hI, hJ, hIJ⟩, 
-- end    

-- theorem Basis.exists_Basis_inter_eq_of_supset (hI : M.Basis I X) (hXY : X ⊆ Y) (hY : Y ⊆ M.E := by aesop_mat) :
--   ∃ J, M.Basis J Y ∧ J ∩ X = I :=
-- begin
--   obtain ⟨J, hJ, hIJ⟩ := hI.Indep.subset_Basis_of_subset (hI.subset.trans hXY), 
--   refine ⟨J, hJ, subset_antisymm _ (subset_inter hIJ hI.subset)⟩,  
--   exact λ e he, hI.mem_of_insert_Indep he.2 (hJ.Indep.subset (insert_subset.mpr ⟨he.1, hIJ⟩)), 
-- end   

-- theorem exists_Basis_union_inter_Basis (M : Matroid α) (X Y : Set α) (hX : X ⊆ M.E := by aesop_mat) 
--   (hY : Y ⊆ M.E := by aesop_mat) : ∃ I, M.Basis I (X ∪ Y) ∧ M.Basis (I ∩ Y) Y := 
-- begin
--   obtain ⟨J, hJ⟩ := M.exists_Basis Y, 
--   exact (hJ.exists_Basis_inter_eq_of_supset (subset_union_right X Y)).imp 
--     (λ I hI, ⟨hI.1, by rwa hI.2⟩), 
-- end 

-- theorem Indep.eq_of_Basis (hI : M.Indep I) (hJ : M.Basis J I) : J = I :=
-- hJ.eq_of_subset_Indep hI hJ.subset subset.rfl

-- theorem Indep.Basis_self (hI : M.Indep I) : M.Basis I I := 
-- begin
--   rw [Basis_iff', and_iff_left hI.subset_ground, and_iff_right hI, and_iff_right subset.rfl], 
--   exact λ _ _, subset_antisymm, 
-- end 

-- @[simp] theorem Basis_self_iff_Indep : M.Basis I I ↔ M.Indep I := ⟨Basis.Indep, Indep.Basis_self⟩

-- theorem Basis.exists_Base (hI : M.Basis I X) : ∃ B, M.Base B ∧ I = B ∩ X :=
-- begin
--   obtain ⟨B,hB, hIB⟩ := hI.Indep,
--   refine ⟨B, hB, subset_antisymm (subset_inter hIB hI.subset) _⟩,
--   rw hI.eq_of_subset_Indep (hB.Indep.inter_right X) (subset_inter hIB hI.subset)
--     (inter_subset_right _ _),
-- end

-- theorem Base_iff_Basis_ground : M.Base B ↔ M.Basis B M.E :=
-- begin
--   rw [Base_iff_maximal_Indep, Basis_iff, and_congr_right], 
--   intro hB, 
--   rw [and_iff_right hB.subset_ground], 
--   exact ⟨λ h J hJ hBJ hJE, h _ hJ hBJ, λ h I hI hBI, h I hI hBI hI.subset_ground⟩,
-- end 

-- theorem Base.Basis_ground (hB : M.Base B) : M.Basis B M.E := Base_iff_Basis_ground.mp hB

-- theorem Indep.Basis_of_forall_insert (hI : M.Indep I) 
--   (hIX : I ⊆ X) (he : ∀ e ∈ X \ I, ¬ M.Indep (insert e I)) (hX : X ⊆ M.E := by aesop_mat) : M.Basis I X :=
-- begin
--   rw [Basis_iff, and_iff_right hI, and_iff_right hIX], 
--   refine λJ hJ hIJ hJX, hIJ.antisymm (λ e heJ, by_contra (λ heI, he e ⟨hJX heJ, heI⟩ _)),  
--   exact hJ.subset (insert_subset.mpr ⟨heJ, hIJ⟩), 
-- end 

-- theorem Basis.Union_Basis_Union {ι : Type*} (X I : ι → Set α) (hI : ∀ i, M.Basis (I i) (X i)) 
-- (h_ind : M.Indep (⋃ i, I i)) : M.Basis (⋃ i, I i) (⋃ i, X i) :=
-- begin
   
--   refine h_ind.Basis_of_forall_insert 
--     (Union_subset_iff.mpr (λ i, (hI i).subset.trans (subset_Union _ _))) (λ e he hi, _)
--     (Union_subset (λ i, (hI i).subset_ground)), 
--   simp only [mem_diff, mem_Union, not_exists] at he, 
--   obtain ⟨i, heXi⟩ := he.1, 
--   exact he.2 i ((hI i).mem_of_insert_Indep heXi 
--     (hi.subset (insert_subset_insert (subset_Union _ _)))), 
-- end 

-- theorem Basis.Basis_Union {ι : Type*} [nonempty ι] (X : ι → Set α) (hI : ∀ i, M.Basis I (X i)) : 
--   M.Basis I (⋃ i, X i) :=
-- begin
--   convert Basis.Union_Basis_Union X (λ _, I) (λ i, hI i) _, 
--   all_goals { rw Union_const },
--   exact (hI (‹nonempty ι›.some)).Indep, 
-- end 

-- theorem Basis.union_Basis_union (hIX : M.Basis I X) (hJY : M.Basis J Y) (h : M.Indep (I ∪ J)) : 
--   M.Basis (I ∪ J) (X ∪ Y) :=
-- begin 
--   rw [union_eq_Union, union_eq_Union], 
--   refine Basis.Union_Basis_Union _ _ _ _,   
--   { simp only [bool.forall_bool, bool.cond_ff, bool.cond_tt], exact ⟨hJY, hIX⟩ }, 
--   rwa [←union_eq_Union], 
-- end 

-- theorem Basis.Basis_union (hIX : M.Basis I X) (hIY : M.Basis I Y) : M.Basis I (X ∪ Y) :=
-- by { convert hIX.union_Basis_union hIY _; rw union_self, exact hIX.Indep }

-- theorem Basis.Basis_union_of_subset (hI : M.Basis I X) (hJ : M.Indep J) (hIJ : I ⊆ J) : 
--   M.Basis J (J ∪ X) :=
-- begin
--   convert hJ.Basis_self.union_Basis_union hI (by rwa union_eq_left_iff_subset.mpr hIJ), 
--   rw union_eq_left_iff_subset.mpr hIJ, 
-- end 

-- theorem Basis.insert_Basis_insert (hI : M.Basis I X) (h : M.Indep (insert e I)) : 
--   M.Basis (insert e I) (insert e X) :=
-- begin
--   convert hI.union_Basis_union 
--     (Indep.Basis_self (h.subset (singleton_subset_iff.mpr (mem_insert _ _)))) _, 
--   simp, simp, simpa, 
-- end 

-- theorem Base.insert_Dep (hB : M.Base B) (h : e ∉ B) : ¬ M.Indep (insert e B) :=
--   λ h', (insert_ne_self.mpr h).symm ((Base_iff_maximal_Indep.mp hB).2 _ h' (subset_insert _ _))

-- theorem Base.ssubset_Dep (hB : M.Base B) (h : B ⊂ X) : ¬ M.Indep X :=
--   λ h', h.ne ((Base_iff_maximal_Indep.mp hB).2 _ h' h.subset)

-- theorem Indep.exists_insert_of_not_Base (hI : M.Indep I) (hI' : ¬M.Base I) (hB : M.Base B) : 
--   ∃ e ∈ B \ I, M.Indep (insert e I) :=
-- begin
--   obtain ⟨B', hB', hIB'⟩ := hI, 
--   obtain ⟨x, hxB', hx⟩ := exists_of_ssubset (hIB'.ssubset_of_ne (by { rintro rfl, exact hI' hB' })), 
--   obtain (hxB | hxB) := em (x ∈ B), 
--   { exact ⟨x, ⟨hxB, hx⟩ , ⟨B', hB', insert_subset.mpr ⟨hxB',hIB'⟩⟩⟩ },
--   obtain ⟨e,he, hBase⟩ := hB'.exchange hB ⟨hxB',hxB⟩,    
--   exact ⟨e, ⟨he.1, not_mem_subset hIB' he.2⟩, 
--     ⟨_, hBase, insert_subset_insert (subset_diff_singleton hIB' hx)⟩⟩,  
-- end  

-- theorem Basis.inter_eq_of_subset_Indep (hIX : M.Basis I X) (hIJ : I ⊆ J) (hJ : M.Indep J) : 
--   J ∩ X = I := 
-- (subset_inter hIJ hIX.subset).antisymm' 
--   (λ e he, hIX.mem_of_insert_Indep he.2 (hJ.subset (insert_subset.mpr ⟨he.1, hIJ⟩))) 

-- theorem Base.exists_insert_of_ssubset (hB : M.Base B) (hIB : I ⊂ B) (hB' : M.Base B') : 
--   ∃ e ∈ B' \ I, M.Indep (insert e I) :=
-- (hB.Indep.subset hIB.subset).exists_insert_of_not_Base 
--     (λ hI, hIB.ne (hI.eq_of_subset_Base hB hIB.subset)) hB'

-- theorem Base.Base_of_Basis_supset (hB : M.Base B) (hBX : B ⊆ X) (hIX : M.Basis I X) : M.Base I :=
-- begin
--   by_contra h, 
--   obtain ⟨e,heBI,he⟩ := hIX.Indep.exists_insert_of_not_Base h hB, 
--   exact heBI.2 (hIX.mem_of_insert_Indep (hBX heBI.1) he), 
-- end 

-- theorem Base.Basis_of_subset (hX : X ⊆ M.E := by aesop_mat) (hB : M.Base B) (hBX : B ⊆ X) : M.Basis B X :=
-- begin
--   rw [Basis_iff, and_iff_right hB.Indep, and_iff_right hBX], 
--   exact λ J hJ hBJ hJX, hB.eq_of_subset_Indep hJ hBJ, 
-- end 

-- theorem Indep.exists_Base_subset_union_Base (hI : M.Indep I) (hB : M.Base B) : 
--   ∃ B', M.Base B' ∧ I ⊆ B' ∧ B' ⊆ I ∪ B :=
-- begin
--   obtain ⟨B', hB', hIB'⟩ := hI.subset_Basis_of_subset (subset_union_left I B),  
--   exact ⟨B', hB.Base_of_Basis_supset (subset_union_right _ _) hB', hIB', hB'.subset⟩, 
-- end  

-- theorem eq_of_Base_iff_Base_forall {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E) 
-- (h : ∀ B ⊆ M₁.E, (M₁.Base B ↔ M₂.Base B)) : M₁ = M₂ :=
-- begin
--   apply Matroid.ext _ _ hE, 
--   ext B, 
--   refine ⟨λ h', (h _ h'.subset_ground).mp h', 
--     λ h', (h _ (h'.subset_ground.trans_eq hE.symm)).mpr h'⟩,
-- end 

-- theorem eq_of_Indep_iff_Indep_forall {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E) 
-- (h : ∀ I ⊆ M₁.E, (M₁.Indep I ↔ M₂.Indep I)) :
--   M₁ = M₂ :=
-- begin
--   refine eq_of_Base_iff_Base_forall hE (λ B hB, _), 
--   rw [Base_iff_maximal_Indep, Base_iff_maximal_Indep], 
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

-- theorem eq_iff_Indep_iff_Indep_forall {M₁ M₂ : Matroid α} : 
--   M₁ = M₂ ↔ (M₁.E = M₂.E) ∧ ∀ I ⊆ M₁.E , M₁.Indep I ↔ M₂.Indep I :=
-- ⟨λ h, by { subst h, simp }, λ h, eq_of_Indep_iff_Indep_forall h.1 h.2⟩  


-- -- theorem eq_iff_Indep_iff_Indep_forall {M₁ M₂ : Matroid α} : M₁ = M₂ ↔ ∀ I, M₁.Indep I ↔ M₂.Indep I :=  
-- -- ⟨λ h I, by rw h, eq_of_Indep_iff_Indep_forall⟩  

-- -- theorem eq_iff_set_of_Indep_eq_set_of_Indep {M₁ M₂ : Matroid α} : 
-- --   M₁ = M₂ ↔ {I | M₁.Indep I} = {I | M₂.Indep I} :=
-- -- by { rw [eq_iff_Indep_iff_Indep_forall, set.ext_iff], refl }

-- end Dep_Indep


-- section from_axioms

-- def matroid_of_Base {α : Type*} (E : Set α) (Base : Set α → Prop) 
-- (exists_Base : ∃ B, Base B) (Base_exchange : exchange_property Base) 
-- (maximality : exists_maximal_subset_property (λ I, ∃ B, Base B ∧ I ⊆ B))
-- (support : ∀ B, Base B → B ⊆ E) : Matroid α := 
-- ⟨E, Base, exists_Base, Base_exchange, maximality, support⟩

-- @[simp] theorem matroid_of_Base_apply {α : Type*} (E : Set α) (Base : Set α → Prop) 
-- (exists_Base : ∃ B, Base B) (Base_exchange : exchange_property Base) 
-- (maximality : exists_maximal_subset_property (λ I, ∃ B, Base B ∧ I ⊆ B))
-- (support : ∀ B, Base B → B ⊆ E) :
-- (matroid_of_Base E Base exists_Base Base_exchange maximality support).Base = Base := rfl 

-- /-- A collection of Bases with the exchange property and at least one finite member is a matroid -/
-- def matroid_of_exists_finite_Base {α : Type*} (E : Set α) (Base : Set α → Prop) 
-- (exists_finite_Base : ∃ B, Base B ∧ B.Finite) (Base_exchange : exchange_property Base) 
-- (support : ∀ B, Base B → B ⊆ E) : 
--   Matroid α := 
-- matroid_of_Base E Base (let ⟨B,h⟩ := exists_finite_Base in ⟨B,h.1⟩) Base_exchange
-- (begin
--   obtain ⟨B, hB, hfin⟩ := exists_finite_Base,  
--   apply exists_maximal_subset_property_of_bounded ⟨B.ncard, _⟩,
--   rintro I ⟨B', hB', hIB'⟩,   
--   have hB'fin : B'.Finite, 
--   { rwa [finite_iff_finite_of_encard_eq_encard (encard_eq_of_exch Base_exchange hB' hB)] },
--   rw [←encard_to_nat_eq B, encard_eq_of_exch Base_exchange hB hB', encard_to_nat_eq], 
--   exact ⟨hB'fin.subset hIB', ncard_le_of_subset hIB' hB'fin⟩, 
-- end) 
-- support 

-- @[simp] theorem matroid_of_exists_finite_Base_apply {α : Type*} (E : Set α) (Base : Set α → Prop) 
-- (exists_finite_Base : ∃ B, Base B ∧ B.Finite) (Base_exchange : exchange_property Base) 
-- (support : ∀ B, Base B → B ⊆ E) : 
-- (matroid_of_exists_finite_Base E Base exists_finite_Base Base_exchange support).Base = Base := rfl 

-- /-- A matroid constructed with a finite Base is `Finite_rk` -/
-- instance {E : Set α} {Base : Set α → Prop} {exists_finite_Base : ∃ B, Base B ∧ B.Finite} 
-- {Base_exchange : exchange_property Base} {support : ∀ B, Base B → B ⊆ E} : 
--   Matroid.Finite_rk (matroid_of_exists_finite_Base E Base exists_finite_Base Base_exchange support) := 
-- ⟨exists_finite_Base⟩  

-- def matroid_of_Base_of_finite {E : Set α} (hE : E.Finite) (Base : Set α → Prop)
-- (exists_Base : ∃ B, Base B) (Base_exchange : exchange_property Base)
-- (support : ∀ B, Base B → B ⊆ E) : 
--   Matroid α :=
-- matroid_of_exists_finite_Base E Base (let ⟨B,hB⟩ := exists_Base in ⟨B,hB, hE.subset (support _ hB)⟩) 
-- Base_exchange support

-- @[simp] theorem matroid_of_Base_of_finite_apply {E : Set α} (hE : E.Finite) (Base : Set α → Prop)
-- (exists_Base : ∃ B, Base B) (Base_exchange : exchange_property Base)
-- (support : ∀ B, Base B → B ⊆ E) : 
-- (matroid_of_Base_of_finite hE Base exists_Base Base_exchange support).Base = Base := rfl 

-- /-- A version of the Independence axioms that avoids cardinality -/
-- def matroid_of_Indep (E : Set α) (Indep : Set α → Prop) (h_empty : Indep ∅) 
-- (h_subset : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I) 
-- (h_aug : ∀⦃I B⦄, Indep I → I ∉ maximals (⊆) Indep → B ∈ maximals (⊆) Indep → 
--   ∃ x ∈ B \ I, Indep (insert x I))
-- (h_maximal : exists_maximal_subset_property Indep) 
-- (h_support : ∀ I, Indep I → I ⊆ E) : 
--   Matroid α :=
-- matroid_of_Base E (λ B, B ∈ maximals (⊆) Indep)
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
--   rintro A B' ⟨(hB'i : Indep _), hB'max⟩ hB'' hIA hAX hJA, 
--   exact hJmax ⟨h_subset hB'i hB'', hIA, hAX⟩ hJA,
-- end )
-- (λ B hB, h_support B hB.1)

-- @[simp] theorem matroid_of_Indep_apply (E : Set α) (Indep : Set α → Prop) (h_empty : Indep ∅) 
-- (h_subset : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I) 
-- (h_aug : ∀⦃I B⦄, Indep I → I ∉ maximals (⊆) Indep → B ∈ maximals (⊆) Indep → 
--   ∃ x ∈ B \ I, Indep (insert x I))
-- (h_maximal : exists_maximal_subset_property Indep) 
-- (h_support : ∀ I, Indep I → I ⊆ E)  : 
-- (matroid_of_Indep E Indep h_empty h_subset h_aug h_maximal h_support).Indep = Indep :=
-- begin
--   ext I, 
--   simp only [Matroid.Indep, matroid_of_Indep], 
--   refine ⟨λ ⟨B, hB, hIB⟩, h_subset hB.1 hIB, λ hI, _⟩, 
--   obtain ⟨B, ⟨hB, hIB, -⟩, hBmax⟩ :=  h_maximal I univ hI (subset_univ _), 
--   exact ⟨B, ⟨hB, λ B' hB' hBB', hBmax ⟨hB', hIB.trans hBB', subset_univ _⟩ hBB'⟩, hIB⟩, 
-- end 

-- /-- If there is an absolute upper bound on the size of an Independent set, then the maximality axiom isn't needed to define a matroid by Independent sets. -/
-- def matroid_of_Indep_of_bdd (E : Set α) (Indep : Set α → Prop) (h_empty : Indep ∅) 
-- (h_subset : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I) 
-- (h_aug : ∀⦃I B⦄, Indep I → I ∉ maximals (⊆) Indep → B ∈ maximals (⊆) Indep → 
--   ∃ x ∈ B \ I, Indep (insert x I))
-- (h_bdd : ∃ n, ∀ I, Indep I → I.Finite ∧ I.ncard ≤ n )
-- (h_support : ∀ I, Indep I → I ⊆ E) : Matroid α :=
-- matroid_of_Indep E Indep h_empty h_subset h_aug (exists_maximal_subset_property_of_bounded h_bdd) 
-- h_support 

-- @[simp] theorem matroid_of_Indep_of_bdd_apply (E : Set α) (Indep : Set α → Prop) (h_empty : Indep ∅) 
-- (h_subset : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I) 
-- (h_aug : ∀⦃I B⦄, Indep I → I ∉ maximals (⊆) Indep → B ∈ maximals (⊆) Indep → 
--   ∃ x ∈ B \ I, Indep (insert x I))
-- (h_bdd : ∃ n, ∀ I, Indep I → I.Finite ∧ I.ncard ≤ n ) 
-- (h_support : ∀ I, Indep I → I ⊆ E) : 
-- (matroid_of_Indep_of_bdd E Indep h_empty h_subset h_aug h_bdd h_support).Indep = Indep := 
-- by simp [matroid_of_Indep_of_bdd]

-- instance (E : Set α) (Indep : Set α → Prop) (h_empty : Indep ∅) 
-- (h_subset : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I) 
-- (h_aug : ∀⦃I B⦄, Indep I → I ∉ maximals (⊆) Indep → B ∈ maximals (⊆) Indep → 
--   ∃ x ∈ B \ I, Indep (insert x I)) (h_bdd : ∃ n, ∀ I, Indep I → I.Finite ∧ I.ncard ≤ n ) 
-- (h_support : ∀ I, Indep I → I ⊆ E) : 
-- Matroid.Finite_rk (matroid_of_Indep_of_bdd E Indep h_empty h_subset h_aug h_bdd h_support) := 
-- begin
--   obtain ⟨B, hB⟩ := 
--     (matroid_of_Indep_of_bdd E Indep h_empty h_subset h_aug h_bdd h_support).exists_Base, 
--   obtain ⟨h, h_bdd⟩ := h_bdd,  
--   refine hB.Finite_rk_of_finite (h_bdd B _).1,
--   rw [←matroid_of_Indep_of_bdd_apply E Indep, Matroid.Indep], 
--   exact ⟨_, hB, subset.rfl⟩,  
-- end 

-- def matroid_of_Indep_of_bdd' (E : Set α) (Indep : Set α → Prop) (h_empty : Indep ∅) 
-- (h_subset : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I) 
-- (ind_aug : ∀ ⦃I J⦄, Indep I → Indep J → I.ncard < J.ncard →
--   ∃ e ∈ J, e ∉ I ∧ Indep (insert e I)) (h_bdd : ∃ n, ∀ I, Indep I → I.Finite ∧ I.ncard ≤ n )
-- (h_support : ∀ I, Indep I → I ⊆ E) : Matroid α :=
-- matroid_of_Indep_of_bdd E Indep h_empty h_subset 
-- (begin
--   intros I J hI hIn hJ, 
--   by_contra' h', 
--   obtain (hlt | hle) := lt_or_le I.ncard J.ncard, 
--   { obtain ⟨e,heJ,heI, hi⟩ :=  ind_aug hI hJ.1 hlt, 
--     exact h' e ⟨heJ,heI⟩ hi },
--   obtain (h_eq | hlt) := hle.eq_or_lt, 
--   { refine hIn ⟨hI, λ K (hK : Indep K) hIK, hIK.ssubset_or_eq.elim (λ hss, _) 
--       (λ h, h.symm.subset)⟩,
--     obtain ⟨f, hfK, hfJ, hi⟩ := ind_aug hJ.1 hK (h_eq.trans_lt (ncard_lt_ncard hss _)), 
--     { exact (hfJ (hJ.2 hi (subset_insert _ _) (mem_insert f _))).elim },
--     obtain ⟨n, hn⟩ := h_bdd, 
--     exact (hn K hK).1 },
--   obtain ⟨e,heI, heJ, hi⟩ := ind_aug hJ.1 hI hlt, 
--     exact heJ (hJ.2 hi (subset_insert _ _) (mem_insert e _)), 
-- end) h_bdd h_support 

-- @[simp] theorem matroid_of_Indep_of_bdd'_apply (E : Set α) (Indep : Set α → Prop) (h_empty : Indep ∅) 
-- (h_subset : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I) 
-- (ind_aug : ∀ ⦃I J⦄, Indep I → Indep J → I.ncard < J.ncard →
--   ∃ e ∈ J, e ∉ I ∧ Indep (insert e I)) (h_bdd : ∃ n, ∀ I, Indep I → I.Finite ∧ I.ncard ≤ n )
-- (h_support : ∀ I, Indep I → I ⊆ E) : 
-- (matroid_of_Indep_of_bdd' E Indep h_empty h_subset ind_aug h_bdd h_support).Indep = Indep :=
-- by simp [matroid_of_Indep_of_bdd']

-- /-- A collection of sets in a finite type satisfying the usual Independence axioms determines a matroid -/
-- def matroid_of_Indep_of_finite {E : Set α} (hE : E.Finite) (Indep : Set α → Prop)
-- (h_empty : Indep ∅)
-- (ind_mono : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I)
-- (ind_aug : ∀ ⦃I J⦄, Indep I → Indep J → I.ncard < J.ncard → ∃ e ∈ J, e ∉ I ∧ Indep (insert e I)) 
-- (h_support : ∀ ⦃I⦄, Indep I → I ⊆ E) :
--   Matroid α := 
-- matroid_of_Indep_of_bdd' E Indep h_empty ind_mono ind_aug 
--   ⟨E.ncard, λ I hI, ⟨hE.subset (h_support hI), ncard_le_of_subset (h_support hI) hE⟩⟩ h_support 

-- @[simp] theorem matroid_of_Indep_of_finite_apply {E : Set α} (hE : E.Finite) (Indep : Set α → Prop)
-- (h_empty : Indep ∅)
-- (ind_mono : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I)
-- (ind_aug : ∀ ⦃I J⦄, Indep I → Indep J → I.ncard < J.ncard → ∃ e ∈ J, e ∉ I ∧ Indep (insert e I)) 
-- (h_support : ∀ ⦃I⦄, Indep I → I ⊆ E) :
--   (matroid_of_Indep_of_finite hE Indep h_empty ind_mono ind_aug h_support).Indep = Indep :=
-- by simp [matroid_of_Indep_of_finite]

-- end from_axioms 

-- section dual

-- /-- This is really an order-theory theorem. Not clear where to put it, though.  -/
-- theorem Base_compl_iff_mem_maximals_disjoint_Base : 
--   M.Base Bᶜ ↔ B ∈ maximals (⊆) {I | ∃ B, M.Base B ∧ disjoint I B} :=
-- begin
--   simp_rw ←subset_compl_iff_disjoint_left, 
--   refine ⟨λ h, ⟨⟨Bᶜ,h,subset.rfl⟩, _⟩, _⟩,
--   { rintro X ⟨B', hB', hXB'⟩ hBX, 
--     rw [←compl_subset_compl] at ⊢ hBX,
--     rwa ←hB'.eq_of_subset_Base h (hXB'.trans hBX) },
--   rintro ⟨⟨B',hB',hBB'⟩,h⟩, 
--   rw subset_compl_comm at hBB', 
--   rwa [hBB'.antisymm (h ⟨_, hB', _⟩ hBB'), compl_compl],   
--   rw compl_compl, 
-- end 

-- theorem Base_compl_iff_mem_maximals_disjoint_Base' (hB : B ⊆ M.E := by aesop_mat) : 
--   M.Base (M.E \ B) ↔ B ∈ maximals (⊆) {I | I ⊆ M.E ∧ ∃ B, M.Base B ∧ disjoint I B} := 
-- begin
--   refine ⟨λ h, ⟨⟨hB,_,h,disjoint_sdiff_right⟩,_⟩, λ h, _⟩, 
--   { rintro X ⟨hXE,B', hB', hXB'⟩ hBX,
--     rw [hB'.eq_of_subset_Base h (subset_diff.mpr ⟨hB'.subset_ground,_⟩), 
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
-- matroid_of_Indep M.E (λ I, I ⊆ M.E ∧ ∃ B, M.Base B ∧ disjoint I B) 
-- ⟨empty_subset M.E, M.exists_Base.imp (λ B hB, ⟨hB, empty_disjoint _⟩)⟩ 
-- (begin
--   rintro I J ⟨hJE, B, hB, hJB⟩ hIJ, 
--   exact ⟨hIJ.trans hJE, ⟨B, hB, disjoint_of_subset_left hIJ hJB⟩⟩, 
-- end) 
-- (begin
--   rintro I X ⟨hIE, B, hB, hIB⟩ hI_not_max hX_max,  
--   have hXE := hX_max.1.1, 
--   have hB' := (Base_compl_iff_mem_maximals_disjoint_Base' hXE).mpr hX_max,
  
--   set B' := M.E \ X with hX, 
--   have hI := (not_iff_not.mpr (Base_compl_iff_mem_maximals_disjoint_Base')).mpr hI_not_max, 
--   obtain ⟨B'', hB'', hB''₁, hB''₂⟩ := (hB'.Indep.diff I).exists_Base_subset_union_Base hB, 
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
--   obtain ⟨I, hI⟩ :=  M.exists_Basis (M.E \ X) ,
--   obtain ⟨B', hB', hIB', hB'IB⟩ := hI.Indep.exists_Base_subset_union_Base hB, 
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
  
--   obtain ⟨B₁,hB₁,hI'B₁,hB₁I⟩ := (hB'.Indep.subset hI').exists_Base_subset_union_Base hB'',
--   rw [union_comm, ←union_assoc, union_eq_self_of_subset_right (inter_subset_left _ _)] at hB₁I, 
  
--   have : B₁ = B', 
--   { refine hB₁.eq_of_subset_Indep hB'.Indep (λ e he, _), 
--     refine (hB₁I he).elim (λ heB'',_) (λ h, h.1), 
--     refine (em (e ∈ X)).elim (λ heX, hI' (or.inl ⟨heB'', heX⟩)) (λ heX, hIB' _), 
--     refine hI.mem_of_insert_Indep ⟨hB₁.subset_ground he, heX⟩ 
--       (hB₁.Indep.subset (insert_subset.mpr ⟨he, _⟩)), 
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

-- theorem dual_Indep_iff_exists' : (M﹡.Indep I) ↔ I ⊆ M.E ∧ (∃ B, M.Base B ∧ disjoint I B) := 
-- by simp [has_matroid_dual.dual, dual]

-- theorem dual_Indep_iff_exists (hI : I ⊆ M.E := by aesop_mat) : 
--   (M﹡.Indep I) ↔ (∃ B, M.Base B ∧ disjoint I B) := 
-- by rw [dual_Indep_iff_exists', and_iff_right hI]

-- @[simp] theorem dual_ground : M﹡.E = M.E := rfl 

-- theorem dual_Dep_iff_forall : (M﹡.Dep I) ↔ I ⊆ M.E ∧ ∀ B, M.Base B → (I ∩ B).nonempty :=
-- begin
--   simp_rw [Dep_iff, dual_Indep_iff_exists', and_comm, dual_ground, and.congr_right_iff, not_and, 
--     not_exists, not_and, not_disjoint_iff_nonempty_inter], 
--   exact λ hIE, by rw [imp_iff_right hIE], 
-- end   

-- instance dual_finite [M.Finite] : M﹡.Finite := 
-- ⟨M.ground_finite⟩  

-- theorem set.subset_ground_dual (hX : X ⊆ M.E) : X ⊆ M﹡.E := hX 

-- theorem dual_Base_iff (hB : B ⊆ M.E := by aesop_mat) : M﹡.Base B ↔ M.Base (M.E \ B) := 
-- begin
--   rw [Base_compl_iff_mem_maximals_disjoint_Base', Base_iff_maximal_Indep, dual_Indep_iff_exists', 
--     mem_maximals_set_of_iff],
--   simp [dual_Indep_iff_exists'],
-- end 

-- theorem dual_Base_iff' : M﹡.Base B ↔ M.Base (M.E \ B) ∧ B ⊆ M.E := 
-- begin
--   obtain (h | h) := em (B ⊆ M.E), 
--   { rw [dual_Base_iff, and_iff_left h] },
--   rw [iff_false_intro h, and_false, iff_false], 
--   exact λ h', h h'.subset_ground,  
-- end  

-- theorem Base.compl_Base_of_dual (h : M﹡.Base B) : M.Base (M.E \ B) := 
-- (dual_Base_iff (by { exact h.subset_ground })).mp h

-- @[simp] theorem dual_dual (M : Matroid α) : M﹡﹡ = M := 
-- begin
--   refine eq_of_Base_iff_Base_forall rfl (λ B hB, _), 
--   rw [dual_Base_iff, dual_Base_iff], 
--   rw [dual_ground] at *, 
--   simp only [sdiff_sdiff_right_self, inf_eq_inter, ground_inter_right], 
-- end 

-- theorem dual_Indep_iff_Coindep : M﹡.Indep X ↔ M.Coindep X := dual_Indep_iff_exists'

-- theorem Base.compl_Base_dual (hB : M.Base B) : M﹡.Base (M.E \ B) := 
-- by { haveI := fact.mk hB.subset_ground, simpa [dual_Base_iff] }

-- theorem Base.compl_inter_Basis_of_inter_Basis (hB : M.Base B) (hBX : M.Basis (B ∩ X) X) :
--   M﹡.Basis ((M.E \ B) ∩ (M.E \ X)) (M.E \ X) := 
-- begin
--   rw Basis_iff, 
--   refine ⟨(hB.compl_Base_dual.Indep.subset (inter_subset_left _ _)), inter_subset_right _ _, 
--     λ J hJ hBCJ hJX, hBCJ.antisymm (subset_inter _ hJX)⟩, 
  
--   obtain ⟨-, B', hB', hJB'⟩ := dual_Indep_iff_Coindep.mp hJ, 

--   obtain ⟨B'', hB'', hsB'', hB''s⟩  := hBX.Indep.exists_Base_subset_union_Base hB', 
--   have hB'ss : B' ⊆ B ∪ X, 
--   { rw [←diff_subset_diff_iff M.E (by ssE : B ∪ X ⊆ M.E) hB'.subset_ground, subset_diff,
--       and_iff_right (diff_subset _ _)],
--     rw [diff_inter_diff] at hBCJ, 
--     exact disjoint_of_subset_left hBCJ hJB' },
  
--   have hB''ss : B'' ⊆ B, 
--   { refine λ e he, (hB''s he).elim and.left (λ heB', (hB'ss heB').elim id (λ heX, _)), 
--      exact (hBX.mem_of_insert_Indep heX (hB''.Indep.subset (insert_subset.mpr ⟨he,hsB''⟩))).1 }, 
  
--   have := (hB''.eq_of_subset_Indep hB.Indep hB''ss).symm, subst this,
--   rw subset_diff at *, 
--   exact ⟨hJX.1, disjoint_of_subset_right hB''s (disjoint_union_right.mpr 
--     ⟨disjoint_of_subset_right (inter_subset_right _ _) hJX.2, hJB'⟩)⟩, 
-- end 

-- theorem Base.inter_Basis_iff_compl_inter_Basis_dual (hB : M.Base B) (hX : X ⊆ M.E := by aesop_mat): 
--   M.Basis (B ∩ X) X ↔ M﹡.Basis ((M.E \ B) ∩ (M.E \ X)) (M.E \ X) :=
-- begin
--   refine ⟨hB.compl_inter_Basis_of_inter_Basis, λ h, _⟩, 
--   simpa using hB.compl_Base_dual.compl_inter_Basis_of_inter_Basis h, 
-- end 
  
-- theorem dual_inj {M₁ M₂ : Matroid α} (h : M₁﹡ = M₂﹡) : M₁ = M₂ :=
-- by rw [←dual_dual M₁, h, dual_dual]

-- @[simp] theorem dual_inj_iff {M₁ M₂ : Matroid α} : M₁﹡ = M₂﹡ ↔ M₁ = M₂ := ⟨dual_inj, congr_arg _⟩

-- theorem eq_dual_comm {M₁ M₂ : Matroid α} : M₁ = M₂﹡ ↔ M₂ = M₁﹡ := 
-- by rw [←dual_inj_iff, dual_dual, eq_comm]

-- theorem dual_eq_comm {M₁ M₂ : Matroid α} : M₁﹡ = M₂ ↔ M₂﹡ = M₁ := 
-- by rw [←dual_inj_iff, dual_dual, eq_comm]

-- theorem Coindep_iff_exists (hX : X ⊆ M.E := by aesop_mat) : M.Coindep X ↔ ∃ B, M.Base B ∧ disjoint X B := 
-- by rw [Coindep, and_iff_right hX]

-- theorem Coindep.exists_disjoint_Base (hX : M.Coindep X) : ∃ B, M.Base B ∧ disjoint X B := hX.2

-- theorem Coindep.Base_of_Basis_compl (hX : M.Coindep X) (hB : M.Basis B Xᶜ) : M.Base B :=
-- begin
--   obtain ⟨B',hB'⟩ := hX.exists_disjoint_Base, 
--   exact hB'.1.Base_of_Basis_supset (subset_compl_iff_disjoint_left.mpr hB'.2) hB, 
-- end 

-- theorem Base_iff_dual_Base_compl (hB : B ⊆ M.E := by aesop_mat) : M.Base B ↔ M﹡.Base (M.E \ B) :=
-- by simp [dual_Base_iff]

-- end dual 

-- end Matroid 
