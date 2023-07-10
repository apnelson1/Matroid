import Mathlib.Data.Set.Finite
import Matroid.ForMathlib.encard_stuff
import Matroid.ForMathlib.Other
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
  (exists_base' : ∃ B, Base B)
  (base_exchange' : Matroid.exchange_property Base)
  (maximality' : ∀ X, X ⊆ ground → 
    Matroid.exists_maximal_subset_property (fun I ↦ ∃ B, Base B ∧ I ⊆ B) X)
  (subset_ground' : ∀ B, Base B → B ⊆ ground)

namespace Matroid


variable {α : Type _} {M : Matroid α} 

pp_extended_field_notation Base

/-- We write `M.E` for the ground set of a matroid `M`-/
def E (M : Matroid α) : Set α := M.ground
pp_extended_field_notation Matroid.E

@[simp] theorem ground_eq_E (M : Matroid α) : M.ground = M.E := rfl 

/-- Typeclass for a matroid having finite ground set. This is just a wrapper for `[M.E.Finite]`-/
class Finite (M : Matroid α) : Prop := (ground_finite : M.E.Finite)

theorem ground_finite (M : Matroid α) [M.Finite] : M.E.Finite := ‹M.Finite›.ground_finite   

theorem Set_finite (M : Matroid α) [M.Finite] (X : Set α) (hX : X ⊆ M.E := by aesop) : X.Finite :=
  M.ground_finite.subset hX 

instance finite_of_finite [@_root_.Finite α] {M : Matroid α} : Finite M := 
  ⟨Set.toFinite _⟩ 

/-- A `FiniteRk` matroid is one with a finite Basis -/
class FiniteRk (M : Matroid α) : Prop := (exists_finite_base : ∃ B, M.Base B ∧ B.Finite) 

instance finiteRk_of_finite (M : Matroid α) [Finite M] : FiniteRk M := 
  ⟨ M.exists_base'.imp (fun B hB ↦ ⟨hB, M.Set_finite B (M.subset_ground' _ hB)⟩) ⟩ 

/-- An `InfiniteRk` matroid is one whose Bases are infinite. -/
class InfiniteRk (M : Matroid α) : Prop := (exists_infinite_base : ∃ B, M.Base B ∧ B.Infinite)

/-- A `RkPos` matroid is one in which the empty set is not a Basis -/
class RkPos (M : Matroid α) : Prop := (empty_not_base : ¬M.Base ∅)

theorem rkPos_iff_empty_not_base : M.RkPos ↔ ¬M.Base ∅ :=
  ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩  


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
theorem encard_base_eq_of_exch {Base : Set α → Prop} (exch : exchange_property Base)
    (hB₁ : Base B₁) (hB₂ : Base B₂) : B₁.encard = B₂.encard := by 
rw [←encard_diff_add_encard_inter B₁ B₂, encard_diff_eq_of_exch exch hB₁ hB₂, inter_comm, 
     encard_diff_add_encard_inter]

end exchange


section aesop

/-- The `aesop_mat` tactic attempts to prove a set is contained in the ground set of a matroid. 
  It uses a `[Matroid]` ruleset, and is allowed to fail. -/
macro (name := aesop_mat) "aesop_mat" c:Aesop.tactic_clause* : tactic =>
`(tactic|
  aesop $c* (options := { terminal := true })
  (rule_sets [$(Lean.mkIdent `Matroid):ident]))

macro (name := aesop_mat?) "aesop_mat?" c:Aesop.tactic_clause* : tactic =>
`(tactic|
  aesop? $c* (options := { terminal := true })
  (rule_sets [$(Lean.mkIdent `Matroid):ident]))

@[aesop unsafe 5% (rule_sets [Matroid])] 
private theorem inter_right_subset_ground (hX : X ⊆ M.E) : 
    X ∩ Y ⊆ M.E := (inter_subset_left _ _).trans hX 

@[aesop unsafe 5% (rule_sets [Matroid])]
private theorem inter_left_subset_ground (hX : X ⊆ M.E) :
    Y ∩ X ⊆ M.E := (inter_subset_right _ _).trans hX 

@[aesop unsafe 5% (rule_sets [Matroid])]
private theorem diff_subset_ground (hX : X ⊆ M.E) : X \ Y ⊆ M.E :=      
  (diff_subset _ _).trans hX 

@[aesop unsafe 10% (rule_sets [Matroid])]
private theorem ground_diff_subset_ground : M.E \ X ⊆ M.E :=
  diff_subset_ground rfl.subset 

@[aesop unsafe 10% (rule_sets [Matroid])]
private theorem singleton_subset_ground (he : e ∈ M.E) : {e} ⊆ M.E := 
  singleton_subset_iff.mpr he

@[aesop unsafe 5% (rule_sets [Matroid])]
private theorem subset_ground_of_subset (hXY : X ⊆ Y) (hY : Y ⊆ M.E) : X ⊆ M.E := 
  hXY.trans hY

@[aesop safe (rule_sets [Matroid])]
private theorem insert_subset_ground {e : α} {X : Set α} {M : Matroid α} 
    (he : e ∈ M.E) (hX : X ⊆ M.E) : insert e X ⊆ M.E := 
    insert_subset he hX 

@[aesop safe (rule_sets [Matroid])]
private theorem ground_subset_ground {M : Matroid α} : M.E ⊆ M.E := 
  rfl.subset
   
attribute [aesop safe (rule_sets [Matroid])] empty_subset union_subset iUnion_subset 

end aesop
section Base

@[aesop unsafe 10% (rule_sets [Matroid])]
theorem Base.subset_ground (hB : M.Base B) : B ⊆ M.E :=
  M.subset_ground' B hB 

theorem exists_base (M : Matroid α) : ∃ B, M.Base B := M.exists_base'

theorem Base.exchange (hB₁ : M.Base B₁) (hB₂ : M.Base B₂) (hx : e ∈ B₁ \ B₂) :
    ∃ y ∈ B₂ \ B₁, M.Base (insert y (B₁ \ {e}))  :=
  M.base_exchange' B₁ B₂ hB₁ hB₂ _ hx

theorem Base.exchange_mem (hB₁ : M.Base B₁) (hB₂ : M.Base B₂) (hxB₁ : e ∈ B₁) (hxB₂ : e ∉ B₂) :
    ∃ y, (y ∈ B₂ ∧ y ∉ B₁) ∧ M.Base (insert y (B₁ \ {e})) :=
  by simpa using hB₁.exchange hB₂ ⟨hxB₁, hxB₂⟩

theorem Base.eq_of_subset_base (hB₁ : M.Base B₁) (hB₂ : M.Base B₂) (hB₁B₂ : B₁ ⊆ B₂) :
    B₁ = B₂ :=
  antichain_of_exch M.base_exchange' hB₁ hB₂ hB₁B₂

theorem Base.encard_diff_comm (hB₁ : M.Base B₁) (hB₂ : M.Base B₂) :
    (B₁ \ B₂).encard = (B₂ \ B₁).encard :=
  encard_diff_eq_of_exch (M.base_exchange') hB₁ hB₂ 

theorem Base.card_diff_comm (hB₁ : M.Base B₁) (hB₂ : M.Base B₂) :
    (B₁ \ B₂).ncard = (B₂ \ B₁).ncard := by
  rw [←encard_toNat_eq, hB₁.encard_diff_comm hB₂, encard_toNat_eq]

theorem Base.encard_eq_encard_of_base (hB₁ : M.Base B₁) (hB₂ : M.Base B₂) :
    B₁.encard = B₂.encard := by
  rw [encard_base_eq_of_exch M.base_exchange' hB₁ hB₂]

theorem Base.card_eq_card_of_base (hB₁ : M.Base B₁) (hB₂ : M.Base B₂) : B₁.ncard = B₂.ncard := by
  rw [←encard_toNat_eq B₁, hB₁.encard_eq_encard_of_base hB₂, encard_toNat_eq]

theorem Base.finite_of_finite (hB : M.Base B) (h : B.Finite) (hB' : M.Base B') : B'.Finite :=
  (finite_iff_finite_of_encard_eq_encard (hB.encard_eq_encard_of_base hB')).mp h  

theorem Base.infinite_of_infinite (hB : M.Base B) (h : B.Infinite) (hB₁ : M.Base B₁) :
    B₁.Infinite :=
  by_contra (fun hB_inf ↦ (hB₁.finite_of_finite (not_infinite.mp hB_inf) hB).not_infinite h)

theorem Base.finite [FiniteRk M] (hB : M.Base B) : B.Finite := 
  let ⟨B₀,hB₀⟩ := ‹FiniteRk M›.exists_finite_base
  hB₀.1.finite_of_finite hB₀.2 hB

theorem Base.infinite [InfiniteRk M] (hB : M.Base B) : B.Infinite :=
  let ⟨B₀,hB₀⟩ := ‹InfiniteRk M›.exists_infinite_base
  hB₀.1.infinite_of_infinite hB₀.2 hB

theorem Base.finiteRk_of_finite (hB : M.Base B) (hfin : B.Finite) : FiniteRk M := 
  ⟨⟨B, hB, hfin⟩⟩   

theorem Base.infiniteRk_of_infinite (hB : M.Base B) (h : B.Infinite) : InfiniteRk M := 
  ⟨⟨B, hB, h⟩⟩ 

theorem not_finiteRk (M : Matroid α) [InfiniteRk M] : ¬ FiniteRk M := by
  intro h; obtain ⟨B,hB⟩ := M.exists_base; exact hB.infinite hB.finite

theorem not_infiniteRk (M : Matroid α) [FiniteRk M] : ¬ InfiniteRk M := by
  intro h; obtain ⟨B,hB⟩ := M.exists_base; exact hB.infinite hB.finite

theorem finite_or_infiniteRk (M : Matroid α) : FiniteRk M ∨ InfiniteRk M :=
  let ⟨B, hB⟩ := M.exists_base
  B.finite_or_infinite.elim 
  (Or.inl ∘ hB.finiteRk_of_finite) (Or.inr ∘ hB.infiniteRk_of_infinite)

theorem Base.diff_finite_comm (hB₁ : M.Base B₁) (hB₂ : M.Base B₂) :
    (B₁ \ B₂).Finite ↔ (B₂ \ B₁).Finite := 
  finite_iff_finite_of_encard_eq_encard (hB₁.encard_diff_comm hB₂)

theorem Base.diff_infinite_comm (hB₁ : M.Base B₁) (hB₂ : M.Base B₂) : 
    (B₁ \ B₂).Infinite ↔ (B₂ \ B₁).Infinite := 
  infinite_iff_infinite_of_encard_eq_encard (hB₁.encard_diff_comm hB₂)

theorem Base.ncard_eq_ncard_of_base (hB₁ : M.Base B₁) (hB₂ : M.Base B₂) : B₁.ncard = B₂.ncard :=
by rw [←encard_toNat_eq, hB₁.encard_eq_encard_of_base hB₂, encard_toNat_eq]

theorem eq_of_base_iff_base_forall {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E) 
    (h : ∀ B, B ⊆ M₁.E → (M₁.Base B ↔ M₂.Base B)) : M₁ = M₂ := by
  apply Matroid.ext _ _ hE
  ext B
  exact ⟨fun h' ↦ (h _ h'.subset_ground).mp h', 
    fun h' ↦ (h _ (h'.subset_ground.trans_eq hE.symm)).mpr h'⟩

theorem base_compl_iff_mem_maximals_disjoint_base (hB : B ⊆ M.E := by aesop_mat) : 
    M.Base (M.E \ B) ↔ B ∈ maximals (· ⊆ ·) {I | I ⊆ M.E ∧ ∃ B, M.Base B ∧ Disjoint I B} := by
  simp_rw [mem_maximals_setOf_iff, and_iff_right hB, and_imp, forall_exists_index]
  refine' ⟨fun h ↦ ⟨⟨_, h, disjoint_sdiff_right⟩, 
    fun I hI B' ⟨hB', hIB'⟩ hBI ↦ hBI.antisymm _⟩, fun ⟨⟨ B', hB', hBB'⟩,h⟩ ↦ _⟩
  · rw [hB'.eq_of_subset_base h, ←subset_compl_iff_disjoint_right, diff_eq, compl_inter, 
      compl_compl] at hIB'
    · exact fun e he ↦  (hIB' he).elim (fun h' ↦ (h' (hI he)).elim) id
    rw [subset_diff, and_iff_right hB'.subset_ground, disjoint_comm]
    exact disjoint_of_subset_left hBI hIB'
  rw [h (diff_subset M.E B') B' ⟨hB', disjoint_sdiff_left⟩]
  · simpa [hB'.subset_ground]
  simp [subset_diff, hB, hBB']
  
end Base

section dep_indep

/-- A set is independent if it is contained in a Base.  -/
def Indep (M : Matroid α) (I : Set α) : Prop := ∃ B, M.Base B ∧ I ⊆ B 
pp_extended_field_notation Indep

/-- A subset of `M.E` is Dependent if it is not independent . -/
def Dep (M : Matroid α) (D : Set α) : Prop := ¬M.Indep D ∧ D ⊆ M.E   
pp_extended_field_notation Dep

theorem indep_iff_subset_base : M.Indep I ↔ ∃ B, M.Base B ∧ I ⊆ B := Iff.rfl

theorem setOf_indep_eq (M : Matroid α) : {I | M.Indep I} = lowerClosure ({B | M.Base B}) := rfl

theorem dep_iff : M.Dep D ↔ ¬M.Indep D ∧ D ⊆ M.E := Iff.rfl  

theorem setOf_dep_eq (M : Matroid α) : {D | M.Dep D} = {I | M.Indep I}ᶜ ∩ Iic M.E := rfl

@[aesop unsafe 30% (rule_sets [Matroid])]
theorem Indep.subset_ground (hI : M.Indep I) : I ⊆ M.E := by 
  obtain ⟨B, hB, hIB⟩ := hI
  exact hIB.trans hB.subset_ground 

@[aesop unsafe 20% (rule_sets [Matroid])]
theorem Dep.subset_ground (hD : M.Dep D) : D ⊆ M.E :=
  hD.2 

theorem indep_or_dep (hX : X ⊆ M.E := by aesop_mat) : M.Indep X ∨ M.Dep X := by 
  rw [Dep, and_iff_left hX]
  apply em

theorem Indep.not_dep (hI : M.Indep I) : ¬ M.Dep I := 
  fun h ↦ h.1 hI   

theorem Dep.not_indep (hD : M.Dep D) : ¬ M.Indep D := 
  hD.1  

theorem dep_of_not_indep (hD : ¬ M.Indep D) (hDE : D ⊆ M.E := by aesop_mat) : M.Dep D := 
  ⟨hD, hDE⟩ 

theorem indep_of_not_dep (hI : ¬ M.Dep I) (hIE : I ⊆ M.E := by aesop_mat) : M.Indep I := 
  by_contra (fun h ↦ hI ⟨h, hIE⟩)

@[simp] theorem not_dep_iff (hX : X ⊆ M.E := by aesop_mat) : ¬ M.Dep X ↔ M.Indep X := by
  rw [Dep, and_iff_left hX, not_not]

@[simp] theorem not_indep_iff (hX : X ⊆ M.E := by aesop_mat) : ¬ M.Indep X ↔ M.Dep X := by
  rw [Dep, and_iff_left hX]  

theorem indep_iff_not_dep : M.Indep I ↔ ¬M.Dep I ∧ I ⊆ M.E := by
  rw [dep_iff, not_and, not_imp_not]
  exact ⟨fun h ↦ ⟨fun _ ↦ h, h.subset_ground⟩, fun h ↦ h.1 h.2⟩
  
theorem Indep.exists_base_supset (hI : M.Indep I) : ∃ B, M.Base B ∧ I ⊆ B :=
  hI

theorem Indep.subset (hJ : M.Indep J) (hIJ : I ⊆ J) : M.Indep I :=
  let ⟨B, hB, hJB⟩ := hJ
  ⟨B, hB, hIJ.trans hJB⟩

theorem Dep.supset (hD : M.Dep D) (hDX : D ⊆ X) (hXE : X ⊆ M.E := by aesop_mat) : M.Dep X := 
  dep_of_not_indep (fun hI ↦ (hI.subset hDX).not_dep hD)

@[simp] theorem empty_indep (M : Matroid α) : M.Indep ∅ :=
  Exists.elim M.exists_base (fun B hB ↦ ⟨_, hB, B.empty_subset⟩)

theorem Dep.nonempty (hD : M.Dep D) : D.Nonempty := by
  rw [nonempty_iff_ne_empty]; rintro rfl; exact hD.not_indep M.empty_indep

theorem Indep.finite [FiniteRk M] (hI : M.Indep I) : I.Finite := 
  let ⟨_, hB, hIB⟩ := hI
  hB.finite.subset hIB  

theorem Indep.inter_right (hI : M.Indep I) (X : Set α) : M.Indep (I ∩ X) :=
  hI.subset (inter_subset_left _ _)

theorem Indep.inter_left (hI : M.Indep I) (X : Set α) : M.Indep (X ∩ I) :=
  hI.subset (inter_subset_right _ _)

theorem Indep.diff (hI : M.Indep I) (X : Set α) : M.Indep (I \ X) :=
  hI.subset (diff_subset _ _)

theorem Base.indep (hB : M.Base B) : M.Indep B :=
  ⟨B, hB, subset_rfl⟩

theorem Base.eq_of_subset_indep (hB : M.Base B) (hI : M.Indep I) (hBI : B ⊆ I) : B = I :=
  let ⟨B', hB', hB'I⟩ := hI
  hBI.antisymm (by rwa [hB.eq_of_subset_base hB' (hBI.trans hB'I)])

theorem base_iff_maximal_indep : M.Base B ↔ M.Indep B ∧ ∀ I, M.Indep I → B ⊆ I → B = I := by
  refine' ⟨fun h ↦ ⟨h.indep, fun _ ↦ h.eq_of_subset_indep ⟩, fun h ↦ _⟩
  obtain ⟨⟨B', hB', hBB'⟩, h⟩ := h
  rwa [h _ hB'.indep hBB']
  
theorem setOf_base_eq_maximals_setOf_indep : {B | M.Base B} = maximals (· ⊆ ·) {I | M.Indep I} := by
  ext B; rw [mem_maximals_setOf_iff, mem_setOf, base_iff_maximal_indep]

theorem Indep.base_of_maximal (hI : M.Indep I) (h : ∀ J, M.Indep J → I ⊆ J → I = J) : M.Base I := 
  base_iff_maximal_indep.mpr ⟨hI,h⟩

theorem Base.dep_of_ssubset (hB : M.Base B) (h : B ⊂ X) (hX : X ⊆ M.E := by aesop_mat) : M.Dep X :=
  ⟨λ hX ↦ h.ne (hB.eq_of_subset_indep hX h.subset), hX⟩

theorem Base.dep_of_insert (hB : M.Base B) (heB : e ∉ B) (he : e ∈ M.E := by aesop_mat) : 
    M.Dep (insert e B) := hB.dep_of_ssubset (ssubset_insert heB) (insert_subset he hB.subset_ground)

/-- If the difference of two Bases is a singleton, then they differ by an insertion/removal -/
theorem Base.eq_exchange_of_diff_eq_singleton (hB : M.Base B) (hB' : M.Base B') (h : B \ B' = {e}) : 
  ∃ f ∈ B' \ B, B' = (insert f B) \ {e} := by
  obtain ⟨f, hf, hb⟩ := hB.exchange hB' (h.symm.subset (mem_singleton e))
  have hne : f ≠ e := by rintro rfl; exact hf.2 (h.symm.subset (mem_singleton f)).1
  rw [insert_diff_singleton_comm hne] at hb
  refine ⟨f, hf, (hb.eq_of_subset_base hB' ?_).symm⟩
  rw [diff_subset_iff, insert_subset_iff, union_comm, ←diff_subset_iff, h, and_iff_left rfl.subset]
  exact Or.inl hf.1

theorem Base.exchange_base_of_indep (hB : M.Base B) (hf : f ∉ B) 
    (hI : M.Indep (insert f (B \ {e}))) : M.Base (insert f (B \ {e})) := by
  obtain ⟨B', hB', hIB'⟩ := hI.exists_base_supset
  have hcard := hB'.encard_diff_comm hB
  rw [insert_subset_iff, ←diff_eq_empty, diff_diff_comm, diff_eq_empty, subset_singleton_iff_eq] 
    at hIB'
  obtain ⟨hfB, (h | h)⟩ := hIB'
  · rw [h, encard_empty, encard_eq_zero, eq_empty_iff_forall_not_mem] at hcard
    exact (hcard f ⟨hfB, hf⟩).elim
  rw [h, encard_singleton, encard_eq_one] at hcard
  obtain ⟨x, hx⟩ := hcard
  obtain (rfl : f = x) := hx.subset ⟨hfB, hf⟩
  simp_rw [←h, ←singleton_union, ←hx, sdiff_sdiff_right_self, inf_eq_inter, inter_comm B, 
    diff_union_inter]
  exact hB'

theorem Base.exchange_base_of_indep' (hB : M.Base B) (he : e ∈ B) (hf : f ∉ B) 
    (hI : M.Indep (insert f B \ {e})) : M.Base (insert f B \ {e}) := by
  have hfe : f ≠ e := by rintro rfl; exact hf he
  rw [←insert_diff_singleton_comm hfe] at *
  exact hB.exchange_base_of_indep hf hI

theorem Base.insert_dep (hB : M.Base B) (h : e ∈ M.E \ B) : M.Dep (insert e B) := by
  rw [←not_indep_iff (insert_subset h.1 hB.subset_ground)]
  exact h.2 ∘ (fun hi ↦ insert_eq_self.mp (hB.eq_of_subset_indep hi (subset_insert e B)).symm)
  
theorem Indep.exists_insert_of_not_base (hI : M.Indep I) (hI' : ¬M.Base I) (hB : M.Base B) : 
    ∃ e ∈ B \ I, M.Indep (insert e I) := by
  obtain ⟨B', hB', hIB'⟩ := hI.exists_base_supset
  obtain ⟨x, hxB', hx⟩ := exists_of_ssubset (hIB'.ssubset_of_ne (by (rintro rfl; exact hI' hB'))) 
  obtain (hxB | hxB) := em (x ∈ B)
  · exact ⟨x, ⟨hxB, hx⟩ , ⟨B', hB', insert_subset hxB' hIB'⟩⟩ 
  obtain ⟨e,he, hBase⟩ := hB'.exchange hB ⟨hxB',hxB⟩    
  exact ⟨e, ⟨he.1, not_mem_subset hIB' he.2⟩, 
    ⟨_, hBase, insert_subset_insert (subset_diff_singleton hIB' hx)⟩⟩

theorem ground_indep_iff_base : M.Indep M.E ↔ M.Base M.E :=
  ⟨fun h ↦ h.base_of_maximal (fun _ hJ hEJ ↦ hEJ.antisymm hJ.subset_ground), Base.indep⟩

theorem Base.exists_insert_of_ssubset (hB : M.Base B) (hIB : I ⊂ B) (hB' : M.Base B') : 
  ∃ e ∈ B' \ I, M.Indep (insert e I) :=
(hB.indep.subset hIB.subset).exists_insert_of_not_base 
    (fun hI ↦ hIB.ne (hI.eq_of_subset_base hB hIB.subset)) hB'

theorem eq_of_indep_iff_indep_forall {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E) 
    (h : ∀ I, I ⊆ M₁.E → (M₁.Indep I ↔ M₂.Indep I)) : M₁ = M₂ :=
  let h' : ∀ I, M₁.Indep I ↔ M₂.Indep I := fun I ↦ 
    (em (I ⊆ M₁.E)).elim (h I) (fun h' ↦ iff_of_false (fun hi ↦ h' (hi.subset_ground)) 
      (fun hi ↦ h' (hi.subset_ground.trans_eq hE.symm)))
  eq_of_base_iff_base_forall hE (fun B _ ↦ by simp_rw [base_iff_maximal_indep, h']) 
  
theorem eq_iff_indep_iff_indep_forall {M₁ M₂ : Matroid α} : 
  M₁ = M₂ ↔ (M₁.E = M₂.E) ∧ ∀ I, I ⊆ M₁.E → (M₁.Indep I ↔ M₂.Indep I) :=
⟨fun h ↦ by (subst h; simp), fun h ↦ eq_of_indep_iff_indep_forall h.1 h.2⟩  

end dep_indep

section Basis

def Basis' (M : Matroid α) (I X : Set α) : Prop := 
  I ∈ maximals (· ⊆ ·) {A | M.Indep A ∧ A ⊆ X}
pp_extended_field_notation Basis'

/-- A Basis for a set `X ⊆ M.E` is a maximal independent subset of `X`
  (Often in the literature, the word 'Basis' is used to refer to what we call a 'Base'). -/
def Basis (M : Matroid α) (I X : Set α) : Prop := 
  I ∈ maximals (· ⊆ ·) {A | M.Indep A ∧ A ⊆ X} ∧ X ⊆ M.E  
pp_extended_field_notation Basis

theorem Basis'.indep (hI : M.Basis' I X) : M.Indep I :=
  hI.1.1

theorem Basis.indep (hI : M.Basis I X) : M.Indep I :=
  hI.1.1.1

theorem Basis.subset (hI : M.Basis I X) : I ⊆ X :=
  hI.1.1.2

theorem Basis.basis' (hI : M.Basis I X) : M.Basis' I X := 
  hI.1 

theorem Basis'.basis (hI : M.Basis' I X) (hX : X ⊆ M.E := by aesop_mat) : M.Basis I X := 
  ⟨hI, hX⟩ 

theorem Basis'.subset (hI : M.Basis' I X) : I ⊆ X :=
  hI.1.2

theorem setOf_basis_eq (M : Matroid α) (hX : X ⊆ M.E := by aesop_mat) : 
    {I | M.Basis I X} = maximals (· ⊆ ·) ({I | M.Indep I} ∩ Iic X) := by
  ext I; simp [Matroid.Basis, maximals, iff_true_intro hX] 
  
@[aesop unsafe 15% (rule_sets [Matroid])]
theorem Basis.subset_ground (hI : M.Basis I X) : X ⊆ M.E :=
  hI.2 

theorem Basis.basis_inter_ground (hI : M.Basis I X) : M.Basis I (X ∩ M.E) := by
  convert hI
  rw [inter_eq_self_of_subset_left hI.subset_ground]

@[aesop unsafe 15% (rule_sets [Matroid])]
theorem Basis.left_subset_ground (hI : M.Basis I X) : I ⊆ M.E := 
  hI.indep.subset_ground

theorem Basis.eq_of_subset_indep (hI : M.Basis I X) (hJ : M.Indep J) (hIJ : I ⊆ J) (hJX : J ⊆ X) :
    I = J :=
  hIJ.antisymm (hI.1.2 ⟨hJ, hJX⟩ hIJ)

theorem Basis.Finite (hI : M.Basis I X) [FiniteRk M] : I.Finite := hI.indep.finite 

theorem basis_iff' : 
    M.Basis I X ↔ (M.Indep I ∧ I ⊆ X ∧ ∀ J, M.Indep J → I ⊆ J → J ⊆ X → I = J) ∧ X ⊆ M.E := by
  simp [Basis, mem_maximals_setOf_iff, and_assoc, and_congr_left_iff, and_imp, 
    and_congr_left_iff, and_congr_right_iff, @Imp.swap (_ ⊆ X)]

theorem basis_iff (hX : X ⊆ M.E := by aesop_mat) : 
  M.Basis I X ↔ (M.Indep I ∧ I ⊆ X ∧ ∀ J, M.Indep J → I ⊆ J → J ⊆ X → I = J) :=
by rw [basis_iff', and_iff_left hX]

theorem basis'_iff_basis_inter_ground : M.Basis' I X ↔ M.Basis I (X ∩ M.E) := by
  rw [Basis', Basis, and_iff_left (inter_subset_right _ _)]
  convert Iff.rfl using 3
  ext I 
  simp only [subset_inter_iff, mem_setOf_eq, and_congr_right_iff, and_iff_left_iff_imp]
  exact fun h _ ↦ h.subset_ground

theorem Basis'.basis_inter_ground (hIX : M.Basis' I X) : M.Basis I (X ∩ M.E) :=
  basis'_iff_basis_inter_ground.mp hIX

theorem Basis'.eq_of_subset_indep (hI : M.Basis' I X) (hJ : M.Indep J) (hIJ : I ⊆ J) 
    (hJX : J ⊆ X) : I = J := 
  hIJ.antisymm (hI.2 ⟨hJ, hJX⟩ hIJ)

theorem basis_iff_mem_maximals (hX : X ⊆ M.E := by aesop_mat): 
    M.Basis I X ↔ I ∈ maximals (· ⊆ ·) {I | M.Indep I ∧ I ⊆ X} := by
  rw [Basis, and_iff_left hX]

theorem basis_iff_mem_maximals_Prop (hX : X ⊆ M.E := by aesop_mat): 
    M.Basis I X ↔ I ∈ maximals (· ⊆ ·) (fun I ↦ M.Indep I ∧ I ⊆ X) :=
  basis_iff_mem_maximals

theorem Indep.basis_of_maximal_subset (hI : M.Indep I) (hIX : I ⊆ X)
    (hmax : ∀ ⦃J⦄, M.Indep J → I ⊆ J → J ⊆ X → J ⊆ I) (hX : X ⊆ M.E := by aesop_mat) : M.Basis I X := by
  rw [basis_iff (by aesop_mat : X ⊆ M.E), and_iff_right hI, and_iff_right hIX]
  exact fun J hJ hIJ hJX ↦ hIJ.antisymm (hmax hJ hIJ hJX)

theorem Basis.basis_subset (hI : M.Basis I X) (hIY : I ⊆ Y) (hYX : Y ⊆ X) : M.Basis I Y := by
  rw [basis_iff (hYX.trans hI.subset_ground), and_iff_right hI.indep, and_iff_right hIY] 
  exact fun J hJ hIJ hJY ↦ hI.eq_of_subset_indep hJ hIJ (hJY.trans hYX) 

@[simp] theorem basis_self_iff_indep : M.Basis I I ↔ M.Indep I := by
  rw [basis_iff', and_iff_right rfl.subset, and_assoc, and_iff_left_iff_imp] 
  exact fun hi ↦ ⟨fun _ _ ↦ subset_antisymm, hi.subset_ground⟩ 
  
theorem Indep.basis_self (h : M.Indep I) : M.Basis I I :=
  basis_self_iff_indep.mpr h

@[simp] theorem basis_empty_iff (M : Matroid α) : M.Basis I ∅ ↔ I = ∅ :=
  ⟨fun h ↦ subset_empty_iff.mp h.subset, fun h ↦ by (rw [h]; exact M.empty_indep.basis_self)⟩
  
theorem Basis.dep_of_ssubset (hI : M.Basis I X) (hIY : I ⊂ Y) (hYX : Y ⊆ X) : M.Dep Y := by
  have : X ⊆ M.E := hI.subset_ground
  rw [←not_indep_iff]
  exact fun hY ↦ hIY.ne (hI.eq_of_subset_indep hY hIY.subset hYX)

theorem Basis.insert_dep (hI : M.Basis I X) (he : e ∈ X \ I) : M.Dep (insert e I) :=
  hI.dep_of_ssubset (ssubset_insert he.2) (insert_subset he.1 hI.subset)

theorem Basis.mem_of_insert_indep (hI : M.Basis I X) (he : e ∈ X) (hIe : M.Indep (insert e I)) : 
    e ∈ I :=
  by_contra (fun heI ↦ (hI.insert_dep ⟨he, heI⟩).not_indep hIe) 

theorem Basis.not_basis_of_ssubset (hI : M.Basis I X) (hJI : J ⊂ I) : ¬ M.Basis J X :=
  fun h ↦ hJI.ne (h.eq_of_subset_indep hI.indep hJI.subset hI.subset)

theorem Indep.subset_basis_of_subset (hI : M.Indep I) (hIX : I ⊆ X) (hX : X ⊆ M.E := by aesop_mat) : 
    ∃ J, M.Basis J X ∧ I ⊆ J := by
  obtain ⟨J, ⟨(hJ : M.Indep J),hIJ,hJX⟩, hJmax⟩ := M.maximality' X hX I hI hIX
  use J
  rw [and_iff_left hIJ, basis_iff, and_iff_right hJ, and_iff_right hJX]
  exact fun K hK hJK hKX ↦ hJK.antisymm (hJmax ⟨hK, hIJ.trans hJK, hKX⟩ hJK)

theorem Indep.subset_basis'_of_subset (hI : M.Indep I) (hIX : I ⊆ X) :
    ∃ J, M.Basis' J X ∧ I ⊆ J := by
  simp_rw [basis'_iff_basis_inter_ground]
  exact hI.subset_basis_of_subset (subset_inter hIX hI.subset_ground)
  
theorem exists_basis (M : Matroid α) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    ∃ I, M.Basis I X :=
  let ⟨_, hI, _⟩ := M.empty_indep.subset_basis_of_subset (empty_subset X) 
  ⟨_,hI⟩

theorem exists_basis' (M : Matroid α) (X : Set α) : ∃ I, M.Basis' I X :=
  let ⟨_, hI, _⟩ := M.empty_indep.subset_basis'_of_subset (empty_subset X) 
  ⟨_,hI⟩

theorem exists_basis_subset_basis (M : Matroid α) (hXY : X ⊆ Y) (hY : Y ⊆ M.E := by aesop_mat) :
    ∃ I J, M.Basis I X ∧ M.Basis J Y ∧ I ⊆ J := by
  obtain ⟨I, hI⟩ := M.exists_basis X (hXY.trans hY)
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_basis_of_subset (hI.subset.trans hXY)
  exact ⟨_, _, hI, hJ, hIJ⟩ 

theorem Basis.exists_basis_inter_eq_of_supset (hI : M.Basis I X) (hXY : X ⊆ Y) 
    (hY : Y ⊆ M.E := by aesop_mat) : ∃ J, M.Basis J Y ∧ J ∩ X = I := by
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_basis_of_subset (hI.subset.trans hXY)
  refine ⟨J, hJ, subset_antisymm ?_ (subset_inter hIJ hI.subset)⟩
  exact fun e he ↦ hI.mem_of_insert_indep he.2 (hJ.indep.subset (insert_subset he.1 hIJ))

theorem exists_basis_union_inter_basis (M : Matroid α) (X Y : Set α) (hX : X ⊆ M.E := by aesop_mat) 
    (hY : Y ⊆ M.E := by aesop_mat) : ∃ I, M.Basis I (X ∪ Y) ∧ M.Basis (I ∩ Y) Y :=
  let ⟨J, hJ⟩ := M.exists_basis Y
  (hJ.exists_basis_inter_eq_of_supset (subset_union_right X Y)).imp 
  (fun I hI ↦ ⟨hI.1, by rwa [hI.2]⟩)

theorem Indep.eq_of_basis (hI : M.Indep I) (hJ : M.Basis J I) : J = I :=
  hJ.eq_of_subset_indep hI hJ.subset rfl.subset

theorem Basis.exists_base (hI : M.Basis I X) : ∃ B, M.Base B ∧ I = B ∩ X := 
  let ⟨B,hB, hIB⟩ := hI.indep
  ⟨B, hB, subset_antisymm (subset_inter hIB hI.subset) 
    (by rw [hI.eq_of_subset_indep (hB.indep.inter_right X) (subset_inter hIB hI.subset)
    (inter_subset_right _ _)])⟩ 

@[simp] theorem basis_ground_iff : M.Basis B M.E ↔ M.Base B := by
  rw [base_iff_maximal_indep, basis_iff', and_assoc, and_congr_right]
  rw [and_iff_left (rfl.subset : M.E ⊆ M.E)]
  exact fun h ↦ ⟨fun h' I hI hBI ↦ h'.2 _ hI hBI hI.subset_ground,
    fun h' ↦ ⟨h.subset_ground,fun J hJ hBJ _ ↦ h' J hJ hBJ⟩⟩ 

theorem Base.basis_ground (hB : M.Base B) : M.Basis B M.E :=
  basis_ground_iff.mpr hB

theorem Indep.basis_iff_forall_insert_dep (hI : M.Indep I) (hIX : I ⊆ X) : 
    M.Basis I X ↔ ∀ e ∈ X \ I, M.Dep (insert e I) := by
  rw [basis_iff', and_iff_right hIX, and_iff_right hI]
  refine' ⟨fun h e he ↦ ⟨fun hi ↦ he.2 _, insert_subset (h.2 he.1) hI.subset_ground⟩, 
    fun h ↦ ⟨fun J hJ hIJ hJX ↦ hIJ.antisymm (fun e heJ ↦ by_contra (fun heI ↦ _)),_⟩⟩
  · exact (h.1 _ hi (subset_insert _ _) (insert_subset he.1 hIX)).symm.subset (mem_insert e I)
  · exact (h e ⟨hJX heJ, heI⟩).not_indep (hJ.subset (insert_subset heJ hIJ))
  rw [←diff_union_of_subset hIX, union_subset_iff, and_iff_left hI.subset_ground]
  exact fun e he ↦ (h e he).subset_ground (mem_insert _ _)

theorem Indep.basis_of_forall_insert (hI : M.Indep I) (hIX : I ⊆ X) 
    (he : ∀ e ∈ X \ I, M.Dep (insert e I)) : M.Basis I X :=
  (hI.basis_iff_forall_insert_dep hIX).mpr he
  
theorem Indep.basis_insert_iff (hI : M.Indep I) :
    M.Basis I (insert e I) ↔ M.Dep (insert e I) ∨ e ∈ I := by 
  simp_rw [insert_subset_iff, and_iff_left hI.subset_ground, or_iff_not_imp_right, 
    hI.basis_iff_forall_insert_dep (subset_insert _ _), dep_iff, insert_subset_iff, 
    and_iff_left hI.subset_ground, mem_diff, mem_insert_iff, or_and_right, and_not_self, 
    or_false, and_imp, forall_eq]
    
theorem Basis.iUnion_basis_iUnion {ι : Type _} (X I : ι → Set α) (hI : ∀ i, M.Basis (I i) (X i)) 
    (h_ind : M.Indep (⋃ i, I i)) : M.Basis (⋃ i, I i) (⋃ i, X i) := by
  refine' h_ind.basis_of_forall_insert 
    (iUnion_subset (fun i ↦ (hI i).subset.trans (subset_iUnion _ _))) _
  rintro e ⟨⟨_, ⟨⟨i, hi, rfl⟩, (hes : e ∈ X i)⟩⟩, he'⟩
  rw [mem_iUnion, not_exists] at he'
  refine' ((hI i).insert_dep ⟨hes, he' _⟩).supset (insert_subset_insert (subset_iUnion _ _)) _
  rw [insert_subset_iff, iUnion_subset_iff, and_iff_left (fun i ↦ (hI i).indep.subset_ground)]
  exact (hI i).subset_ground hes

theorem Basis.basis_iUnion {ι : Type _} [Nonempty ι] (X : ι → Set α) (hI : ∀ i, M.Basis I (X i)) : 
    M.Basis I (⋃ i, X i) := by
  convert Basis.iUnion_basis_iUnion X (fun _ ↦ I) (fun i ↦ hI i) _ <;> rw [iUnion_const]
  exact (hI (Classical.arbitrary ι)).indep
  
theorem Basis.basis_sUnion {Xs : Set (Set α)} (hne : Xs.Nonempty) (h : ∀ X ∈ Xs, M.Basis I X) :
    M.Basis I (⋃₀ Xs) := by
  rw [sUnion_eq_iUnion]
  have := Iff.mpr nonempty_coe_sort hne
  exact Basis.basis_iUnion _ fun X ↦ (h X X.prop)

-- theorem Basis.basis_of_subset_of_forall_basis_insert (hIX : I ⊆ X) 
--     (h : ∀ x ∈ X, M.Basis I (insert x I)) : M.Basis I X := by
--   obtain (rfl | ⟨e,he⟩) := X.eq_empty_or_nonempty
--   · obtain rfl := subset_empty_iff.mp hIX; exact M.empty_indep.basis_self
--   have hne : {insert x I | x ∈ X}.Nonempty := ⟨_, ⟨e, he, rfl⟩⟩
--   convert Basis.basis_sUnion (M := M) (I := I) hne _
--   · ext f
--     simp only [mem_sUnion, mem_setOf_eq, exists_exists_and_eq_and, mem_insert_iff]
--     exact ⟨fun h ↦ ⟨_, h, Or.inl rfl⟩, 
--       fun ⟨a, ha, h'⟩ ↦ h'.elim (fun ha ↦ by rwa [ha]) (fun hf ↦ hIX hf)⟩
--   rintro Y ⟨f, hf, rfl⟩
--   exact h f hf


/- This follows from `Basis.basis_iUnion`, but the overhead seems too high. -/
theorem Indep.basis_setOf_insert_basis (hI : M.Indep I) :
    M.Basis I {x | M.Basis I (insert x I)} := by
  refine' hI.basis_of_forall_insert (fun e he ↦ (_ : M.Basis _ _))
    (fun e he ↦ ⟨fun hu ↦ he.2 _, he.1.subset_ground⟩)
  · rw [insert_eq_of_mem he]; exact hI.basis_self
  simpa using (hu.eq_of_basis he.1).symm
  
  -- refine' Basis.basis_of_subset_of_forall_basis_insert (fun e heI ↦ _) (fun _ ↦ id)
  -- rw [mem_setOf, insert_eq_of_mem heI]
  -- exact hI.basis_self
  -- -- obtain (he | hne) := {x | M.Basis I (insert x I)}.eq_empty_or_nonempty
  -- -- · rw [he, basis_empty_iff, ←subset_empty_iff, ←he]
  -- --   rintro e he'; rw [mem_setOf, insert_eq_of_mem he']; exact hI.basis_self
  -- -- -- have' := Basis.basis_sUnion hne
  -- -- have := hne.coe_sort
  -- -- rw [←iUnion_of_singleton_coe {x | M.Basis I (insert x I)}]
  -- -- apply Basis.basis_iUnion
  
  


theorem Basis.union_basis_union (hIX : M.Basis I X) (hJY : M.Basis J Y) (h : M.Indep (I ∪ J)) : 
    M.Basis (I ∪ J) (X ∪ Y) := by
  rw [union_eq_iUnion, union_eq_iUnion]
  refine' Basis.iUnion_basis_iUnion _ _ _ _
  · simp only [Bool.forall_bool, cond_false, cond_true]; exact ⟨hJY, hIX⟩  
  rwa [←union_eq_iUnion]
  
theorem Basis.basis_union (hIX : M.Basis I X) (hIY : M.Basis I Y) : M.Basis I (X ∪ Y) := by
    convert hIX.union_basis_union hIY _ <;> rw [union_self]; exact hIX.indep

theorem Basis.basis_union_of_subset (hI : M.Basis I X) (hJ : M.Indep J) (hIJ : I ⊆ J) : 
    M.Basis J (J ∪ X) := by
  convert hJ.basis_self.union_basis_union hI _ <;>
  rw [union_eq_self_of_subset_right hIJ]
  assumption

theorem Basis.insert_basis_insert (hI : M.Basis I X) (h : M.Indep (insert e I)) : 
    M.Basis (insert e I) (insert e X) := by
  simp_rw [←union_singleton] at *
  exact hI.union_basis_union (h.subset (subset_union_right _ _)).basis_self h

theorem Base.base_of_basis_supset (hB : M.Base B) (hBX : B ⊆ X) (hIX : M.Basis I X) : M.Base I := by
  by_contra h
  obtain ⟨e,heBI,he⟩ := hIX.indep.exists_insert_of_not_base h hB
  exact heBI.2 (hIX.mem_of_insert_indep (hBX heBI.1) he)

theorem Indep.exists_base_subset_union_base (hI : M.Indep I) (hB : M.Base B) : 
    ∃ B', M.Base B' ∧ I ⊆ B' ∧ B' ⊆ I ∪ B := by
  obtain ⟨B', hB', hIB'⟩ := hI.subset_basis_of_subset (subset_union_left I B)
  exact ⟨B', hB.base_of_basis_supset (subset_union_right _ _) hB', hIB', hB'.subset⟩

theorem Basis.inter_eq_of_subset_indep (hIX : M.Basis I X) (hIJ : I ⊆ J) (hJ : M.Indep J) : 
  J ∩ X = I :=
(subset_inter hIJ hIX.subset).antisymm' 
  (fun _ he ↦ hIX.mem_of_insert_indep he.2 (hJ.subset (insert_subset he.1 hIJ))) 

theorem Base.basis_of_subset (hX : X ⊆ M.E := by aesop_mat) (hB : M.Base B) (hBX : B ⊆ X) : 
    M.Basis B X := by
  rw [basis_iff, and_iff_right hB.indep, and_iff_right hBX]
  exact fun J hJ hBJ _ ↦ hB.eq_of_subset_indep hJ hBJ

end Basis
section from_axioms

/-- A constructor for matroids via the base axioms. 
  (In fact, just a wrapper for the definition of a matroid) -/
def matroid_of_base (E : Set α) (Base : Set α → Prop) (exists_base : ∃ B, Base B) 
    (base_exchange : exchange_property Base) 
    (maximality : ∀ X, X ⊆ E → exists_maximal_subset_property (fun I ↦ ∃ B, Base B ∧ I ⊆ B) X)
    (support : ∀ B, Base B → B ⊆ E) : Matroid α := 
  ⟨E, Base, exists_base, base_exchange, maximality, support⟩

@[simp] theorem matroid_of_base_apply (E : Set α) (Base : Set α → Prop) (exists_base : ∃ B, Base B)
    (base_exchange : exchange_property Base) 
    (maximality : ∀ X, X ⊆ E → exists_maximal_subset_property (fun I ↦ ∃ B, Base B ∧ I ⊆ B) X)
    (support : ∀ B, Base B → B ⊆ E) : 
    (matroid_of_base E Base exists_base base_exchange maximality support).Base = Base := rfl

/-- A version of the independence axioms that avoids cardinality -/
def matroid_of_indep (E : Set α) (Indep : Set α → Prop) (h_empty : Indep ∅) 
    (h_subset : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I) 
    (h_aug : ∀⦃I B⦄, Indep I → I ∉ maximals (· ⊆ ·) (setOf Indep) → 
      B ∈ maximals (· ⊆ ·) (setOf Indep) → ∃ x ∈ B \ I, Indep (insert x I))
    (h_maximal : ∀ X, X ⊆ E → exists_maximal_subset_property Indep X) 
    (h_support : ∀ I, Indep I → I ⊆ E) : Matroid α :=
  matroid_of_base E (· ∈ maximals (· ⊆ ·) (setOf Indep))
  ( by 
      obtain ⟨B, ⟨hB,-,-⟩, hB₁⟩ := h_maximal E rfl.subset ∅ h_empty (empty_subset _)
      exact ⟨B, ⟨hB, fun B' hB' hBB' ↦ hB₁ ⟨hB', empty_subset _,h_support B' hB'⟩ hBB'⟩⟩ )
  ( by 
      rintro B B' ⟨hB, hBmax⟩ ⟨hB',hB'max⟩ e he
      have hnotmax : B \ {e} ∉ maximals (· ⊆ ·) (setOf Indep)
      { simp only [mem_maximals_setOf_iff, diff_singleton_subset_iff, not_and, not_forall,
          exists_prop, exists_and_left]
        exact fun _ ↦ ⟨B, hB, subset_insert _ _, by simpa using he.1⟩ }
      
      obtain ⟨f,hf,hfB⟩ := h_aug (h_subset hB (diff_subset B {e})) hnotmax ⟨hB',hB'max⟩
      simp only [mem_diff, mem_singleton_iff, not_and, not_not] at hf 
      
      have hfB' : f ∉ B := by (intro hfB; obtain rfl := hf.2 hfB; exact he.2 hf.1)
      
      refine' ⟨f, ⟨hf.1, hfB'⟩, by_contra (fun hnot ↦ _)⟩
      obtain ⟨x,hxB, hind⟩ :=  h_aug hfB hnot ⟨hB, hBmax⟩ 
      simp only [mem_diff, mem_insert_iff, mem_singleton_iff, not_or, not_and, not_not] at hxB
      obtain rfl := hxB.2.2 hxB.1
      rw [insert_comm, insert_diff_singleton, insert_eq_of_mem he.1] at hind 
      exact not_mem_subset (hBmax hind (subset_insert _ _)) hfB' (mem_insert _ _) ) 
  ( by
      rintro X hXE I ⟨hB, hB, hIB⟩ hIX 
      obtain ⟨J, ⟨hJ, hIJ, hJX⟩, hJmax⟩ := h_maximal X hXE I (h_subset hB.1 hIB) hIX
      obtain ⟨BJ, hBJ⟩ := h_maximal E rfl.subset J hJ (h_support J hJ) 
      refine' ⟨J, ⟨⟨BJ,_, hBJ.1.2.1⟩ ,hIJ,hJX⟩, _⟩  
      · exact ⟨hBJ.1.1, fun B' hB' hBJB' ↦ hBJ.2 ⟨hB',hBJ.1.2.1.trans hBJB', h_support _ hB'⟩ hBJB'⟩
      simp only [maximals, mem_setOf_eq, and_imp, forall_exists_index]
      rintro A B' (hBi' : Indep _) - hB'' hIA hAX hJA
      simp only [mem_setOf_eq, and_imp] at hJmax 
      exact hJmax (h_subset hBi' hB'') hIA hAX hJA ) 
  ( fun B hB ↦ h_support B hB.1 )

@[simp] theorem matroid_of_indep_apply (E : Set α) (Indep : Set α → Prop) (h_empty : Indep ∅) 
    (h_subset : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I) 
    (h_aug : ∀⦃I B⦄, Indep I → I ∉ maximals (· ⊆ ·) (setOf Indep) → 
      B ∈ maximals (· ⊆ ·) (setOf Indep) → ∃ x ∈ B \ I, Indep (insert x I))
    (h_maximal : ∀ X, X ⊆ E → exists_maximal_subset_property Indep X) 
    (h_support : ∀ I, Indep I → I ⊆ E) : 
    (matroid_of_indep E Indep h_empty h_subset h_aug h_maximal h_support).Indep = Indep := by
  ext I
  simp_rw [indep_iff_subset_base, matroid_of_indep, matroid_of_base_apply, mem_maximals_setOf_iff]
  refine' ⟨fun ⟨B, ⟨hBi, _⟩, hIB⟩ ↦ h_subset hBi hIB, fun h ↦ _⟩
  obtain ⟨B, hB⟩ := h_maximal E rfl.subset I h (h_support I h)
  simp_rw [mem_maximals_setOf_iff, and_imp] at hB
  exact ⟨B, ⟨hB.1.1, fun J hJ hBJ ↦ hB.2 hJ (hB.1.2.1.trans hBJ) (h_support J hJ) hBJ⟩, hB.1.2.1⟩  

/-- If there is an absolute upper bound on the size of a set satisfying `P`, then the 
  maximal subset property always holds. -/
theorem Matroid.exists_maximal_subset_property_of_bdd {P : Set α → Prop} 
    (hP : ∃ (n : ℕ), ∀ Y, P Y → Y.encard ≤ n) (X : Set α) : exists_maximal_subset_property P X := by
  obtain ⟨n, hP⟩ := hP
  simp_rw [encard_le_coe_iff] at hP
  rintro I hI hIX
  have hfin : Set.Finite (ncard '' {Y | P Y ∧ I ⊆ Y ∧ Y ⊆ X})
  · rw [Finset.finite_iff_bddAbove, bddAbove_def]
    use n
    rintro x ⟨Y, ⟨hY,-,-⟩, rfl⟩
    exact (hP Y hY).2
  obtain ⟨Y, hY, hY'⟩ := Finite.exists_maximal_wrt' ncard _ hfin ⟨I, hI, rfl.subset, hIX⟩
  refine' ⟨Y, hY, fun J ⟨hJ, hIJ, hJX⟩ (hYJ : Y ⊆ J) ↦ (_ : J ⊆ Y)⟩
  have hJfin := (hP J hJ).1
  refine' (eq_of_subset_of_ncard_le hYJ _ hJfin).symm.subset
  rw [hY' J ⟨hJ, hIJ, hJX⟩ (ncard_le_of_subset hYJ hJfin)]

/-- If there is an absolute upper bound on the size of an independent set, then the maximality axiom 
  isn't needed to define a matroid by independent sets. -/
def matroid_of_indep_of_bdd (E : Set α) (Indep : Set α → Prop) (h_empty : Indep ∅) 
    (h_subset : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I) 
    (h_aug : ∀⦃I B⦄, Indep I → I ∉ maximals (· ⊆ ·) (setOf Indep) → 
      B ∈ maximals (· ⊆ ·) (setOf Indep) → ∃ x ∈ B \ I, Indep (insert x I))
    (h_bdd : ∃ (n : ℕ), ∀ I, Indep I → I.encard ≤ n )
    (h_support : ∀ I, Indep I → I ⊆ E) : Matroid α :=
  matroid_of_indep E Indep h_empty h_subset h_aug 
    (fun X _ ↦ Matroid.exists_maximal_subset_property_of_bdd h_bdd X) h_support 

@[simp] theorem matroid_of_indep_of_bdd_apply (E : Set α) (Indep : Set α → Prop) (h_empty : Indep ∅) 
    (h_subset : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I) 
    (h_aug : ∀⦃I B⦄, Indep I → I ∉ maximals (· ⊆ ·) (setOf Indep) → 
      B ∈ maximals (· ⊆ ·) (setOf Indep) → ∃ x ∈ B \ I, Indep (insert x I))
    (h_bdd : ∃ (n : ℕ), ∀ I, Indep I → I.encard ≤ n) (h_support : ∀ I, Indep I → I ⊆ E) : 
    (matroid_of_indep_of_bdd E Indep h_empty h_subset h_aug h_bdd h_support).Indep = Indep := by
  simp [matroid_of_indep_of_bdd]

/-- `matroid_of_indep_of_bdd` constructs a `FiniteRk` matroid. -/
instance (E : Set α) (Indep : Set α → Prop) (h_empty : Indep ∅) 
    (h_subset : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I) 
    (h_aug : ∀⦃I B⦄, Indep I → I ∉ maximals (· ⊆ ·) (setOf Indep) → 
      B ∈ maximals (· ⊆ ·) (setOf Indep) → ∃ x ∈ B \ I, Indep (insert x I))
    (h_bdd : ∃ (n : ℕ), ∀ I, Indep I → I.encard ≤ n ) 
    (h_support : ∀ I, Indep I → I ⊆ E) : 
    Matroid.FiniteRk (matroid_of_indep_of_bdd E Indep h_empty h_subset h_aug h_bdd h_support) := by
  obtain ⟨B, hB⟩ := 
    (matroid_of_indep_of_bdd E Indep h_empty h_subset h_aug h_bdd h_support).exists_base
  obtain ⟨n, h_bdd⟩ := h_bdd
  simp_rw [encard_le_coe_iff] at h_bdd
  refine' hB.finiteRk_of_finite (h_bdd B _).1
  rw [←matroid_of_indep_of_bdd_apply E Indep, indep_iff_subset_base]
  exact ⟨_, hB, rfl.subset⟩

def matroid_of_indep_of_bdd_augment (E : Set α) (Indep : Set α → Prop) (h_empty : Indep ∅) 
    (h_subset : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I) 
    (ind_aug : ∀ ⦃I J⦄, Indep I → Indep J → I.ncard < J.ncard →
      ∃ e ∈ J, e ∉ I ∧ Indep (insert e I)) 
    (h_bdd : ∃ (n : ℕ), ∀ I, Indep I → I.encard ≤ n ) (h_support : ∀ I, Indep I → I ⊆ E) : 
    Matroid α := 
  matroid_of_indep_of_bdd E Indep h_empty h_subset 
    (by {
      simp_rw [mem_maximals_setOf_iff, not_and, not_forall, exists_prop, exists_and_left, mem_diff,
        and_imp, and_assoc]
      simp_rw [encard_le_coe_iff] at h_bdd; obtain ⟨n, h_bdd⟩ := h_bdd
      rintro I B hI hImax hB hBmax
      obtain ⟨J, hJ, hIJ, hne⟩ := hImax hI
      have hlt : I.ncard < J.ncard := ncard_lt_ncard (hIJ.ssubset_of_ne hne) (h_bdd J hJ).1
      have hle : J.ncard ≤ B.ncard := by
      { refine' le_of_not_lt (fun hlt' ↦ _)
        obtain ⟨e, he⟩ := ind_aug hB hJ hlt' 
        rw [hBmax he.2.2 (subset_insert _ _)] at he
        exact he.2.1 (mem_insert _ _) }
      exact ind_aug hI hB (hlt.trans_le hle) })
    h_bdd h_support 

@[simp] theorem matroid_of_indep_of_bbd_augment_apply (E : Set α) (Indep : Set α → Prop) 
    (h_empty : Indep ∅) (h_subset : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I) 
    (ind_aug : ∀ ⦃I J⦄, Indep I → Indep J → I.ncard < J.ncard →
      ∃ e ∈ J, e ∉ I ∧ Indep (insert e I)) 
    (h_bdd : ∃ (n : ℕ), ∀ I, Indep I → I.encard ≤ n ) (h_support : ∀ I, Indep I → I ⊆ E) : 
    (matroid_of_indep_of_bdd_augment E Indep h_empty h_subset ind_aug h_bdd h_support).Indep 
      = Indep := by
  simp [matroid_of_indep_of_bdd_augment]

/-- A collection of Bases with the exchange property and at least one finite member is a matroid -/
def matroid_of_exists_finite_base {α : Type _} (E : Set α) (Base : Set α → Prop) 
    (exists_finite_base : ∃ B, Base B ∧ B.Finite) (base_exchange : exchange_property Base) 
    (support : ∀ B, Base B → B ⊆ E) : Matroid α := 
  matroid_of_base E Base 
    (by { obtain ⟨B,h⟩ := exists_finite_base; exact ⟨B,h.1⟩ }) base_exchange 
    (by {
      obtain ⟨B, hB, hfin⟩ := exists_finite_base
      refine' fun X _ ↦ Matroid.exists_maximal_subset_property_of_bdd 
        ⟨B.ncard, fun Y ⟨B', hB', hYB'⟩ ↦ _⟩ X
      rw [←hfin.encard_eq, encard_base_eq_of_exch base_exchange hB hB']
      exact encard_mono hYB' })
    support

@[simp] theorem matroid_of_exists_finite_base_apply {α : Type _} (E : Set α) (Base : Set α → Prop) 
    (exists_finite_base : ∃ B, Base B ∧ B.Finite) (base_exchange : exchange_property Base) 
    (support : ∀ B, Base B → B ⊆ E) : 
    (matroid_of_exists_finite_base E Base exists_finite_base base_exchange support).Base = Base := 
  rfl 

/-- A matroid constructed with a finite Base is `FiniteRk` -/
instance {E : Set α} {Base : Set α → Prop} {exists_finite_base : ∃ B, Base B ∧ B.Finite} 
    {base_exchange : exchange_property Base} {support : ∀ B, Base B → B ⊆ E} : 
    Matroid.FiniteRk 
      (matroid_of_exists_finite_base E Base exists_finite_base base_exchange support) := 
  ⟨exists_finite_base⟩  

def matroid_of_base_of_finite {E : Set α} (hE : E.Finite) (Base : Set α → Prop)
    (exists_base : ∃ B, Base B) (base_exchange : exchange_property Base)
    (support : ∀ B, Base B → B ⊆ E) : Matroid α :=
  matroid_of_exists_finite_base E Base 
    (by { obtain ⟨B,hB⟩ := exists_base; exact ⟨B,hB, hE.subset (support _ hB)⟩ }) 
    base_exchange support

@[simp] theorem matroid_of_base_of_finite_apply {E : Set α} (hE : E.Finite) (Base : Set α → Prop)
    (exists_base : ∃ B, Base B) (base_exchange : exchange_property Base)
    (support : ∀ B, Base B → B ⊆ E) : 
    (matroid_of_base_of_finite hE Base exists_base base_exchange support).Base = Base := rfl 

/-- A collection of subsets of a finite ground set satisfying the usual independence axioms 
  determines a matroid -/
def matroid_of_indep_of_finite {E : Set α} (hE : E.Finite) (Indep : Set α → Prop)
    (h_empty : Indep ∅)
    (ind_mono : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I)
    (ind_aug : ∀ ⦃I J⦄, Indep I → Indep J → I.ncard < J.ncard → ∃ e ∈ J, e ∉ I ∧ Indep (insert e I)) 
    (h_support : ∀ ⦃I⦄, Indep I → I ⊆ E) : Matroid α := 
  matroid_of_indep_of_bdd_augment E Indep h_empty ind_mono ind_aug
  (⟨E.ncard, fun I hI ↦ by { rw [←hE.encard_eq]; exact encard_mono (h_support hI) }⟩ )
  h_support

instance matroid_of_indep_of_finite.Finite {E : Set α} (hE : E.Finite) (Indep : Set α → Prop)
    (h_empty : Indep ∅)
    (ind_mono : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I)
    (ind_aug : ∀ ⦃I J⦄, Indep I → Indep J → I.ncard < J.ncard → ∃ e ∈ J, e ∉ I ∧ Indep (insert e I)) 
    (h_support : ∀ ⦃I⦄, Indep I → I ⊆ E) : 
    ((matroid_of_indep_of_finite) hE Indep h_empty ind_mono ind_aug h_support).Finite := 
  ⟨hE⟩ 

instance matroid_of_indep_of_finite_apply {E : Set α} (hE : E.Finite) (Indep : Set α → Prop)
    (h_empty : Indep ∅)
    (ind_mono : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I)
    (ind_aug : ∀ ⦃I J⦄, Indep I → Indep J → I.ncard < J.ncard → ∃ e ∈ J, e ∉ I ∧ Indep (insert e I)) 
    (h_support : ∀ ⦃I⦄, Indep I → I ⊆ E) : 
    ((matroid_of_indep_of_finite) hE Indep h_empty ind_mono ind_aug h_support).Indep = Indep := by
  simp [matroid_of_indep_of_finite]

end from_axioms

end Matroid 


/- Restrict a matroid to a set containing a known basis. This is a special case of restriction
  and only has auxiliary use -/
-- def bRestr (M : Matroid α) {B₀ R : Set α} (hB₀ : M.Base B₀) (hB₀R : B₀ ⊆ R) (hR : R ⊆ M.E) : 
--     Matroid α where
--   ground := R
--   Base B := M.Base B ∧ B ⊆ R
--   exists_base' := ⟨B₀, ⟨hB₀, hB₀R⟩⟩ 
--   base_exchange' := by
--     rintro B B' ⟨hB, hBR⟩ ⟨hB', hB'R⟩ e he
--     obtain ⟨f, hf⟩ := hB.exchange hB' he
--     refine' ⟨f, hf.1, hf.2, insert_subset (hB'R hf.1.1) ((diff_subset _ _).trans hBR)⟩    
--   maximality' := by
--     rintro X hXR Y ⟨B, ⟨hB, -⟩, hYB⟩ hYX
--     obtain ⟨J, ⟨⟨BJ, hBJ, hJBJ⟩, hJ⟩, hJmax⟩ := M.maximality' X (hXR.trans hR) Y ⟨B, hB, hYB⟩ hYX 
--     simp only [mem_setOf_eq, and_imp, forall_exists_index] at hJmax 
--     obtain ⟨BJ', hBJ', hJBJ'⟩ :=
--       (hBJ.indep.subset hJBJ).subset_basis_of_subset (subset_union_left _ B₀) 
--         (union_subset (hJ.2.trans (hXR.trans hR)) (hB₀R.trans hR))
--     have' hBJ'b := hB₀.base_of_basis_supset (subset_union_right _ _) hBJ'
--     refine' ⟨J, ⟨⟨BJ', ⟨hBJ'b, hBJ'.subset.trans (union_subset (hJ.2.trans hXR) hB₀R)⟩, hJBJ'⟩,hJ⟩, 
--       fun K ⟨⟨BK, ⟨hBK, _⟩, hKBK⟩, hYK, hKX⟩ hKJ ↦ hJmax BK hBK hKBK hYK hKX hKJ⟩
--   subset_ground' := by tauto
