import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.Order.Closure
import Mathlib.Data.List.Chain

open Set Function

variable {α β γ ι : Type*} {a b c : α} {x y z : β} {u v w : γ} {f : β → α}
  {r r' : α → β → Prop} {s s' : β → γ → Prop} {t t' : α → γ → Prop}

lemma not_symm_not {r : α → α → Prop} [Std.Symm r] : ¬ r a b → ¬ r b a := fun h ↦ h ∘ symm

lemma not_comm_not {r : α → α → Prop} [Std.Symm r] : ¬ r a b ↔ ¬ r b a :=
  ⟨not_symm_not, not_symm_not⟩

lemma trans' [Trans r s t] (hr : r a x) (hs : s x u) : t a u :=
  Trans.trans hr hs

namespace Relation

/--
# Relation

## Heterogeneous relations

converse is `flip`
-/

scoped macro:1050 r:term "ᵀ" : term => `(flip $r)

@[simp] lemma compl_apply : (r a x)ᶜ ↔ ¬r a x := Iff.rfl

@[simp] lemma flip_apply (r : α → α → Prop) : rᵀ a b ↔ r b a := Iff.rfl

def domain (r : α → β → Prop) : Set α := {x | ∃ y, r x y}

def codomain (r : α → β → Prop) : Set β := {y | ∃ x, r x y}

@[simp]
lemma mem_domain_iff (r : α → β → Prop) : a ∈ domain r ↔ ∃ x, r a x := Iff.rfl

@[simp]
lemma mem_codomain_iff (r : α → β → Prop) : x ∈ codomain r ↔ ∃ a, r a x := Iff.rfl

lemma left_mem_domain (hr : r a x) : a ∈ domain r := ⟨x, hr⟩

lemma right_mem_codomain (hr : r a x) : x ∈ codomain r := ⟨a, hr⟩

@[simp]
lemma domain_flip (r : α → β → Prop) : domain rᵀ = codomain r := rfl

@[simp]
lemma codomain_flip (r : α → β → Prop) : codomain rᵀ = domain r := rfl

lemma domain_comp (r : α → β → Prop) (s : β → γ → Prop) : domain (Comp r s) ⊆ domain r := by
  rintro x ⟨c, b, hrxb, hsbc⟩
  use b

lemma codomain_comp (r : α → β → Prop) (s : β → γ → Prop) : codomain (Comp r s) ⊆ codomain s := by
  rintro y ⟨c, b, hrxb, hsbc⟩
  use b

lemma domain_mono (h : r ≤ r') : domain r ⊆ domain r' := by
  rintro x ⟨y, hry⟩
  exact ⟨y, h _ _ hry⟩

lemma codomain_mono (h : r ≤ r') : codomain r ⊆ codomain r' := by
  rintro y ⟨x, hry⟩
  exact ⟨x, h _ _ hry⟩

/-- Double composition of `r` of the converse of `s`-/
def Domp (r s : α → β → Prop) : α → β → Prop := Comp r (Comp sᵀ r)

lemma domp_def (r s : α → β → Prop) : Domp r s = Comp (Comp r sᵀ) r := by
  rw [comp_assoc]
  rfl

lemma domp_def' (r s : α → β → Prop) : Domp r s = Comp r (Comp sᵀ r) := rfl

lemma domain_domp (r s : α → β → Prop) : domain (Domp r s) ⊆ domain r := by
  rw [domp_def']
  exact domain_comp r (Comp (flip s) r)

lemma codomain_domp (r s : α → β → Prop) : codomain (Domp r s) ⊆ codomain r := by
  rw [domp_def]
  exact codomain_comp (Comp r sᵀ) r

lemma le_domp_self (r : α → β → Prop) : r ≤ Domp r r :=
  fun a b hrab => ⟨b, hrab, a, hrab, hrab⟩

lemma domp_mono {r₁ r₂ s₁ s₂ : α → β → Prop} (hr : r₁ ≤ r₂) (hs : s₁ ≤ s₂) :
    Domp r₁ s₁ ≤ Domp r₂ s₂ := by
  rintro a b ⟨d, had, c, hcd, hcb⟩
  exact ⟨d, hr a d had, c, hs c d hcd, hr c b hcb⟩

@[simp] lemma domp_bot_right (r : α → β → Prop) : Domp r ⊥ = ⊥ := by
  ext a b
  simp [Domp, Comp, flip]

@[simp] lemma domp_bot_left (s : α → β → Prop) : Domp ⊥ s = ⊥ := by
  ext a b
  simp [Domp, Comp, flip]

lemma domp_sup_right (r : α → β → Prop) (s₁ s₂ : α → β → Prop) :
    Domp r (s₁ ⊔ s₂) = Domp r s₁ ⊔ Domp r s₂ := by
  ext a b
  simp [Domp, Comp, flip, and_or_left, exists_or, or_and_right]

lemma domp_or (r s t : α → β → Prop) :
    Domp r (fun x y ↦ s x y ∨ t x y) = fun x y ↦ Domp r s x y ∨ Domp r t x y := by
  ext a b
  simp [Domp, Comp, flip, and_or_left, exists_or, or_and_right]


class Dompeq (r s : α → β → Prop) : Prop where
  dompeq : Domp r s = s

lemma domp_eq (r s : α → β → Prop) [Dompeq r s] : Domp r s = s := Dompeq.dompeq

instance [Dompeq r r'] : Trans r (Comp r'ᵀ r) r' where
  trans := by
    rintro a x y hrax ⟨b, hr'bx, hrby⟩
    exact domp_eq r r' |>.le a y ⟨x, hrax, b, hr'bx, hrby⟩

instance [Dompeq r r'] : Trans (Comp r r'ᵀ) r r' where
  trans := by
    rintro a b x ⟨y, hray, hr'by⟩ hrbx
    exact domp_eq r r' |>.le a x ⟨y, hray, b, hr'by, hrbx⟩

lemma dompeq_apply [Dompeq r r'] (hr'ax : r' a x) (hrbx : r b x) (hray : r a y) : r' b y :=
  domp_eq r r' |>.le b y ⟨x, hrbx, a, hr'ax, hray⟩

lemma dompeq_left_iff [Dompeq r r] (hrax : r a x) (hrbx : r b x) : r a y ↔ r b y :=
  ⟨dompeq_apply hrax hrbx, dompeq_apply hrbx hrax⟩

lemma dompeq_right_iff [Dompeq r r] (hrax : r a x) (hray : r a y) : r b x ↔ r b y :=
  ⟨(dompeq_apply hrax · hray), (dompeq_apply hray · hrax)⟩


def fiber (r : α → β → Prop) (x : β) : Set α := {a | r a x}

@[simp]
lemma mem_fiber_iff (r : α → β → Prop) : a ∈ fiber r x ↔ r a x := Iff.rfl

@[simp]
lemma fiber_empty : fiber r x = ∅ ↔ x ∉ codomain r := by
  simp [fiber, eq_empty_iff_forall_notMem]

lemma fiber_eq_or_disjoint [Dompeq r r] :
    fiber r x = fiber r y ∨ Disjoint (fiber r x) (fiber r y) := by
  rw [or_iff_not_imp_right, not_disjoint_iff_nonempty_inter]
  rintro ⟨a, hax, hay⟩
  ext b
  simp only [mem_fiber_iff] at hax hay ⊢
  exact dompeq_right_iff hax hay

lemma fiber_eq_of_mem [Dompeq r r] (hrax : r a x) (hray : r a y) : fiber r x = fiber r y := by
  apply fiber_eq_or_disjoint.resolve_right
  rw [not_disjoint_iff_nonempty_inter]
  use a
  exact ⟨hrax, hray⟩


def image (r : α → β → Prop) (S : Set α) : Set β := {x | ∃ a ∈ S, r a x}

def preimage (r : α → β → Prop) (S : Set β) : Set α := {a | ∃ x ∈ S, r a x}

@[simp]
lemma image_flip (r : α → β → Prop) (S : Set β) : image rᵀ S = preimage r S := rfl

@[simp]
lemma preimage_flip (r : α → β → Prop) (S : Set α) : preimage rᵀ S = image r S := rfl

@[simp]
lemma mem_image_iff (r : α → β → Prop) (S : Set α) :
    x ∈ image r S ↔ ∃ a ∈ S, r a x := Iff.rfl

@[simp]
lemma mem_preimage_iff (r : α → β → Prop) (S : Set β) :
    a ∈ preimage r S ↔ ∃ x ∈ S, r a x := Iff.rfl

@[simp]
lemma sUnion_fiber (r : α → β → Prop) (S : Set β) : ⋃₀ (fiber r '' S) = preimage r S := by
  ext a
  simp

@[simp]
lemma image_domain (r : α → β → Prop) : image r (domain r) = codomain r := by
  ext x
  simp only [mem_image_iff, mem_domain_iff, mem_codomain_iff]
  exact ⟨fun ⟨a, _, hrax⟩ => ⟨a, hrax⟩, fun ⟨a, hrax⟩ => ⟨a, ⟨x, hrax⟩, hrax⟩⟩

@[simp]
lemma preimage_codomain (r : α → β → Prop) : preimage r (codomain r) = domain r := by
  ext a
  simp only [mem_preimage_iff, mem_codomain_iff, mem_domain_iff]
  exact ⟨fun ⟨x, _, hrax⟩ => ⟨x, hrax⟩, fun ⟨x, hrax⟩ => ⟨x, ⟨a, hrax⟩, hrax⟩⟩

@[simp]
lemma image_mono {r r' : α → β → Prop} (h : r ≤ r') (S : Set α) :
    image r S ⊆ image r' S := by
  rintro x ⟨a, haS, hrax⟩
  exact ⟨a, haS, h _ _ hrax⟩

@[simp]
lemma preimage_mono {r r' : α → β → Prop} (h : r ≤ r') (S : Set β) :
    preimage r S ⊆ preimage r' S := by
  rintro a ⟨x, hxS, hrax⟩
  exact ⟨x, hxS, h _ _ hrax⟩


class IsLeftTotal (r : α → β → Prop) : Prop where
  is_left_total : ∀ a, ∃ x, r a x

lemma left_total (r : α → β → Prop) [IsLeftTotal r] : ∀ a, ∃ x, r a x :=
  IsLeftTotal.is_left_total

@[simp]
lemma domain_univ (r : α → β → Prop) [IsLeftTotal r] : domain r = univ := by
  ext x
  simp only [mem_domain_iff, mem_univ, iff_true]
  exact left_total r x

class IsRightTotal (r : α → β → Prop) : Prop where
  is_right_total : ∀ x, ∃ a, r a x

lemma right_total (r : α → β → Prop) [IsRightTotal r] : ∀ x, ∃ a, r a x :=
  IsRightTotal.is_right_total

@[simp]
lemma codomain_univ (r : α → β → Prop) [IsRightTotal r] : codomain r = univ := by
  ext y
  simp only [mem_codomain_iff, mem_univ, iff_true]
  exact right_total r y

class IsTotal (r : α → β → Prop) : Prop extends IsLeftTotal r, IsRightTotal r

class IsLeftUnique (r : α → β → Prop) : Prop where
  is_left_unique : ∀ a x y, r a x → r a y → x = y

lemma left_unique (r : α → β → Prop) [IsLeftUnique r] : ∀ a x y, r a x → r a y → x = y :=
  IsLeftUnique.is_left_unique

class IsRightUnique (r : α → β → Prop) : Prop where
  is_right_unique : ∀ a b x, r a x → r b x → a = b

lemma right_unique (r : α → β → Prop) [IsRightUnique r] : ∀ a b x, r a x → r b x → a = b :=
  IsRightUnique.is_right_unique

class IsUnique (r : α → β → Prop) : Prop extends IsLeftUnique r, IsRightUnique r


def fibers (r : α → β → Prop) : Set (Set α) := fiber r '' codomain r

lemma fiber_mem_fibers_of_mem_codomain (hx : x ∈ codomain r) : fiber r x ∈ fibers r := by
  use x

lemma fiber_mem_fibers (hx : r a x) : fiber r x ∈ fibers r :=
  fiber_mem_fibers_of_mem_codomain (right_mem_codomain hx)

@[simp]
lemma mem_fibers_iff (r : α → β → Prop) (S : Set α) :
    S ∈ fibers r ↔ ∃ x ∈ codomain r, fiber r x = S := by
  simp [fibers]

lemma emptySet_notMem_fibers (r : α → β → Prop) : ∅ ∉ fibers r := by
  rintro ⟨x, ⟨a, hrax⟩, heq⟩
  have : a ∈ fiber r x := hrax
  simp only [mem_empty_iff_false, heq] at this

lemma nonempty_of_mem_fibers {S : Set α} (hS : S ∈ fibers r) : S.Nonempty := by
  obtain ⟨x, ⟨a, hax⟩, rfl⟩ := hS
  exact ⟨a, hax⟩

@[simp]
lemma sUnion_fibers (r : α → β → Prop) : ⋃₀ fibers r = domain r := by
  simp [fibers]

lemma fibers_pairwiseDisjoint' [IsLeftUnique r] : (fibers r).PairwiseDisjoint id := by
  rintro S ⟨b, -, rfl⟩ T ⟨b', -, rfl⟩ hST
  change Disjoint (fiber r b) (fiber r b')
  rw [disjoint_iff_inter_eq_empty]
  ext a
  simp only [mem_inter_iff, mem_fiber_iff, mem_empty_iff_false, iff_false, not_and]
  rintro hrxb hrxb'
  obtain rfl := left_unique r a b b' hrxb hrxb'
  exact hST rfl

lemma fibers_pairwiseDisjoint [Dompeq r r] :
    (fibers r).PairwiseDisjoint id := by
  rintro S ⟨x, ⟨a, hrax⟩, rfl⟩ T ⟨y, ⟨b, hrby⟩, rfl⟩ hST
  change Disjoint (fiber r x) (fiber r y)
  rw [disjoint_iff_inter_eq_empty]
  ext b
  simp only [mem_inter_iff, mem_fiber_iff, mem_empty_iff_false, iff_false, not_and]
  rintro hrbx hrby
  refine hST ?_
  ext c
  simp only [mem_fiber_iff]
  exact dompeq_right_iff hrbx hrby


instance : HasSubset (α → β → Prop) where
  Subset r s := fibers r ⊆ fibers s

instance : IsPreorder (α → β → Prop) (· ⊆ ·) where
  refl _ _ := id
  trans _ _ _ h₁ h₂ _ h := h₂ (h₁ h)


def leftRestrict (r : α → β → Prop) (S : Set α) : α → β → Prop :=
  fun x y ↦ r x y ∧ x ∈ S

-- notation r " |ₗ " S => leftRestrict r S

def rightRestrict (r : α → β → Prop) (S : Set β) : α → β → Prop :=
  fun x y ↦ r x y ∧ y ∈ S

-- notation r " |ᵣ " S => rightRestrict r S

def leftResidual (r : α → β → Prop) (s : α → γ → Prop) : β → γ → Prop :=
  (Comp rᵀ sᶜ)ᶜ
-- notation r " \\ " s => leftResidual r s

def rightResidual (r : α → β → Prop) (s : γ → β → Prop) : α → γ → Prop :=
  (Comp rᶜ sᵀ)ᶜ
-- notation r " / " s => rightResidual r s

@[simp]
lemma leftResidual_apply {r : α → β → Prop} {t : α → γ → Prop} :
    leftResidual r t x u ↔ ∀ a, r a x → t a u := by
  simp [leftResidual, Comp, flip]

@[simp]
lemma rightResidual_apply {r : α → β → Prop} {s : γ → β → Prop} :
    rightResidual r s a u ↔ ∀ x, s u x → r a x := by
  simp [rightResidual, Comp, flip, not_imp_not]

-- This is iff
lemma comp_le (r : α → β → Prop) (s : β → γ → Prop) (t : α → γ → Prop) [Trans r s t] :
    Comp r s ≤ t := by
  rintro a c ⟨b, hrab, hsbc⟩
  exact trans hrab hsbc

lemma Schroder_leftResidual {r : α → β → Prop} {s : β → γ → Prop} {t : α → γ → Prop} :
    Comp r s ≤ t ↔ s ≤ leftResidual r t := by
  refine ⟨fun hrs b c hsbc ⟨a, hrab, hntac⟩ => hntac <| hrs a c ⟨b, hrab, hsbc⟩,
    fun hsle a c ⟨b, hrab, hsbc⟩ => ?_⟩
  have := hsle b c hsbc
  contrapose! this
  simp only [leftResidual, Pi.compl_apply, compl_iff_not, not_not]
  use a, hrab, this

lemma le_leftResidual (r : α → β → Prop) (s : β → γ → Prop) (t : α → γ → Prop) [Trans r s t] :
    s ≤ leftResidual r t := by
  rw [← Schroder_leftResidual]
  exact comp_le r s t

lemma Schroder_rightResidual {r : α → β → Prop} {s : β → γ → Prop} {t : α → γ → Prop} :
    Comp r s ≤ t ↔ r ≤ rightResidual t s := by
  refine ⟨fun hrs a b hrac ⟨c, hntac, hsbc⟩ => hntac <| hrs a c ⟨b, hrac, hsbc⟩,
    fun hrle a c ⟨b, hrab, hsbc⟩ => ?_⟩
  have := hrle a b hrab
  contrapose! this
  simp only [rightResidual, Pi.compl_apply, compl_iff_not, not_not]
  use c, this, hsbc

lemma le_rightResidual {r : α → β → Prop} {s : β → γ → Prop} {t : α → γ → Prop} [Trans r s t]:
    r ≤ rightResidual t s := by
  rw [← Schroder_rightResidual]
  exact comp_le r s t


/-
## Interaction between heterogeneous and homogeneous relations
-/

variable {r : α → α → Prop} {s s' : α → β → Prop} {t : β → α → Prop}

lemma left_rw {a b : α} {c : β} {r : α → α → Prop} [Std.Symm r] (s : α → β → Prop) [Trans r s s]
    (hr : r a b) : s a c ↔ s b c := ⟨trans' (symm hr), trans' hr⟩

lemma right_rw {a : α} {b c : β} {r : β → β → Prop} [Std.Symm r] (s : α → β → Prop) [Trans s r s]
    (hs : r b c) : s a b ↔ s a c := ⟨(trans' · hs), (trans' · (symm hs))⟩

instance : Trans r (⊥ : α → β → Prop) (⊥ : α → β → Prop) where
  trans hr hb := by simp_all

instance {r : α → β → Prop} : Trans (⊥ : α → α → Prop) r r where
  trans := by simp_all

instance [Trans r s s'] : Trans r (Comp r s) (Comp r s') where
  trans := by
    rintro a b x hrab ⟨c, hrbc, hscx⟩
    exact ⟨b, hrab, trans hrbc hscx⟩

instance [IsTrans α r] : Trans r (Comp r s) (Comp r s) where
  trans := by
    rintro a b x hrab ⟨c, hrbc, hscx⟩
    exact ⟨c, trans' hrab hrbc, hscx⟩

instance {r : β → β → Prop} [IsTrans β r] : Trans (Comp s r) r (Comp s r) where
  trans := by
    rintro a x y ⟨z, hsaz, hrzx⟩ hrxy
    exact ⟨z, hsaz, trans' hrzx hrxy⟩

@[simp]
lemma comp_bot {γ : Type*} (r : α → β → Prop) : Comp r (⊥ : β → γ → Prop) = ⊥ := by
  ext x y
  simp [Comp]

@[simp]
lemma bot_comp {γ : Type*} (r : β → γ → Prop) : Comp (⊥ : α → β → Prop) r = ⊥ := by
  ext x y
  simp [Comp]

/-
## Homogeneous relations
-/

variable {r s t : α → α → Prop}

instance : Std.Refl (⊤ : α → α → Prop) where
  refl := by simp

instance : Std.Symm (⊤ : α → α → Prop) where
  symm := by simp

instance : IsTrans α ⊤ where
  trans := by simp

instance : Std.Symm (⊥ : α → α → Prop) where
  symm := by simp

instance : IsTrans α ⊥ where
  trans := by simp

instance [Std.Refl r] : Std.Refl (r on f) where
  refl a := refl (f a)

instance [Std.Symm r] : Std.Symm (r on f) where
  symm a _ := symm (a := f a)

instance [IsTrans α r] : IsTrans β (r on f) where
  trans a _ _ := trans' (a := f a)

instance [IsTrans α r] [Dompeq r s] : Trans r s s where
  trans := by
    rintro a b c hr hs
    rw [← domp_eq r s] at hs ⊢
    obtain ⟨e, hrbe, d, hsde, hrdc⟩ := hs
    exact ⟨e, trans' hr hrbe, d, hsde, hrdc⟩

instance [IsTrans α r] [Dompeq r s] : Trans s r s where
  trans := by
    rintro a b c hs hrbc
    rw [← domp_eq r s] at hs ⊢
    obtain ⟨d, hrae, e, hsde, hrdb⟩ := hs
    exact ⟨d, hrae, e, hsde, trans' hrdb hrbc⟩

instance [Std.Symm r] [Std.Symm s] [Trans r s s]: Trans s r s where
  trans hs hr := symm <| trans' (symm hr) (symm hs)

instance [Std.Symm r] [Std.Symm s] [Trans s r s]: Trans r s s where
  trans hs hr := symm <| trans' (symm hr) (symm hs)

instance [Std.Symm r] [Std.Symm s] : Std.Symm (r ⊔ s) := by
  refine ⟨fun a b h ↦ ?_⟩
  obtain (h | h) := h <;> simp [symm h]

instance [Std.Symm r] [Std.Symm s] : Std.Symm (r ⊓ s) :=
  ⟨fun a b ⟨hr, hs⟩ ↦ by simp [symm hr, symm hs]⟩

instance [Std.Refl r] : Std.Refl rᵀ where
  refl := refl_of r

instance [Std.Symm r] : Std.Symm rᵀ where
  symm _ _ := symm_of r

instance [IsTrans α r] : IsTrans α rᵀ where
  trans _ _ _ := flip (trans_of r)

instance [Std.Antisymm r] : Std.Antisymm rᵀ where
  antisymm _ _ := flip (antisymm_of r)

instance [IsPreorder α r] : IsPreorder α rᵀ where
  refl := refl_of r
  trans _ _ _ := flip (trans_of r)

-- instance [IsPartialOrder α r] : IsPartialOrder α rᵀ where
--   antisymm _ _ := flip (antisymm_of r)

instance [IsLinearOrder α r] : IsLinearOrder α rᵀ where
  total a b := (total_of r b a)

lemma sSup_symmtric {s : Set (α → α → Prop)} (hs : ∀ r ∈ s, Std.Symm r) : Symmetric (sSup s) := by
  rintro a b h
  induction h with
  | intro w h =>
    simp only [mem_range, eq_iff_iff, Subtype.exists, exists_prop, exists_exists_and_eq_and,
      binary_relation_sSup_iff s] at h ⊢
    obtain ⟨⟨r, hrs, hrw⟩, hw⟩ := h
    have := hs r hrs
    exact ⟨r, hrs, symm <| hrw.mpr hw⟩

lemma sInf_symmtric {s : Set (α → α → Prop)} (hs : ∀ r ∈ s, Std.Symm r) : Symmetric (sInf s) := by
  rintro a b
  simp_rw [binary_relation_sInf_iff s]
  exact fun h r hrs => let := hs r hrs; symm (h r hrs)

instance {s : ι → α → α → Prop} [∀ i, Std.Symm (s i)] : Std.Symm (⨆ i, s i) where
  symm a b h := by
    simp only [iSup_apply, iSup_Prop_eq] at h ⊢
    obtain ⟨i, h⟩ := h
    exact ⟨i, symm h⟩

instance {s : ι → α → α → Prop} [∀ i, Std.Symm (s i)] : Std.Symm (⨅ i, s i) where
  symm a b h := by
    simp only [iInf_apply, iInf_Prop_eq] at h ⊢
    exact fun i => symm (h i)

lemma sInf_transitive {s : Set (α → α → Prop)} (hs : ∀ r ∈ s, IsTrans α r) :
    Transitive (sInf s) := by
  rintro a b c
  simp_rw [binary_relation_sInf_iff s]
  exact fun hab hbc r hrs => let := hs r hrs; trans' (hab r hrs) (hbc r hrs)

instance {s : ι → α → α → Prop} [∀ i, IsTrans α (s i)] : IsTrans α (⨅ i, s i) where
  trans a b c hab hbc := by
    simp only [iInf_apply, iInf_Prop_eq] at hab hbc ⊢
    exact fun i => trans' (hab i) (hbc i)

lemma domain_eq_codomain (r : α → α → Prop) [Std.Symm r] : domain r = codomain r := by
  ext a
  simp only [mem_domain_iff, mem_codomain_iff]
  exact ⟨fun ⟨b, hab⟩ => ⟨b, symm hab⟩, fun ⟨b, hba⟩ => ⟨b, symm hba⟩⟩

instance [IsTrans α r] [IsTrans α s] : IsTrans α (r ⊓ s) :=
  ⟨fun _ _ _ ⟨hr, hs⟩ ⟨hr', hs'⟩ ↦ ⟨trans_of r hr hr', trans_of s hs hs'⟩⟩

instance [IsTrans α r] : IsTrans α rᵀ where
  trans _ _ _ h h' := trans_of r h' h

lemma transitive_of_le_eq (r : α → α → Prop) (hr : r ≤ (· = ·)) : Transitive r := by
  rintro a b c hab hbc
  obtain rfl := hr _ _ hab
  obtain rfl := hr _ _ hbc
  exact hab

def SymmClosure : ClosureOperator (α → α → Prop) where
  toFun r := r ⊔ flip r
  monotone' _ _ hle _ _ hab := hab.imp (hle _ _) (hle _ _)
  le_closure' r a b hab := Or.inl hab
  idempotent' r := by
    ext a b
    simp [or_comm]

@[simp]
lemma symmClosure_apply (r : α → α → Prop) (a b : α) :
    SymmClosure r a b ↔ r a b ∨ r b a := Iff.rfl

lemma symmClosure_symmetric (r : α → α → Prop) : Symmetric (SymmClosure r) :=
  fun _ _ ↦ Or.symm

instance : Std.Symm (SymmClosure r) where
  symm := symmClosure_symmetric r

lemma SymmClosure.symm (hr : SymmClosure r a b) : SymmClosure r b a :=
  symmClosure_symmetric r hr

@[simp]
lemma symmClosure_domain (r : α → α → Prop) : domain (SymmClosure r) = domain r ∪ codomain r := by
  ext x
  simp only [mem_domain_iff, mem_union, mem_codomain_iff]
  refine ⟨fun ⟨y, h⟩ => h.imp (⟨y, ·⟩) (⟨y, ·⟩), ?_⟩
  rintro (⟨y, h⟩ | ⟨y, h⟩)
  · exact ⟨y, Or.inl h⟩
  · exact ⟨y, Or.inr h⟩

@[simp]
lemma symmClosure_codomain (r : α → α → Prop) :
    codomain (SymmClosure r) = domain r ∪ codomain r := by
  ext x
  simp only [mem_codomain_iff, mem_union, mem_domain_iff]
  refine ⟨fun ⟨y, h⟩ => h.symm.imp (⟨y, ·⟩) (⟨y, ·⟩), ?_⟩
  rintro (⟨y, h⟩ | ⟨y, h⟩)
  · exact ⟨y, Or.inr h⟩
  · exact ⟨y, Or.inl h⟩

@[simp↓]
lemma symmClosure_eq_self (r : α → α → Prop) [Std.Symm r] : SymmClosure r = r := by
  ext a b
  simp only [symmClosure_apply, or_iff_left_iff_imp]
  exact symm_of r

def TransClosure : ClosureOperator (α → α → Prop) where
  toFun := TransGen
  monotone' _ _ h _ _ h' := TransGen.mono h h'
  le_closure' _ _ _ := TransGen.single
  idempotent' _ := by
    ext a b
    constructor <;> intro h
    · induction h with
      | single h => exact h
      | tail _ h' ih => exact TransGen.trans ih h'
    · exact TransGen.single h
  IsClosed := Transitive
  isClosed_iff := ⟨transGen_eq_self, fun hr => hr ▸ transitive_transGen⟩

instance : IsTrans α (TransClosure r) := by
  change IsTrans α (TransGen r)
  infer_instance

instance [Std.Symm r] : Std.Symm (TransClosure r) := by
  refine ⟨fun a b h ↦ ?_⟩
  induction h with
  | single hr => exact TransGen.single (symm_of r hr)
  | tail _ hr ih => exact TransGen.head (symm_of r hr) ih

@[simp]
lemma transClosure_eq_self (r : α → α → Prop) [IsTrans α r] : TransClosure r = r :=
  transGen_eq_self <| transitive_of_trans r

lemma transClosure_eq_self_of_le_eq (hr : r ≤ (· = ·)) : TransClosure r = r :=
  transGen_eq_self <| transitive_of_le_eq r hr

@[simp]
lemma transClosure_eq : TransClosure (Eq : α → α → Prop) = Eq :=
  transClosure_eq_self_of_le_eq le_rfl

lemma transClosure_le_of_le_trans (hr : r ≤ s) [IsTrans α s] : TransClosure r ≤ s :=
  (ClosureOperator.IsClosed.closure_le_iff IsTrans.trans).mpr hr

lemma transClosure_le_domp_of_le_trans (hr : r ≤ s) [IsTrans α s] : TransClosure r ≤ Domp s r := by
  have hs : TransClosure.IsClosed s := IsTrans.trans
  rintro a b hab
  induction hab with
  | single hab' => exact ⟨_, hr _ _ hab', a, hab', hr _ _ hab'⟩
  | tail hab' hb'c' IH =>
    refine ⟨_, ?_, _, hb'c', hr _ _ hb'c'⟩
    rw [← ClosureOperator.IsClosed.closure_le_iff hs] at hr
    exact hr _ _ <| hab'.tail hb'c'

@[simp]
lemma transClosure_domain (r : α → α → Prop) : domain (TransClosure r) = domain r := by
  ext x
  simp_rw [mem_domain_iff]
  refine ⟨fun ⟨y, h⟩ => ?_, fun ⟨y, h⟩ => ⟨y, TransGen.single h⟩⟩
  induction h with
  | single h => exact ⟨_, h⟩
  | tail _ h' ih => exact ih

@[simp]
lemma transClosure_codomain (r : α → α → Prop) : codomain (TransClosure r) = codomain r := by
  ext x
  simp_rw [mem_codomain_iff]
  refine ⟨fun ⟨y, h⟩ => ?_, fun ⟨y, h⟩ => ⟨y, TransGen.single h⟩⟩
  induction h with
  | single h => exact ⟨_, h⟩
  | tail _ h ih => exact ⟨_, h⟩

lemma transClosure_exists_single_head (r : α → α → Prop) (h : TransClosure r a b) :
    ∃ c, r a c := by
  induction h using TransGen.head_induction_on with
  | single h => use b
  | head h' h IH =>
    rename_i c
    use c

lemma transClosure_exists_single_tail (r : α → α → Prop) (h : TransClosure r a b) :
    ∃ c, r c b := by
  induction h with
  | single _ => use a
  | tail _ _ _ =>
    rename_i c _ _ _ _
    use c

/-- Minimal assumption (that I can think of) for `transGen_self_iff`. -/
class foo (r : α → α → Prop) where
  isfoo : ∀ ⦃a b⦄, r a b → r b b

lemma refl_of_right [foo r] (h : r a b) : r b b := foo.isfoo h
lemma refl_of_left [foo <| flip r] (h : r a b) : r a a := by
  change rᵀ a a
  exact refl_of_right h

instance [Std.Symm r] [IsTrans α r] : foo r where
  isfoo _ _ hr := _root_.trans (symm_of r hr) hr

instance [Std.Symm r] [foo r] : foo rᵀ where
  isfoo _ _ h := by
    rw [Symmetric.flip_eq Std.Symm.symm] at h ⊢
    exact refl_of_right h

instance [foo r] [foo s] : foo (r ⊔ s) where
  isfoo _ _ hr := by obtain (hr | hr) := hr <;> simp [refl_of_right hr]

lemma foo_sSup {s : Set (α → α → Prop)} (hs : ∀ r ∈ s, foo r) : foo (sSup s) where
  isfoo x y hr := by
    simp only [sSup_apply, iSup_apply, iSup_Prop_eq, Subtype.exists, exists_prop] at hr ⊢
    obtain ⟨r, hrs, hrxy⟩ := hr
    let := hs r hrs
    exact ⟨r, hrs, refl_of_right hrxy⟩

instance {r : ι → α → α → Prop} [H : ∀ i, foo (r i)] : foo (⨆ i, r i) :=
  foo_sSup <| by
  rintro _ ⟨i, rfl⟩
  exact H i

instance [foo r] [foo s] : foo (r ⊓ s) where
  isfoo _ _ h := ⟨refl_of_right h.1, refl_of_right h.2⟩

lemma foo_sInf {s : Set (α → α → Prop)} (hs : ∀ r ∈ s, foo r) : foo (sInf s) where
  isfoo x y h := by
    simp only [sInf_apply, iInf_apply, iInf_Prop_eq, Subtype.forall] at h ⊢
    rintro r hrs
    let := hs r hrs
    exact refl_of_right <| h r hrs

instance {r : ι → α → α → Prop} [H : ∀ i, foo (r i)] : foo (⨅ i, r i) :=
  foo_sInf <| by
  rintro _ ⟨i, rfl⟩
  exact H i

@[simp]
lemma transClosure_self_iff [foo r] : TransClosure r a a ↔ r a a := by
  refine ⟨fun h => ?_, TransGen.single⟩
  obtain (h | ⟨_, _, h⟩) := (transGen_iff r _ _).mp h
  · exact h
  exact refl_of_right h

instance [Std.Symm r] [IsTrans α r] : Dompeq r r where
  dompeq := by
    ext a b
    exact ⟨fun ⟨d, had, c, hcd, hcb⟩ => trans' had (trans' (symm hcd) hcb),
      fun h => ⟨b, h, a, h, h⟩⟩

-- def reflSet (r : α → α → Prop) : Set α := {x | r x x}

-- @[simp]
-- lemma mem_reflSet_iff (r : α → α → Prop) : a ∈ reflSet r ↔ r a a := Iff.rfl

-- lemma reflSet_eq_refl (r : α → α → Prop) : reflSet r = {x | r x x} := rfl

-- lemma sup_reflSet (r s : α → α → Prop) : reflSet (r ⊔ s) = reflSet r ⊔ reflSet s := rfl

-- lemma inf_reflSet (r s : α → α → Prop) : reflSet (r ⊓ s) = reflSet r ⊓ reflSet s := rfl

-- lemma reflSet_eq_domain (r : α → α → Prop) [foo <| flip r] : reflSet r = domain r := by
--   ext a
--   rw [mem_reflSet_iff, mem_domain_iff]
--   exact ⟨fun h => ⟨a, h⟩, fun ⟨b, h⟩ => refl_of_left h⟩

-- lemma reflSet_eq_codomain (r : α → α → Prop) [foo r] : reflSet r = codomain r := by
--   ext a
--   rw [mem_reflSet_iff, mem_codomain_iff]
--   exact ⟨fun h => ⟨a, h⟩, fun ⟨b, h⟩ => refl_of_right h⟩



-- lemma sSup_reflSet (s : Set (α → α → Prop)) : reflSet (sSup s) = ⋃₀ (reflSet '' s) :=

-- lemma mem_reflSet_of_right [foo r] (h : r a b) : b ∈ reflSet r := refl_of_right h
-- lemma mem_reflSet_of_left [foo <| flip r] (h : r a b) : a ∈ reflSet r := refl_of_left h

lemma comp_idem_left (r : α → α → Prop) [IsTrans α r] [foo r] (s : α → β → Prop) :
  Comp r (Comp r s) = Comp r s := by
  ext x y
  exact ⟨fun ⟨a, hxa, b, hab, hsby⟩ => ⟨b, trans_of r hxa hab, hsby⟩,
    fun ⟨a, hxa, hsay⟩ => ⟨a, hxa, ⟨a, refl_of_right hxa, hsay⟩⟩⟩

lemma comp_idem_right (r : α → α → Prop) [IsTrans α r] [foo <| flip r] (s : β → α → Prop) :
  Comp (Comp s r) r = Comp s r := by
  ext x y
  refine ⟨fun ⟨a, ⟨b, hxb, hrba⟩, hray⟩ => ⟨b, hxb,  trans_of r hrba hray⟩,
    fun ⟨a, hxa, hray⟩ => ⟨a, ⟨a, hxa, ?_⟩, hray⟩⟩
  change rᵀ a a
  exact refl_of_right hray

lemma comp_self (r : α → α → Prop) [IsTrans α r] [foo r] : Comp r r = r := by
  ext x y
  exact ⟨fun ⟨u, hxu, huy⟩ => trans_of r hxu huy, fun h => ⟨y, h, refl_of_right h⟩⟩

lemma domp_symm (r s : α → α → Prop) [Std.Symm r] [Std.Symm s] : Symmetric (Domp r s) := by
  rintro a b ⟨d, had, c, hcd, hcb⟩
  exact ⟨c, symm hcb, d, symm hcd, symm had⟩

instance [Std.Symm r] [Std.Symm s] : Std.Symm (Domp r s) where
  symm := domp_symm r s

lemma domp_transitive (r s : α → α → Prop) [Std.Symm r] [IsTrans α s] [H : Trans s r s] :
    Transitive (Domp r s) := by
  rintro a b c ⟨e, hae, d, hde, hdb⟩ ⟨f, hbf, e', he'f, he'c⟩
  use e, hae, e', ?_, he'c
  have := trans' (H.trans (H.trans he'f (symm hbf)) (symm hdb)) hde
  exact this

instance [Std.Symm r] [IsTrans α s] [H : Trans s r s] : IsTrans α (Domp r s) where
  trans := domp_transitive r s

instance [IsTrans α r]: Trans r (Domp r s) (Domp r s) where
  trans := by
    rintro a b c hrab ⟨e, hrbe, d, hsde, hrdc⟩
    exact ⟨e, trans' hrab hrbe, d, hsde, hrdc⟩

instance [IsTrans α r] : Trans (Domp r s) r (Domp r s) where
  trans := by
    rintro a b c ⟨e, hrae, d, hsde, hrdb⟩ hrbc
    exact ⟨e, hrae, d, hsde, trans' hrdb hrbc⟩

instance [Dompeq r s] [IsTrans α r] : Trans r s s where
  trans := by
    rintro a b c hrab hsbc
    obtain ⟨d, hrbd, e, hsed, hrec⟩ := (domp_eq r s) ▸ hsbc
    exact (domp_eq r s) ▸ ⟨d, trans' hrab hrbd, e, hsed, hrec⟩

instance [Dompeq r s] [IsTrans α r] : Trans s r s where
  trans := by
    rintro a b c hsab hrbc
    obtain ⟨d, hrad, e, hsed, hrec⟩ := (domp_eq r s) ▸ hsab
    exact (domp_eq r s) ▸ ⟨d, hrad, e, hsed, trans' hrec hrbc⟩



def restrict (r : α → α → Prop) (S : Set α) : α → α → Prop :=
  fun x y ↦ r x y ∧ x ∈ S ∧ y ∈ S

lemma restrict.left_mem {r : α → α → Prop} {S : Set α} (h : restrict r S a b) : a ∈ S := h.2.1
lemma restrict.right_mem {r : α → α → Prop} {S : Set α} (h : restrict r S a b) : b ∈ S := h.2.2

lemma restrict_mono {r s : α → α → Prop} (h : r ≤ s) (S : Set α) :
    restrict r S ≤ restrict s S := by
  rintro x y ⟨hr, hx, hy⟩
  exact ⟨h _ _ hr, hx, hy⟩

-- lemma restrict_reflSet_subset (r : α → α → Prop) (S : Set α) : reflSet (restrict r S) ⊆ S :=
--   fun _ ⟨_, hx, _⟩ => hx

-- lemma restrict_reflSet_subset_reflSet (r : α → α → Prop) (S : Set α) :
--     reflSet (restrict r S) ⊆ reflSet r := fun _ ⟨hr, _, _⟩ => hr

lemma restrict_le (r : α → α → Prop) (S : Set α) : restrict r S ≤ r :=
  fun _ _ hrr => hrr.1

lemma restrict_subset (r : α → α → Prop) {S T : Set α} (h : S ⊆ T) :
    restrict r S ≤ restrict r T := fun _ _ ⟨hr, hx, hy⟩ => ⟨hr, h hx, h hy⟩

lemma restrict_symmetric (r : α → α → Prop) [Std.Symm r] (S : Set α) :
    Symmetric (restrict r S) := fun _ _ ⟨hr, ha, hb⟩ => ⟨symm hr, hb, ha⟩

instance [Std.Symm r] {S : Set α} : Std.Symm (restrict r S) where
  symm := restrict_symmetric r S

lemma restrict_eq_self (r : α → α → Prop) [Std.Symm r] {S : Set α} (hS : domain r ⊆ S) :
    restrict r S = r := by
  ext x y
  simp only [restrict, and_iff_left_iff_imp]
  intro h
  use hS (show x ∈ domain r by use y), hS (show y ∈ domain r by use x, symm h)

lemma restrict_eq_iff (r : α → α → Prop) [Std.Symm r] (S : Set α) :
    restrict r S = r ↔ domain r ⊆ S := by
  refine ⟨fun hr x hx => ?_, restrict_eq_self r⟩
  rw [← hr, mem_domain_iff] at hx
  obtain ⟨y, hxy⟩ := hx
  exact hxy.left_mem

@[simp]
lemma restrict_inter (r : α → α → Prop) (S T : Set α) :
    restrict r (S ∩ T) = restrict r S ⊓ restrict r T := by
  ext x y
  simp only [restrict, mem_inter_iff, Pi.inf_apply, inf_Prop_eq]
  tauto

@[simp]
lemma restrict_inf (r s : α → α → Prop) (S : Set α) :
    restrict (r ⊓ s) S = restrict r S ⊓ restrict s S := by
  ext x y
  simp only [restrict, Pi.inf_apply, inf_Prop_eq]
  tauto

@[simp]
lemma restrict_sup (r s : α → α → Prop) (S : Set α) :
    restrict (r ⊔ s) S = restrict r S ⊔ restrict s S := by
  ext x y
  simp only [restrict, Pi.sup_apply, sup_Prop_eq]
  tauto

@[simp]
lemma restrict_singleton_of_not (r : α → α → Prop) (a : α) (hra : ¬ r a a) :
    restrict r {a} = fun _ _ ↦ False := by
  ext x y
  simp only [restrict, mem_singleton_iff, iff_false, not_and]
  rintro hr rfl rfl
  exact hra hr

@[simp]
lemma restrict_singleton_of_refl (r : α → α → Prop) [Std.Refl r] (a : α) :
    restrict r {a} = fun x y ↦ x = a ∧ y = a := by
  ext x y
  simp only [restrict, mem_singleton_iff, and_iff_right_iff_imp, and_imp]
  rintro rfl rfl
  exact refl y

-- def comply (r : PER α) (s : α → α → Prop) : α → α → Prop :=
--   Comp (Comp r s) r

-- lemma comply_mono (r : PER α) {s t : α → α → Prop} (hst : s ≤ t) :
--     comply r s ≤ comply r t := by
--   rintro x y h'
--   let ⟨u, ⟨v, hxy, havu⟩, huy⟩ := h'
--   exact ⟨u, ⟨v, hxy, hst _ _ havu⟩, huy ⟩

-- @[simp]
-- lemma comply_idem (r : PER α) (s : α → α → Prop) :
--     comply r (comply r s) = comply r s := by
--   unfold comply
--   rw [comp_assoc, comp_idem_right, comp_assoc, comp_idem_left]

-- @[simp]
-- lemma comply_comp_left (r : PER α) (s : α → α → Prop) :
--     Comp r (comply r s) = comply r s := by
--   unfold comply
--   rw [comp_assoc, comp_idem_left]

-- @[simp]
-- lemma comply_comp_right (r : PER α) (s : α → α → Prop) : Comp (comply r s) r = comply r s := by
--   unfold comply
--   rw [comp_assoc, comp_self]

-- lemma comply_reflset_mono {r : PER α} {s₁ s₂ : α → α → Prop} (h₁ : s₁ ≤ s₂) :
--     reflSet (comply r s₁) ≤ reflSet (comply r s₂) :=
--   fun _ ⟨u, ⟨v, huv, hvx⟩, huy⟩ => ⟨u, ⟨v, huv, h₁ _ _ hvx⟩, huy⟩

-- lemma comply_reflset_subset (r : PER α) (s : α → α → Prop) : reflSet (comply r s) ⊆ reflSet r :=
--   fun _ ⟨_, ⟨_, huv, _⟩, _⟩ => refl_of_left huv

-- lemma comply_mono_left (hrs : r ≤ s) (s₁ : α → α → Prop) : comply r s₁ ≤ comply s s₁ :=
--   fun _ _ ⟨u, ⟨v, hxy, havu⟩, huy⟩ => ⟨u, ⟨v, hrs _ _ hxy, havu⟩, hrs _ _ huy⟩

-- lemma restrict_reflSet_le_comply (r : PER α) (s : α → α → Prop) :
--     restrict s (reflSet r) ≤ comply r s :=
--   fun x y ⟨hxy, hx, hy⟩ => ⟨y, ⟨x, hx, hxy⟩, hy⟩

-- @[simp]
-- lemma restrict_comply_eq_comply (r : PER α) (s : α → α → Prop) :
--     comply r (restrict s (reflSet r)) = comply r s := by
--   ext x y
--   exact ⟨fun ⟨u, ⟨v, hxv, hsvu, hv, hu⟩, huy⟩ => ⟨u, ⟨v, hxv, hsvu⟩, huy⟩,
--     fun ⟨u, ⟨v, hxv, hsvu⟩, huy⟩ => ⟨u, ⟨v, hxv, hsvu, refl_of_right hxv, refl_of_left huy⟩,
-- huy⟩⟩

-- lemma comply_le {s t : α → α → Prop} (h1 : restrict s (reflSet r) ≤ t)
--     (h2 : comply r t ≤ t) : comply r s ≤ t :=
--   (restrict_comply_eq_comply r _) ▸ comply_mono r h1 |>.trans h2

end Relation

namespace List.IsChain

lemma head_rel {α : Type*} {r : α → α → Prop} [IsPreorder α r] {l : List α}
    (h : l.IsChain r) (hne : l ≠ []) : ∀ x ∈ l, r (l.head hne) x := by
  rintro x hx
  match l with
  | [] => simp at hne
  | a :: [] =>
    simp_all only [singleton, mem_cons, not_mem_nil, or_false, head_cons]
    exact refl _
  | a :: b :: as =>
    simp only [isChain_cons_cons, head_cons] at h ⊢
    rw [mem_cons] at hx
    obtain rfl | hx := hx
    · exact refl _
    exact trans' h.1 <| by simpa using h.2.head_rel (by simp) x hx

lemma rel_last {α : Type*} {r : α → α → Prop} [IsPreorder α r] {l : List α}
    (h : l.IsChain r) (hne : l ≠ []) : ∀ x ∈ l, r x (l.getLast hne) := by
  rw [← l.reverse_reverse, isChain_reverse] at h
  have : IsPreorder α fun a b ↦ r b a := Relation.instIsPreorderFlip_matroid
  have := by simpa using h.head_rel (by simpa)
  rwa [List.head_reverse] at this

lemma eq_head_of_antisymm {α : Type*} {r : α → α → Prop} [IsPartialOrder α r]
    {l : List α} (h : l.IsChain r) (hne : l ≠ []) (hend : l.head hne = l.getLast hne) :
    ∀ x ∈ l, x = l.head hne :=
  fun x hx ↦ antisymm (hend ▸ h.rel_last hne x hx) <| h.head_rel hne x hx

lemma antisymm {α : Type*} {r : α → α → Prop} [IsPartialOrder α r]
    {l : List α} (h : l.IsChain r) (hend : l.head = l.getLast) : ∀ x ∈ l, ∀ y ∈ l, x = y := by
  by_cases hne : l = []
  · subst l
    simp
  rintro x hx y hy
  obtain rfl := h.eq_head_of_antisymm hne (congr_fun hend _) x hx
  exact h.eq_head_of_antisymm hne (congr_fun hend _) y hy |>.symm

end List.IsChain
