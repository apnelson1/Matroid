import Mathlib.Data.Setoid.Basic
import Mathlib.Order.Closure

open Set Function
namespace Relation

variable {α β γ ι : Type*} {a b c : α} {x y z : β} {u v w : γ} {f : ι → α}
  {r r' : α → β → Prop} {s s' : β → γ → Prop} {t t' : α → γ → Prop}

/--
# Relation

## Heterogeneous relations

converse is `flip`
-/

@[simp]
lemma compl_apply : (r a x)ᶜ ↔ ¬r a x := Iff.rfl

lemma trans' [Trans r s t] (hr : r a x) (hs : s x u) : t a u :=
  Trans.trans hr hs

def domain (r : α → β → Prop) : Set α := {x | ∃ y, r x y}

def codomain (r : α → β → Prop) : Set β := {y | ∃ x, r x y}

@[simp]
lemma mem_domain_iff (r : α → β → Prop) : a ∈ domain r ↔ ∃ x, r a x := Iff.rfl

@[simp]
lemma mem_codomain_iff (r : α → β → Prop) : x ∈ codomain r ↔ ∃ a, r a x := Iff.rfl

lemma left_mem_domain (hr : r a x) : a ∈ domain r := ⟨x, hr⟩

lemma right_mem_codomain (hr : r a x) : x ∈ codomain r := ⟨a, hr⟩

@[simp]
lemma domain_flip (r : α → β → Prop) : domain (flip r) = codomain r := rfl

@[simp]
lemma codomain_flip (r : α → β → Prop) : codomain (flip r) = domain r := rfl

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


def fiber (r : α → β → Prop) (x : β) : Set α := {a | r a x}

@[simp]
lemma mem_fiber_iff (r : α → β → Prop) : a ∈ fiber r x ↔ r a x := Iff.rfl

@[simp]
lemma fiber_empty : fiber r x = ∅ ↔ x ∉ codomain r := by
  simp [fiber, eq_empty_iff_forall_notMem]

def image (r : α → β → Prop) (S : Set α) : Set β := {x | ∃ a ∈ S, r a x}

def preimage (r : α → β → Prop) (S : Set β) : Set α := {a | ∃ x ∈ S, r a x}

@[simp]
lemma image_flip (r : α → β → Prop) (S : Set β) : image (flip r) S = preimage r S := rfl

@[simp]
lemma preimage_flip (r : α → β → Prop) (S : Set α) : preimage (flip r) S = image r S := rfl

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

lemma fibers_sSup_univ [IsLeftTotal r] : ⋃₀ fibers r = univ := by
  ext a
  simp only [fibers, fiber, mem_sUnion, mem_image, mem_codomain_iff, exists_exists_and_eq_and,
    mem_setOf_eq, mem_univ, iff_true]
  obtain ⟨x, hrax⟩ := left_total r a
  exact ⟨x, ⟨a, hrax⟩, hrax⟩

lemma fibers_pairwiseDisjoint [IsLeftUnique r] :
    ∀ S T, S ∈ fibers r → T ∈ fibers r → S ≠ T → Disjoint S T := by
  rintro S T ⟨b, -, rfl⟩ ⟨b', -, rfl⟩ hST
  rw [disjoint_iff_inter_eq_empty]
  ext a
  simp only [mem_inter_iff, mem_fiber_iff, mem_empty_iff_false, iff_false, not_and]
  rintro hrxb hrxb'
  obtain rfl := left_unique r a b b' hrxb hrxb'
  exact hST rfl


instance : HasSubset (α → β → Prop) where
  Subset r s := fibers r ⊆ fibers s

instance : IsPreorder (α → β → Prop) (· ⊆ ·) where
  refl _ _ := id
  trans _ _ _ h₁ h₂ _ h := h₂ (h₁ h)








def leftRestrict (r : α → β → Prop) (S : Set α) : α → β → Prop :=
  fun x y ↦ r x y ∧ x ∈ S

notation r " |ₗ " S => leftRestrict r S

def rightRestrict (r : α → β → Prop) (S : Set β) : α → β → Prop :=
  fun x y ↦ r x y ∧ y ∈ S

notation r " |ᵣ " S => rightRestrict r S

def leftResidual (r : α → β → Prop) (s : α → γ → Prop) : β → γ → Prop :=
  (Comp (flip r) sᶜ)ᶜ
notation r " \\ " s => leftResidual r s

def rightResidual (r : α → β → Prop) (s : γ → β → Prop) : α → γ → Prop :=
  (Comp rᶜ (flip s))ᶜ
notation r " / " s => rightResidual r s




lemma comp_le (r : α → β → Prop) (s : β → γ → Prop) (t : α → γ → Prop) [Trans r s t] :
    Comp r s ≤ t := by
  rintro a c ⟨b, hrab, hsbc⟩
  exact trans hrab hsbc

-- lemma Schroder_leftResidual {r : α → β → Prop} {s : β → γ → Prop} {t : α → γ → Prop} :
--     Comp r s ≤ t ↔ s ≤ r \ t := by
--   refine ⟨fun hrs b c hsbc ⟨a, hrab, hntac⟩ => hntac <| hrs a c ⟨b, hrab, hsbc⟩,
--     fun hsle a c ⟨b, hrab, hsbc⟩ => ?_⟩
--   have := hsle b c hsbc
--   contrapose! this
--   simp only [leftResidual, Pi.compl_apply, compl_iff_not, not_not]
--   use a, hrab, this

-- lemma le_leftResidual (r : α → β → Prop) (s : β → γ → Prop) (t : α → γ → Prop) [Schroder r s t] :
--     s ≤ r \ t := by
--   rw [← Schroder_leftResidual]
--   exact comp_le r s t

-- lemma Schroder_rightResidual {r : α → β → Prop} {s : β → γ → Prop} {t : α → γ → Prop} :
--     Comp r s ≤ t ↔ r ≤ t / s := by
--   refine ⟨fun hrs a b hrac ⟨c, hntac, hsbc⟩ => hntac <| hrs a c ⟨b, hrac, hsbc⟩,
--     fun hrle a c ⟨b, hrab, hsbc⟩ => ?_⟩
--   have := hrle a b hrab
--   contrapose! this
--   simp only [rightResidual, Pi.compl_apply, compl_iff_not, not_not]
--   use c, this, hsbc

-- lemma le_rightResidual {r : α → β → Prop} {s : β → γ → Prop} {t : α → γ → Prop} [Schroder r s t] :
--     r ≤ t / s := by
--   rw [← Schroder_rightResidual]
--   exact comp_le


/-
## Interaction between heterogeneous and homogeneous relations
-/

variable {r : α → α → Prop} {s s' : α → β → Prop} {t : β → α → Prop}

lemma left_rw {a b : α} {c : β} {r : α → α → Prop} [IsSymm α r] (s : α → β → Prop) [Trans r s s]
    (hr : r a b) : s a c ↔ s b c := ⟨trans' (symm hr), trans' hr⟩

lemma right_rw {a : α} {b c : β} {r : β → β → Prop} [IsSymm β r] (s : α → β → Prop) [Trans s r s]
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

instance : IsRefl α ⊤ where
  refl := by simp

instance : IsSymm α ⊤ where
  symm := by simp

instance : IsTrans α ⊤ where
  trans := by simp

instance : IsSymm α ⊥ where
  symm := by simp

instance : IsTrans α ⊥ where
  trans := by simp

instance [IsRefl α r] : IsRefl ι (r on f) where
  refl i := refl (f i)

instance [IsSymm α r] [IsSymm α s] : IsSymm α (r ⊔ s) := by
  refine ⟨fun a b h ↦ ?_⟩
  obtain (h | h) := h <;> simp [symm h]

instance [IsSymm α r] [IsSymm α s] : IsSymm α (r ⊓ s) :=
  ⟨fun a b ⟨hr, hs⟩ ↦ by simp [symm hr, symm hs]⟩

instance [IsSymm α r] : IsSymm α (flip r) where
  symm _ _ := symm_of r

lemma sSup_symm {s : Set (α → α → Prop)} (hs : ∀ r ∈ s, IsSymm α r) : IsSymm α (sSup s) where
  symm a b h := by
    induction h with
    | intro w h =>
      simp only [mem_range, eq_iff_iff, Subtype.exists, exists_prop, exists_exists_and_eq_and,
        binary_relation_sSup_iff s] at h ⊢
      obtain ⟨⟨r, hrs, hrw⟩, hw⟩ := h
      have := hs r hrs
      exact ⟨r, hrs, symm <| hrw.mpr hw⟩

lemma sInf_symm {s : Set (α → α → Prop)} (hs : ∀ r ∈ s, IsSymm α r) : IsSymm α (sInf s) where
  symm a b := by
    simp_rw [binary_relation_sInf_iff s]
    exact fun h r hrs => let := hs r hrs; symm (h r hrs)

lemma sInf_trans {s : Set (α → α → Prop)} (hs : ∀ r ∈ s, IsTrans α r) : IsTrans α (sInf s) where
  trans a b c := by
    simp_rw [binary_relation_sInf_iff s]
    exact fun hab hbc r hrs => let := hs r hrs; trans_of _ (hab r hrs) (hbc r hrs)

lemma domain_eq_codomain (r : α → α → Prop) [IsSymm α r] : domain r = codomain r := by
  ext a
  simp only [mem_domain_iff, mem_codomain_iff]
  exact ⟨fun ⟨b, hab⟩ => ⟨b, symm hab⟩, fun ⟨b, hba⟩ => ⟨b, symm hba⟩⟩

instance [IsTrans α r] [IsTrans α s] : IsTrans α (r ⊓ s) :=
  ⟨fun _ _ _ ⟨hr, hs⟩ ⟨hr', hs'⟩ ↦ ⟨trans_of r hr hr', trans_of s hs hs'⟩⟩

instance [IsTrans α r] : IsTrans α (flip r) where
  trans _ _ _ h h' := trans_of r h' h

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

instance [IsSymm α r] : IsSymm α (TransClosure r) := by
  refine ⟨fun a b h ↦ ?_⟩
  induction h with
  | single hr => exact TransGen.single (symm_of r hr)
  | tail _ hr ih => exact TransGen.head (symm_of r hr) ih

/-- Minimal assumption (that I can think of) for `transGen_self_iff`. -/
class foo (r : α → α → Prop) where
  isfoo : ∀ ⦃a b⦄, r a b → r b b

lemma refl_of_right [foo r] (h : r a b) : r b b := foo.isfoo h
lemma refl_of_left [foo <| flip r] (h : r a b) : r a a := by
  change (flip r) a a
  exact refl_of_right h

instance [IsSymm α r] [IsTrans α r] : foo r where
  isfoo _ _ hr := _root_.trans (symm_of r hr) hr

instance [IsSymm α r] [foo r] : foo (flip r) where
  isfoo _ _ h := by
    rw [Symmetric.flip_eq IsSymm.symm] at h ⊢
    exact refl_of_right h

instance [foo r] [foo s] : foo (r ⊔ s) where
  isfoo _ _ hr := by obtain (hr | hr) := hr <;> simp [refl_of_right hr]

lemma foo_sSup {s : Set (α → α → Prop)} (hs : ∀ r ∈ s, foo r) : foo (sSup s) where
  isfoo x y hr := by
    simp only [sSup_apply, iSup_apply, iSup_Prop_eq, Subtype.exists, exists_prop] at hr ⊢
    obtain ⟨r, hrs, hrxy⟩ := hr
    let := hs r hrs
    exact ⟨r, hrs, refl_of_right hrxy⟩

instance [foo r] [foo s] : foo (r ⊓ s) where
  isfoo _ _ h := ⟨refl_of_right h.1, refl_of_right h.2⟩

lemma foo_sInf {s : Set (α → α → Prop)} (hs : ∀ r ∈ s, foo r) : foo (sInf s) where
  isfoo x y h := by
    simp only [sInf_apply, iInf_apply, iInf_Prop_eq, Subtype.forall] at h ⊢
    rintro r hrs
    let := hs r hrs
    exact refl_of_right <| h r hrs

lemma transClosure_self_iff [foo r] : TransClosure r a a ↔ r a a := by
  refine ⟨fun h => ?_, TransGen.single⟩
  obtain (h | ⟨_, _, h⟩) := (transGen_iff r _ _).mp h
  · exact h
  exact refl_of_right h



def reflSet (r : α → α → Prop) : Set α := {x | r x x}

@[simp]
lemma mem_reflSet_iff (r : α → α → Prop) : a ∈ reflSet r ↔ r a a := Iff.rfl

lemma reflSet_eq_refl (r : α → α → Prop) : reflSet r = {x | r x x} := rfl

lemma sup_reflSet (r s : α → α → Prop) : reflSet (r ⊔ s) = reflSet r ⊔ reflSet s := rfl

lemma inf_reflSet (r s : α → α → Prop) : reflSet (r ⊓ s) = reflSet r ⊓ reflSet s := rfl

lemma reflSet_eq_domain (r : α → α → Prop) [foo <| flip r] : reflSet r = domain r := by
  ext a
  rw [mem_reflSet_iff, mem_domain_iff]
  exact ⟨fun h => ⟨a, h⟩, fun ⟨b, h⟩ => refl_of_left h⟩

lemma reflSet_eq_codomain (r : α → α → Prop) [foo r] : reflSet r = codomain r := by
  ext a
  rw [mem_reflSet_iff, mem_codomain_iff]
  exact ⟨fun h => ⟨a, h⟩, fun ⟨b, h⟩ => refl_of_right h⟩



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
  change (flip r) a a
  exact refl_of_right hray

lemma comp_self (r : α → α → Prop) [IsTrans α r] [foo r] : Comp r r = r := by
  ext x y
  exact ⟨fun ⟨u, hxu, huy⟩ => trans_of r hxu huy, fun h => ⟨y, h, refl_of_right h⟩⟩



def restrict (r : α → α → Prop) (S : Set α) : α → α → Prop :=
  fun x y ↦ r x y ∧ x ∈ S ∧ y ∈ S

lemma restrict.left_mem {r : α → α → Prop} {S : Set α} (h : restrict r S a b) : a ∈ S := h.2.1
lemma restrict.right_mem {r : α → α → Prop} {S : Set α} (h : restrict r S a b) : b ∈ S := h.2.2

lemma restrict_mono {r s : α → α → Prop} (h : r ≤ s) (S : Set α) :
    restrict r S ≤ restrict s S := by
  rintro x y ⟨hr, hx, hy⟩
  exact ⟨h _ _ hr, hx, hy⟩

lemma restrict_reflSet_subset (r : α → α → Prop) (S : Set α) : reflSet (restrict r S) ⊆ S :=
  fun _ ⟨_, hx, _⟩ => hx

lemma restrict_reflSet_subset_reflSet (r : α → α → Prop) (S : Set α) :
    reflSet (restrict r S) ⊆ reflSet r := fun _ ⟨hr, _, _⟩ => hr

lemma restrict_le (r : α → α → Prop) (S : Set α) : restrict r S ≤ r :=
  fun _ _ hrr => hrr.1

lemma restrict_subset (r : α → α → Prop) {S T : Set α} (h : S ⊆ T) :
    restrict r S ≤ restrict r T := fun _ _ ⟨hr, hx, hy⟩ => ⟨hr, h hx, h hy⟩

lemma restrict_eq_iff (r : α → α → Prop) [foo r] [foo <| flip r] (S : Set α) :
    restrict r S = r ↔ reflSet r ⊆ S := by
  refine ⟨fun hr x hx => ?_, fun h => ?_⟩
  · rw [← hr, mem_reflSet_iff] at hx
    exact hx.left_mem
  · ext x y
    simp only [restrict, and_iff_left_iff_imp]
    exact fun hxy => ⟨h <| refl_of_left hxy, h <| refl_of_right hxy⟩



def PER (α : Type*) := {r : α → α → Prop // IsSymm α r ∧ IsTrans α r}

namespace PER

variable {r' s' : PER α}

instance : FunLike (PER α) α (α → Prop) where
  coe := Subtype.val
  coe_injective' := Subtype.val_injective

@[ext] lemma ext {r s : PER α} (h : ⇑r = ⇑s) : r = s :=
  instFunLikeForallProp.coe_injective.eq_iff.mp h

instance : IsSymm α r' := r'.property.1
instance : IsTrans α r' := r'.property.2
instance : IsSymm α r'.val := r'.property.1
instance : IsTrans α r'.val := r'.property.2
instance : PartialOrder (PER α) := Subtype.partialOrder _
instance : OrderTop (PER α) := Subtype.orderTop ⟨inferInstance, inferInstance⟩
instance : OrderBot (PER α) := Subtype.orderBot ⟨inferInstance, inferInstance⟩
instance : CompleteLattice (PER α) where
  sup r s := ⟨TransClosure (r ⊔ s), inferInstance, inferInstance⟩
  le_sup_left r s := by
    change r ≤ TransClosure (r ⊔ s)
    exact le_trans le_sup_left (TransClosure.le_closure _)
  le_sup_right r s := by
    change s ≤ TransGen (r ⊔ s)
    exact le_trans le_sup_right (TransClosure.le_closure _)
  sup_le r s t hrt hst := by
    change TransClosure (r ⊔ s) ≤ t
    exact ClosureOperator.closure_min (sup_le hrt hst) t.prop.2.trans
  inf r s := ⟨r ⊓ s, inferInstance, inferInstance⟩
  inf_le_left r s := by
    change r.val ⊓ s ≤ r
    exact inf_le_left
  inf_le_right r s := by
    change r.val ⊓ s ≤ s
    exact inf_le_right
  le_inf r s t hrt hst := by
    change r ≤ s.val ⊓ t
    exact le_inf hrt hst
  sSup s := ⟨TransGen (sSup <| Subtype.val '' s),
    @instIsSymmCoeClosureOperatorForallForallPropTransClosure _ _
    <| sSup_symm (s := Subtype.val '' s) (fun r ⟨r', hr', heq⟩ => heq ▸ r'.prop.1), inferInstance⟩
  le_sSup S r hrS := by
    change r ≤ TransGen (sSup <| Subtype.val '' S)
    exact le_trans (le_sSup <| mem_image_of_mem Subtype.val hrS) (TransClosure.le_closure _)
  sSup_le S r hrS := by
    refine TransClosure.closure_min (sSup_le ?_) r.prop.2.trans
    rintro s ⟨s', hs', rfl⟩
    exact hrS s' hs'
  sInf S := ⟨sInf <| Subtype.val '' S, sInf_symm (fun r ⟨r', hr', heq⟩ => heq ▸ r'.prop.1),
    sInf_trans (fun r ⟨r', hr', heq⟩ => heq ▸ r'.prop.2)⟩
  le_sInf S r hrS := by
    change r ≤ sInf (Subtype.val '' S)
    refine le_sInf <| ?_
    rintro s ⟨s', hs', rfl⟩
    exact hrS s' hs'
  sInf_le S r hrS := sInf_le <| mem_image_of_mem Subtype.val hrS
  le_top r := by simp
  bot_le r := by simp

@[simp]
lemma sup_reflSet (r s : PER α) : reflSet (r ⊔ s : PER α) = reflSet r ⊔ reflSet s := by
  ext x
  change TransClosure (r ⊔ s) x x ↔ _
  rw [transClosure_self_iff]
  simp only [Pi.sup_apply, sup_Prop_eq, sup_eq_union, mem_union, mem_reflSet_iff]

@[simp]
lemma inf_reflSet (r s : PER α) : reflSet (r ⊓ s : PER α) = reflSet r ⊓ reflSet s := rfl

@[simp]
lemma sSup_reflSet (s : Set (PER α)) :
    reflSet (sSup s : PER α) = ⋃₀ ((reflSet ∘ Subtype.val) '' s) := by
  ext x
  change TransClosure _ x x ↔ _
  have := foo_sSup (s := Subtype.val '' s) (fun r ⟨r', hr', heq⟩ => heq ▸ inferInstance)
  rw [transClosure_self_iff]
  simp

@[simp]
lemma sInf_reflSet (s : Set (PER α)) :
    reflSet (sInf s : PER α) = ⋂₀ ((reflSet ∘ Subtype.val) '' s) := by
  ext x
  have := foo_sInf (s := Subtype.val '' s) (fun r ⟨r', hr', heq⟩ => heq ▸ inferInstance)
  change sInf (Subtype.val '' s) x x ↔ _
  simp only [sInf_apply, iInf_apply, iInf_Prop_eq, Subtype.forall, mem_image, Subtype.exists,
    exists_and_right, exists_eq_right, forall_exists_index, comp_apply, mem_sInter, and_imp]
  refine ⟨fun h S r hr hrs heq => ?_, fun h r hr hrs => h (reflSet r) r hr hrs rfl⟩
  subst heq
  exact (mem_reflSet_iff r).mpr (h r hr hrs)

variable {r s : PER α}

lemma fiber_eq_fiber_iff (hx : r a a) : fiber r a = fiber r b ↔ r a b := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simp only [Set.ext_iff, mem_fiber_iff] at h
    exact h a |>.1 (symm hx)
  ext _
  exact rel_congr_right h

lemma fiber_eq_fiber (hxy : r a b) : fiber r a = fiber r b :=
  fiber_eq_fiber_iff (refl_of_left hxy) |>.2 hxy

instance : HasSubset (PER α) where
  Subset r s := fibers r ⊆ fibers s

lemma le_of_subset {r s : PER α} (h : r ⊆ s) : r ≤ s := by
  rintro a b hr
  obtain ⟨c, hc, heq⟩ := h <| fiber_mem_fibers hr
  have ha : a ∈ fiber r b := hr
  have hb : b ∈ fiber r b := refl_of_right hr
  rw [← heq] at ha hb
  exact trans' ha (symm hb)

instance : IsPartialOrder (PER α) (· ⊆ ·) where
  refl _ _ := id
  antisymm _ _ h₁ h₂ := le_antisymm (le_of_subset h₁) (le_of_subset h₂)
  trans _ _ _ h₁ h₂ _ a := h₂ (h₁ a)

lemma fibers_inj (h : fibers r = fibers s) : r = s :=
  le_antisymm (le_of_subset h.subset) (le_of_subset h.superset)



def comply (r : PER α) (s : α → α → Prop) : α → α → Prop :=
  Comp (Comp r s) r

lemma comply_mono (r : PER α) {s t : α → α → Prop} (hst : s ≤ t) :
    comply r s ≤ comply r t := by
  rintro x y h'
  let ⟨u, ⟨v, hxy, havu⟩, huy⟩ := h'
  exact ⟨u, ⟨v, hxy, hst _ _ havu⟩, huy ⟩

@[simp]
lemma comply_idem (r : PER α) (s : α → α → Prop) :
    comply r (comply r s) = comply r s := by
  unfold comply
  rw [comp_assoc, comp_idem_right, comp_assoc, comp_idem_left]

@[simp]
lemma comply_comp_left (r : PER α) (s : α → α → Prop) :
    Comp r (comply r s) = comply r s := by
  unfold comply
  rw [comp_assoc, comp_idem_left]

@[simp]
lemma comply_comp_right (r : PER α) (s : α → α → Prop) : Comp (comply r s) r = comply r s := by
  unfold comply
  rw [comp_assoc, comp_self]

lemma comply_reflset_mono {r : PER α} {s₁ s₂ : α → α → Prop} (h₁ : s₁ ≤ s₂) :
    reflSet (comply r s₁) ≤ reflSet (comply r s₂) :=
  fun _ ⟨u, ⟨v, huv, hvx⟩, huy⟩ => ⟨u, ⟨v, huv, h₁ _ _ hvx⟩, huy⟩

lemma comply_reflset_subset (r : PER α) (s : α → α → Prop) : reflSet (comply r s) ⊆ reflSet r :=
  fun _ ⟨_, ⟨_, huv, _⟩, _⟩ => refl_of_left huv

lemma comply_mono_left (hrs : r ≤ s) (s₁ : α → α → Prop) : comply r s₁ ≤ comply s s₁ :=
  fun _ _ ⟨u, ⟨v, hxy, havu⟩, huy⟩ => ⟨u, ⟨v, hrs _ _ hxy, havu⟩, hrs _ _ huy⟩

lemma restrict_reflSet_le_comply (r : PER α) (s : α → α → Prop) :
    restrict s (reflSet r) ≤ comply r s :=
  fun x y ⟨hxy, hx, hy⟩ => ⟨y, ⟨x, hx, hxy⟩, hy⟩

@[simp]
lemma restrict_comply_eq_comply (r : PER α) (s : α → α → Prop) :
    comply r (restrict s (reflSet r)) = comply r s := by
  ext x y
  exact ⟨fun ⟨u, ⟨v, hxv, hsvu, hv, hu⟩, huy⟩ => ⟨u, ⟨v, hxv, hsvu⟩, huy⟩,
    fun ⟨u, ⟨v, hxv, hsvu⟩, huy⟩ => ⟨u, ⟨v, hxv, hsvu, refl_of_right hxv, refl_of_left huy⟩, huy⟩⟩

lemma comply_le {s t : α → α → Prop} (h1 : restrict s (reflSet r) ≤ t)
    (h2 : comply r t ≤ t) : comply r s ≤ t :=
  (restrict_comply_eq_comply r _) ▸ comply_mono r h1 |>.trans h2

end PER
end Relation
