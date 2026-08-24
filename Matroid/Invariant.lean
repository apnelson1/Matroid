module

public import Matroid.ForMathlib.Matroid.Map
public import Matroid.ForMathlib.Matroid.Dual
public import Matroid.ForMathlib.Matroid.Closure

@[expose] public section

namespace Matroid

open Set Function

section InvariantSetPred

universe u v w u' v' u₀ u₁ u₂ u₀' u₁' u₂' v₀ v₁ v₂ v₀' v₁' v₂'

variable {α : Type u} {β : Type v} {M : Matroid α}

/-- `Matroid.SupportClass γ` means that for `M : Matroid α`, terms of type `γ α` have a notion of
'supported' that depends only on the ground set of `M`. For sets, this is containment in `M.E`,
and for elements, this is membership in `M.E`.  -/
protected class SupportClass (γ : Type u → Sort u') where
  supported : ∀ {α : Type u}, Matroid α → γ α → Prop
  congr : ∀ {α} {M M' : Matroid α}, M.E = M'.E → ∀ X, supported M X ↔ supported M' X

namespace SupportClass

/-- Supportedness of a pure sort. (Everything is supported.) -/
protected instance pure {μ : Sort u'} : Matroid.SupportClass (fun _ ↦ μ) where
  supported M X := True
  congr := by simp

@[simp]
lemma supported_pure {μ : Sort u'} {M : Matroid α} {X : μ}:
    Matroid.SupportClass.supported (γ := fun _ ↦ μ) M X :=
  trivial

/-- Supportedness of lists. -/
@[simps]
protected instance list : Matroid.SupportClass List where
  supported M X := ∀ e ∈ X, e ∈ M.E
  congr := by simp +contextual

/-- Supportedness of elements. -/
@[simps]
protected instance id : Matroid.SupportClass id where
  supported M x := x ∈ M.E
  congr := by simp +contextual

/-- Supportedness of sets. -/
@[simps]
protected instance set : Matroid.SupportClass Set where
  supported M X := X ⊆ M.E
  congr := by simp +contextual

/-- Supportedness of sets of supported types. -/
@[simps]
protected instance toSet (γ : Type* → Type*) [hγ : Matroid.SupportClass γ] :
    Matroid.SupportClass (fun α ↦ Set (γ α)) where
  supported M s := ∀ x ∈ s, hγ.supported M x
  congr := by
    intro α M M' hM X
    simp_rw [hγ.congr hM]

/-- Supportedness of tuples of supported types. -/
@[simps]
protected instance toFun {ι : Type*} {γ : Type* → Type*}
    [hγ : Matroid.SupportClass γ] : Matroid.SupportClass (fun α ↦ (ι → γ α)) where
  supported M X := ∀ i, hγ.supported M (X i)
  congr := by
    intro α M M' hE X
    simp_rw [hγ.congr hE]

/-- Supportedness of lists of supported types. -/
@[simps]
protected instance toList {γ : Type* → Type*}
    [hγ : Matroid.SupportClass γ] : Matroid.SupportClass (fun α ↦ (List (γ α))) where
  supported M L := ∀ x ∈ L, hγ.supported M x
  congr := by
    intro α M M' hE L
    simp_rw [hγ.congr hE]

end SupportClass

/-- `Matroid.TransferClass γ δ` contains the data needed to move terms of type
`γ α` to ones of type `δ β` via a function `f : α → β`. Transferred values need to respect
supportedness in a given matroid. -/
protected class TransferClass (γ : Type u → Sort u') (δ : Type v → Sort v')
    [Sγ : Matroid.SupportClass γ] [Sδ : Matroid.SupportClass δ] where
  transfer : ∀ {α : Type u} {β : Type v}, (α → β) → (γ α → δ β)
  transferEmpty : ∀ {α β}, IsEmpty β → (x : γ α) → Sγ.supported (emptyOn α) x → δ β
  supported_transfer : ∀ ⦃α β⦄ ⦃M : Matroid α⦄ ⦃f : α → β⦄ (hf : InjOn f M.E) ⦃x : γ α⦄,
    Sγ.supported M x → Sδ.supported (M.map f hf) (transfer f x)
  supported_transferEmpty : ∀ ⦃α β⦄ (hβ : IsEmpty β) (x : γ α) (hx : Sγ.supported (emptyOn α) x),
    Sδ.supported (emptyOn β) (transferEmpty hβ x hx)

namespace TransferClass

@[simps]
protected instance pure {μ : Sort u'} : Matroid.TransferClass (fun _ ↦ μ) (fun _ ↦ μ) where
  transfer _ x := x
  transferEmpty _ x _ := x
  supported_transfer := by simp
  supported_transferEmpty := by simp

@[simps]
protected instance id : Matroid.TransferClass id id where
  transfer := id
  transferEmpty _ _ h := by simp at h
  supported_transfer _ _ _ _ _ x hx := ⟨x, hx, rfl⟩
  supported_transferEmpty := by simp

@[simps]
protected instance set : Matroid.TransferClass Set Set where
  transfer := Set.image
  transferEmpty := fun _ _ _ ↦ ∅
  supported_transfer _ _ _ _ _ _ := image_mono
  supported_transferEmpty := by simp

@[simps]
protected instance list : Matroid.TransferClass List List where
  transfer f X := X.map f
  transferEmpty _ _ _ := []
  supported_transfer α β M f hf L hL e he := by
    obtain ⟨x, hxL, rfl⟩ := List.mem_map.1 he
    exact mem_image_of_mem f <| hL x hxL
  supported_transferEmpty := by simp

@[simps]
protected instance toSet {γ δ : Type* → Type*} [Sγ : Matroid.SupportClass γ]
    [Sδ : Matroid.SupportClass δ] [T : Matroid.TransferClass γ δ] :
    Matroid.TransferClass (fun α ↦ Set (γ α)) (fun β ↦ Set (δ β)) where
  transfer f X := (T.transfer f) '' X
  transferEmpty := @fun α β hβ X hX ↦
    {y | ∃ (x : γ α) (_ : x ∈ X) (hx : Sγ.supported (emptyOn α) x), T.transferEmpty hβ x hx = y}
  supported_transfer α β M f hf X hX := by
    rintro _ ⟨x, hx, rfl⟩
    exact T.supported_transfer hf (x := x) (hX _ hx)
  supported_transferEmpty α β hβ x hx := by
    simp only [SupportClass.toSet_supported, mem_ofPred_eq, forall_exists_index]
    rintro _ x hxX hx rfl
    exact T.supported_transferEmpty hβ x hx

@[simps]
protected instance toList {γ δ : Type* → Type*} [Sγ : Matroid.SupportClass γ]
    [Sδ : Matroid.SupportClass δ] [T : Matroid.TransferClass γ δ] :
    Matroid.TransferClass (fun α ↦ List (γ α)) (fun β ↦ List (δ β)) where
  transfer f X := X.map (T.transfer f)
  transferEmpty hβ L hL := L.pmap (T.transferEmpty hβ) <| by simpa
  supported_transfer α β M f hf X hx := by
    simpa using fun x hxX ↦ T.supported_transfer hf <| hx x hxX
  supported_transferEmpty α β hβ L hx := by
    simpa using fun y x hxL hx_eq ↦ hx_eq ▸ T.supported_transferEmpty hβ x (hx x hxL)

@[simps transferEmpty]
protected instance toFun {γ δ : Type* → Type*} {ι : Type*} [hγ : Matroid.SupportClass γ]
    [Matroid.SupportClass δ] [T: Matroid.TransferClass γ δ] :
     Matroid.TransferClass (fun α ↦ (ι → γ α)) (fun β ↦ (ι → δ β)) where
  transfer f X := fun i ↦ (T.transfer f) (X i)
  transferEmpty hβ x hx i := T.transferEmpty hβ (x i) (hx i)
  supported_transfer _ _ _ _ hf _ hx i := T.supported_transfer hf (hx i)
  supported_transferEmpty _ _ hβ x _ i := T.supported_transferEmpty hβ (x i) _

@[simp]
protected lemma toFun_transfer_eq {γ : Type u → Type u'} {δ : Type v → Type v'} {ι : Type*}
    [hγ : Matroid.SupportClass γ] [Matroid.SupportClass δ] [T: Matroid.TransferClass γ δ]
    {α : Type u} {β : Type v} {f : α → β} {X : ι → γ α} :
    (Matroid.TransferClass.transfer (γ := fun α ↦ (ι → γ α)) (δ := fun β ↦ (ι → δ β))) f X =
      fun i ↦ (T.transfer f) (X i) := rfl

end TransferClass

/-- A function from matroids is grounded if it always takes values in the ground set. -/
class GroundedFun {γ : Type u → Sort u'} [S : Matroid.SupportClass γ]
    (F : ∀ {α}, Matroid α → γ α) : Prop where
  supported : ∀ ⦃α⦄ (M : Matroid α), S.supported M (F M)

class GroundedFun₂ {γ γ' : Type u → Sort*} [S : Matroid.SupportClass γ]
    [S' : Matroid.SupportClass γ'] (F : ∀ {α}, Matroid α → γ α → γ' α) : Prop where
  supported : ∀ ⦃α⦄ (M : Matroid α) (x : γ α), S.supported M x → S'.supported M (F M x)

instance {μ : Type w} (F : ∀ {α}, Matroid α → μ) : GroundedFun F where
  supported := by simp

instance {γ : Type u → Sort*} {μ : Sort*} [Matroid.SupportClass γ]
    (F : ∀ {α}, Matroid α → γ α → μ) : GroundedFun₂ F where
  supported := by simp

instance : GroundedFun₂ Matroid.closure where
  supported := by simp [closure_subset_ground]

/-- A predicate of type `γ α → Prop` is a `GroundedPred` if it is only true for elements of `γ α`
that are supported by `M`. -/
class GroundedPred {γ : Type u → Sort u'} [S : Matroid.SupportClass γ]
    (P : ∀ {α}, Matroid α → γ α → Prop) where
  supported : ∀ ⦃α⦄ ⦃M : Matroid α⦄ ⦃x⦄, P M x → S.supported M x

class GroundedPred₂ {γ₁ : Type u → Sort u₁} {γ₂ : Type u → Sort u₂} [S₁ : Matroid.SupportClass γ₁]
    [S₂ : Matroid.SupportClass γ₂] (P : ∀ {α}, Matroid α → γ₁ α → γ₂ α → Prop) where
  supported : ∀ ⦃α⦄ ⦃M : Matroid α⦄ ⦃x y⦄, P M x y → (S₁.supported M x ∧ S₂.supported M y)

instance : GroundedPred Indep where
  supported _ _ _ := Indep.subset_ground

instance : GroundedPred Dep where
  supported _ _ _ := Dep.subset_ground

instance : GroundedPred IsBase where
  supported _ _ _ := IsBase.subset_ground

instance : GroundedPred Spanning where
  supported _ _ _ := Spanning.subset_ground

instance : GroundedPred Nonspanning where
  supported _ _ _ := Nonspanning.subset_ground

instance : GroundedPred Coindep where
  supported _ _ _ := Coindep.subset_ground

instance : GroundedPred Codep where
  supported _ _ _ := Codep.subset_ground

instance : GroundedPred₂ IsBasis where
  supported _ _ _ _ h := ⟨h.indep.subset_ground, h.subset_ground⟩


class Invariant {γ δ : Type* → Sort*}
    [S : Matroid.SupportClass γ] [T : Matroid.SupportClass δ] [C : Matroid.TransferClass γ δ]
    (F : ∀ {α}, Matroid α → γ α) (G : ∀ {β}, Matroid β → δ β) : Prop where
  map_eq : ∀ ⦃α β⦄ ⦃M : Matroid α⦄ ⦃f : α → β⦄ (h : InjOn f M.E), C.transfer f (F M) = G (M.map f h)

lemma Invariant.and (P P' : {α : Type u} → Matroid α → Prop)
    (Q Q' : {α : Type v} → Matroid α → Prop) [h : Invariant P Q] [h' : Invariant P' Q'] :
    Invariant (fun M ↦ P M ∧ P' M) (fun M ↦ Q M ∧ Q' M) where
  map_eq := by simp [← h.map_eq, ← h'.map_eq]

class InvariantFun {γ₁ : Type u → Sort u₁} {γ₂ : Type u → Sort u₂}
    {δ₁ : Type v → Sort v₁} {δ₂ : Type v → Sort v₂}
    [S₁ : Matroid.SupportClass γ₁] [S₂ : Matroid.SupportClass γ₂]
    [T₁ : Matroid.SupportClass δ₁] [T₂ : Matroid.SupportClass δ₂]
    [C₁ : Matroid.TransferClass γ₁ δ₁] [C₂ : Matroid.TransferClass γ₂ δ₂]
    (F : ∀ {α}, Matroid α → γ₁ α → γ₂ α) (G : ∀ {β}, Matroid β → δ₁ β → δ₂ β) : Prop where
  of_empty : ∀ ⦃α⦄ ⦃β : Type v⦄ (hβ : IsEmpty β) ⦃x : γ₁ α⦄ (hx : S₁.supported (emptyOn α) x)
      (hx' : S₂.supported (emptyOn α) (F (emptyOn α) x)),
    C₂.transferEmpty (α := α) hβ (F (emptyOn α) x) hx' = G (emptyOn β) (C₁.transferEmpty hβ x hx)
  map_eq : ∀ ⦃α β⦄ ⦃M : Matroid α⦄ ⦃f : α → β⦄ (hf : InjOn f M.E) ⦃x : γ₁ α⦄,
    S₁.supported M x → C₂.transfer f (F M x) = G (M.map f hf) (C₁.transfer f x)

/-- This could be generalized further like `InvariantFun`,
allowing the output type to take values in a sort depending on the matroid type -/
class InvariantFun₂ {γ₁ : Type u → Sort u₁} {γ₂ : Type u → Sort u₂}
    {δ₁ : Type v → Sort v₁} {δ₂ : Type v → Sort v₂} {μ : Sort w}
    [S₁ : Matroid.SupportClass γ₁] [T₁ : Matroid.SupportClass δ₁] [C₁ : Matroid.TransferClass γ₁ δ₁]
    [S₂ : Matroid.SupportClass γ₂] [T₂ : Matroid.SupportClass δ₂] [C₂ : Matroid.TransferClass γ₂ δ₂]
    (F : ∀ {α}, Matroid α → (γ₁ α) → (γ₂ α) → μ) (G : ∀ {β}, Matroid β → (δ₁ β) → (δ₂ β) → μ) : Prop
      where
  of_empty : ∀ ⦃α β⦄ (hβ : IsEmpty β) ⦃x : γ₁ α⦄ ⦃x' : γ₂ α⦄ (hx : S₁.supported (emptyOn α) x)
      (hx' : S₂.supported (emptyOn α) x'),
    F (emptyOn α) x x' = G (emptyOn β) (C₁.transferEmpty hβ x hx) (C₂.transferEmpty hβ x' hx')
  map_eq : ∀ ⦃α β⦄ ⦃M : Matroid α⦄ ⦃f : α → β⦄ (hf : InjOn f M.E) ⦃x x'⦄, S₁.supported M x →
    S₂.supported M x' → F M x x' = G (M.map f hf) (C₁.transfer f x) (C₂.transfer f x')

-- def foo.{u,v,w} {γ₁ γ₂ : Type u → Sort*} [Matroid.SupportClass γ]
--     [Matroid.TransferClass γ.{u} γ.{v}] (F : ∀ {α : Type*}, Matroid α → γ₁ α )

namespace InvariantFun

variable {γ₁ γ₂ γ₃ : Type u → Sort*} {δ₁ δ₂ δ₃ : Type v → Sort*} {μ μ' : Sort*}
    [S₁ : Matroid.SupportClass γ₁] [S₂ : Matroid.SupportClass γ₂] [S₃ : Matroid.SupportClass γ₃]
    [T₁ : Matroid.SupportClass δ₁] [T₂ : Matroid.SupportClass δ₂] [T₃ : Matroid.SupportClass δ₃]
    [C₁ : Matroid.TransferClass γ₁ δ₁] [C₂ : Matroid.TransferClass γ₂ δ₂]
      [C₃ : Matroid.TransferClass γ₃ δ₃]

instance {f : μ → μ'} : InvariantFun (fun _ ↦ f) (fun _ ↦ f) where
  of_empty := by simp
  map_eq := by simp

lemma map_pure_eq (F : ∀ {α}, Matroid α → (γ₁ α) → μ) (G : ∀ {β}, Matroid β → (δ₁ β) → μ)
    [h : InvariantFun F G] {M : Matroid α} {f : α → β} {hf : InjOn f M.E} {x : γ₁ α}
    (hx : S₁.supported M x) : G (M.map f hf) (C₁.transfer f x) = F M x :=
  Eq.symm <| h.map_eq hf hx

protected lemma comp_right' (F : ∀ {α}, Matroid α → (γ₁ α) → (γ₂ α))
    (G : ∀ {β}, Matroid β → (δ₁ β) → (δ₂ β)) [h : InvariantFun F G]
    [hF : GroundedFun₂ F]
    (s : ∀ {α}, Matroid α → γ₂ α → γ₃ α) (t : ∀ {β}, Matroid β → δ₂ β → δ₃ β)
    [hst : InvariantFun s t] :
    InvariantFun (fun M x ↦ s M (F M x)) (fun N y ↦ t N (G N y)) where
  of_empty α β hβ x hx hx' := by
    rw [← h.of_empty, hst.of_empty hβ (x := F (emptyOn α) x) (hF.supported _ x hx) _]
  map_eq α β M f hf x hx := by
    rw [← h.map_eq hf hx]
    exact hst.map_eq hf (x := F M x) <| hF.supported M x hx

protected lemma comp_right {μ μ' : Sort*} (F : ∀ {α}, Matroid α → (γ₁ α) → μ)
    (G : ∀ {β}, Matroid β → (δ₁ β) → μ) [h : InvariantFun F G] (s : μ → μ') :
    InvariantFun (fun {α} (M : Matroid α) (x : γ₁ α) ↦ s (F M x))
      (fun {β} (N : Matroid β) (y : δ₁ β) ↦ s (G N y)) :=
  InvariantFun.comp_right' F G (fun _ ↦ s) (fun _ ↦ s)

protected lemma comp_left {γ₁' : Type u → Sort*} {δ₁' : Type v → Sort*}
    [S₁' : Matroid.SupportClass γ₁'] [T₁' : Matroid.SupportClass δ₁']
    [C₁' : Matroid.TransferClass γ₁' δ₁'] (F : ∀ {α}, Matroid α → (γ₁ α) → γ₂ α)
    (G : ∀ {β}, Matroid β → (δ₁ β) → δ₂ β) [h : InvariantFun F G]
    (a : ∀ {α}, Matroid α → γ₁' α → γ₁ α) (b : ∀ {β}, Matroid β → δ₁' β → δ₁ β)
    (ha : ∀ {α} (M : Matroid α) x, S₁'.supported M x → S₁.supported M (a M x))
    (hab0 : ∀ {α β} (hβ : IsEmpty β) (x) (hx : S₁'.supported (emptyOn α) x),
      C₁.transferEmpty hβ (a (emptyOn α) x) (ha _ _ hx) = b (emptyOn β) (C₁'.transferEmpty hβ x hx))
    (hab : ∀ {α β} (M) (f : α → β) (hf : InjOn f M.E) (x : γ₁' α), S₁'.supported M x →
      (C₁.transfer f (a M x)) = b (M.map f hf) (C₁'.transfer f x)) :
      InvariantFun (γ₁ := γ₁') (δ₁ := δ₁') (fun M X ↦ F M (a M X)) (fun N Y ↦ G N (b N Y)) where
  of_empty α β hβ x hx hx' := by
    rw [h.of_empty _ _ hx', hab0 _ _ hx]
    exact ha _ _ hx
  map_eq α β M f hf x hx := by rw [h.map_eq hf (ha _ _ hx), hab _ _ _ _ hx]

protected lemma combine (F F' : ∀ {α}, Matroid α → (γ₁ α) → μ)
    (G G' : ∀ {β}, Matroid β → (δ₁ β) → μ)
    [h : InvariantFun F G] [h' : InvariantFun F' G'] (φ : μ → μ → μ) :
    InvariantFun (fun {α} (M : Matroid α) (x : γ₁ α) ↦ φ (F M x) (F' M x))
      (fun {β} (N : Matroid β) (x : δ₁ β) ↦ φ (G N x) (G' N x)) where
  of_empty α β hβ x hx hx' := by
    rw [← h.of_empty hβ hx hx', ← h'.of_empty hβ hx hx']
    rfl
  map_eq α β M f hf x hxE := by
    rw [← h.map_eq hf hxE, ← h'.map_eq hf hxE]
    rfl

protected lemma dual (F : ∀ {α}, Matroid α → γ₁ α → γ₂ α) (G : ∀ {β}, Matroid β → δ₁ β → δ₂ β)
    [h : InvariantFun F G] : InvariantFun (fun M X ↦ F M✶ X) (fun N Y ↦ G N✶ Y) where
  of_empty α β hβ x hx hx' := by
    simp only [emptyOn_dual_eq]
    rw [h.of_empty]
  map_eq α β M f hf x hx := by
    rw [map_dual', ← h.map_eq]
    rwa [S₁.congr (M := M✶) (M' := M) rfl x]

protected lemma compl (F : ∀ {α}, Matroid α → Set α → γ₂ α) (G : ∀ {β}, Matroid β → Set β → δ₂ β)
    [h : InvariantFun F G] :
    InvariantFun (γ₁ := Set) (δ₁ := Set) (fun M X ↦ F M (M.E \ X)) (fun N Y ↦ G N (N.E \ Y)) := by
  apply InvariantFun.comp_left F G
  · simp
  · simp +contextual [InjOn.image_sdiff_subset]
  simp

protected lemma encard : InvariantFun (fun {α : Type u} (_ : Matroid α) (X : Set α) ↦ X.encard)
    (fun {β : Type v} (_ : Matroid β) (Y : Set β) ↦ Y.encard) where
  of_empty := by simp
  map_eq α β M f hf X hX := by simp [(hf.mono hX).encard_image]

protected lemma iff_ext (F : ∀ {α}, Matroid α → γ₁ α → γ₂ α) (G : ∀ {β}, Matroid β → δ₁ β → δ₂ β) :
    InvariantFun F G ↔ InvariantFun (fun M x ↦ F M x) (fun N y ↦ G N y) := Iff.rfl

section Pred

variable {P : ∀ {α : Type u}, Matroid α → (γ₁ α) → Prop}
  {Q : ∀ {β : Type v}, Matroid β → (δ₁ β) → Prop}

protected lemma map
    [h : InvariantFun P Q] [hP : GroundedPred P] {M : Matroid α} {f : α → β} {x}
    (hx : P M x) (hf : InjOn f M.E) : Q (M.map f hf) (C₁.transfer f x) := by
  rwa [← h.map_eq _ (hP.supported hx)]

protected lemma map_iff [h : InvariantFun P Q] {M : Matroid α} {f : α → β} {x} (hf : InjOn f M.E)
    (hx : Matroid.SupportClass.supported M x) : Q (M.map f hf) (C₁.transfer f x) ↔ P M x := by
  rw [← eq_iff_iff, eq_comm]
  exact h.map_eq hf hx

protected lemma map_elem_iff {P Q : ∀ {α}, Matroid α → α → Prop}
    [h : InvariantFun (γ₁ := id) (δ₁ := id) P Q] {M : Matroid α} {f : α → β} {x : α}
    (hf : InjOn f M.E) (hx : x ∈ M.E) :
    Q (M.map f hf) (f x) ↔ P (α := α) M x :=
  InvariantFun.map_iff (γ₁ := id) (δ₁ := id) (P := P) (Q := Q) hf hx

protected lemma map_set {P : ∀ {α}, Matroid α → Set α → Prop} {Q : ∀ {β}, Matroid β → Set β → Prop}
    [h : InvariantFun P Q] [hP : GroundedPred P] {M : Matroid α} {f : α → β} {x}
    (hx : P M x) (hf : InjOn f M.E) : Q (M.map f hf) (f '' x) :=
  h.map hx hf

protected lemma map_elem {P : ∀ {α}, Matroid α → α → Prop} {Q : ∀ {β}, Matroid β → β → Prop}
    [h : InvariantFun (γ₁ := id) (δ₁ := id) P Q] [hP : GroundedPred (γ := id) P]
    {M : Matroid α} {f : α → β} {x}
    (hx : P M x) (hf : InjOn f M.E) : Q (M.map f hf) (f x) :=
  h.map hx hf

protected lemma map_set_image_iff {P : ∀ {α}, Matroid α → Set α → Prop}
    {Q : ∀ {β}, Matroid β → Set β → Prop} [h : InvariantFun P Q] {M : Matroid α} {f : α → β} {X}
    (hX : X ⊆ M.E) (hf : InjOn f M.E) :  Q (M.map f hf) (f '' X) ↔ P M X := by
  simpa using (h.map_eq hf hX).symm

protected lemma map_set_iff_exists {P : ∀ {α}, Matroid α → Set α → Prop}
    {Q : ∀ {β}, Matroid β → Set β → Prop} [h : InvariantFun P Q] [hP : GroundedPred P]
    [hQ : GroundedPred Q] {M : Matroid α} {f : α → β} {X} (hf : InjOn f M.E) :
    Q (M.map f hf) X ↔ ∃ X₀, P M X₀ ∧ X = f '' X₀ := by
  refine ⟨fun h' ↦ ?_, ?_⟩
  · obtain ⟨X, hX, rfl⟩ := subset_image_iff.1 <| hQ.supported h'
    rw [h.map_set_image_iff hX] at h'
    exact ⟨X, h', rfl⟩
  rintro ⟨X, hX, rfl⟩
  exact h.map_set hX hf

protected lemma mapEquiv_set_iff {P : ∀ {α}, Matroid α → Set α → Prop}
    {Q : ∀ {β}, Matroid β → Set β → Prop} [h : InvariantFun P Q] [hP : GroundedPred P]
    [hQ : GroundedPred Q] {M : Matroid α} {f : α ≃ β} {X : Set β} :
    Q (M.mapEquiv f) X ↔ P M (f ⁻¹' X) := by
  rw [mapEquiv_eq_map, h.map_set_iff_exists]
  exact ⟨by rintro ⟨X, hX, rfl⟩; simpa, fun h ↦ ⟨f ⁻¹' X, ⟨h, by simp⟩⟩⟩

protected lemma and (P P' : ∀ {α}, Matroid α → (γ₁ α) → Prop)
    (Q Q' : ∀ {β}, Matroid β → (δ₁ β) → Prop) [h : InvariantFun P Q] [h' : InvariantFun P' Q'] :
    InvariantFun.{u,v} (fun M X ↦ P M X ∧ P' M X) (fun M X ↦ Q M X ∧ Q' M X) :=
  InvariantFun.combine P P' Q Q' And

protected lemma andSupported (P : ∀ {α}, Matroid α → γ₁ α → Prop)
    (Q : ∀ {β}, Matroid β → δ₁ β → Prop) [h : InvariantFun P Q] :
    InvariantFun (fun M X ↦ P M X ∧ S₁.supported M X) (fun M X ↦ Q M X ∧ T₁.supported M X) where
  of_empty α β hβ x hx hx' := by
    rw [← h.of_empty, and_iff_left (C₁.supported_transferEmpty hβ x hx), and_iff_left hx]
  map_eq α β M f hf x hx := by simp [← h.map_eq hf, hx, C₁.supported_transfer]

protected lemma notAndSupported (P : ∀ {α}, Matroid α → γ₁ α → Prop)
    (Q : ∀ {β}, Matroid β → δ₁ β → Prop) [h : InvariantFun P Q] :
    InvariantFun (fun M X ↦ ¬ P M X ∧ S₁.supported M X) (fun M X ↦ ¬ Q M X ∧ T₁.supported M X) :=
  (h.comp_right (F := P) (G := Q) Not).andSupported

protected lemma minimal (P : ∀ {α}, Matroid α → Set α → Prop) (Q : ∀ {β}, Matroid β → Set β → Prop)
    [h : InvariantFun P Q] [hP : GroundedPred P] :
    InvariantFun (fun {α} M (X : Set α) ↦ Minimal (P M) X)
      (fun {β} N {Y : Set β} ↦ Minimal (Q N) Y) where
  of_empty α β hβ x hx := by
    obtain rfl : x = ∅ := by simpa using hx
    simpa [Minimal] using h.of_empty (α := α) hβ (x := ∅)
  map_eq α β M f hf X (hX : X ⊆ M.E) := by
    simp_rw [eq_iff_iff, minimal_subset_iff, ← h.map_eq hf hX, TransferClass.set_transfer,
      TransferClass.pure_transfer, and_congr_right_iff]
    refine fun hPX ↦ ⟨fun h' Y hY hYX ↦ ?_, fun h' Y hPY hYX ↦ ?_⟩
    · obtain ⟨Y, hYX', rfl⟩ := subset_image_iff.1 hYX
      rw [← TransferClass.set_transfer, ← h.map_eq hf (hYX'.trans hX)] at hY
      rw [h' hY hYX']
    rw [← hf.image_eq_image_iff hX (hYX.trans hX), h' (h.map_set hPY hf) (image_mono hYX)]

protected lemma maximal (P : ∀ {α}, Matroid α → Set α → Prop) (Q : ∀ {β}, Matroid β → Set β → Prop)
    [h : InvariantFun P Q] [hP : GroundedPred P] [hQ : GroundedPred Q] :
    InvariantFun (fun {α} M (X : Set α) ↦ Maximal (P M) X)
      (fun {β} N {Y : Set β} ↦ Maximal (Q N) Y) where
  of_empty α β hβ x hx := by
    obtain rfl : x = ∅ := by simpa using hx
    have aux ⦃y⦄ (hy : P (emptyOn α) y) : y = ∅ := by simpa using hP.supported hy
    simpa [Maximal, and_iff_left aux] using h.of_empty (α := α) hβ hx
  map_eq α β M f hf X (hX : X ⊆ M.E) := by
    simp_rw [eq_iff_iff, maximal_subset_iff, ← h.map_eq hf hX, TransferClass.set_transfer,
      TransferClass.pure_transfer, and_congr_right_iff]
    refine fun hPX ↦ ⟨fun h' Y hY hYX ↦ ?_, fun h' Y hPY hYX ↦ ?_⟩
    · obtain ⟨Y, hYE, rfl⟩ := subset_image_iff.1 <| hQ.supported hY
      rw [hf.image_subset_image_iff hX hYE] at hYX
      rw [← TransferClass.set_transfer, ← h.map_eq _ hYE] at hY
      rw [h' hY hYX]
    rw [← hf.image_eq_image_iff hX (hP.supported hPY), h' (h.map_set hPY hf) (image_mono hYX)]

section SetPred

end SetPred

section instances

instance instIndep : InvariantFun Indep Indep where
  of_empty := by simp
  map_eq α β M f hf X (hX : X ⊆ M.E) := by
    simp only [TransferClass.pure_transfer, TransferClass.set_transfer, map_image_indep_iff hX]

instance instCoindep : InvariantFun Coindep Coindep :=
  InvariantFun.dual Indep Indep

instance instDep : InvariantFun Dep Dep := by
  simpa [← dep_iff] using InvariantFun.notAndSupported Indep Indep

instance instBase : InvariantFun IsBase IsBase := by
  simpa [← isBase_iff_maximal_indep] using InvariantFun.maximal Indep Indep

instance instCodep : InvariantFun Codep Codep :=
  InvariantFun.dual Dep Dep

instance instSpanning : InvariantFun Spanning Spanning := by
  simpa [← spanning_iff_compl_coindep'] using (InvariantFun.compl Coindep Coindep).andSupported

instance instNonspanning : InvariantFun Nonspanning Nonspanning := by
  simpa [← nonspanning_iff] using InvariantFun.notAndSupported Spanning Spanning

instance instIsBasis : InvariantFun₂ IsBasis IsBasis where
  of_empty := by simp
  map_eq α β M f hf I X hI hX := by simp [map_isBasis_iff _ _ hI hX]

instance instClosure : InvariantFun closure closure where
  of_empty := by simp
  map_eq α β M f hf X hX := by
    simp only [TransferClass.set_transfer, map_closure_eq]
    rw [eq_comm, ← closure_inter_ground, hf.preimage_image_inter hX]

end instances

end Pred

end InvariantFun

namespace Invariant

instance instFinite : Invariant Matroid.Finite Matroid.Finite where
  map_eq := by simp +contextual [finite_iff, finite_image_iff]

instance instNonempty : Invariant Matroid.Nonempty Matroid.Nonempty where
  map_eq := by simp [← ground_nonempty_iff]

end Invariant
