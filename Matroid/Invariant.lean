module

public import Matroid.ForMathlib.Matroid.Map
public import Matroid.ForMathlib.Matroid.Dual
public import Matroid.ForMathlib.Matroid.Closure

@[expose] public section

namespace Matroid

open Set Function

section InvariantSetPred

universe u v u' v'

variable {α : Type u} {β : Type v} {M : Matroid α} {f : α → β}

protected class hasSupport (M : Matroid α) (γ : Type u) where
  supported : γ → Prop

instance {M : Matroid α} : M.hasSupport α where
  supported e := e ∈ M.E

instance {M : Matroid α} : M.hasSupport (Set α) where
  supported X := X ⊆ M.E

instance {M : Matroid α} : M.hasSupport (List α) where
  supported L := {e | e ∈ L} ⊆ M.E

instance {M : Matroid α} : M.hasSupport (Finset α) where
  supported X := (X : Set α) ⊆ M.E

class InvariantPred {γ : Type u → Type u} {δ : Type v → Type v}
    [suppM : ∀ (α : Type u) (M : Matroid α), M.hasSupport (γ α)]
    [suppN : ∀ (β : Type v) (N : Matroid β), N.hasSupport (δ β)]
    (P : ∀ {α : Type u}, Matroid α → γ α → Prop)
    (Q : ∀ {β : Type v}, Matroid β → δ β → Prop)
    (transfer : ∀ {α : Type u} {β : Type v}, (α → β) → (γ α → δ β)) : Prop where
  supported_left : ∀ ⦃α : Type u⦄ ⦃M : Matroid α⦄ ⦃X⦄, P M X → (suppM α M).supported X
  supported_right : ∀ ⦃β : Type v⦄ ⦃N : Matroid β⦄ ⦃X⦄, Q N X → (suppN β N).supported X
  map_iff' : ∀ ⦃α : Type u⦄ ⦃β : Type v⦄ ⦃M : Matroid α⦄ ⦃X : γ α⦄ ⦃f : α → β⦄ (hf : InjOn f M.E),
      (suppM α M).supported X → (P M X ↔ Q (M.map f hf) (transfer f X))

class InvariantSetPred (P : ∀ {α : Type u}, Matroid α → Set α → Prop)
    (Q : ∀ {β : Type v}, Matroid β → Set β → Prop) where
  subset_ground_left : ∀ ⦃α : Type u⦄ ⦃M : Matroid α⦄ ⦃X⦄, P M X → X ⊆ M.E
  subset_ground_right : ∀ ⦃β : Type v⦄ ⦃M : Matroid β⦄ ⦃X⦄, Q M X → X ⊆ M.E
  map_iff' : ∀ ⦃α : Type u⦄ ⦃β : Type v⦄ ⦃M : Matroid α⦄ ⦃X⦄ ⦃f : α → β⦄ (hf : InjOn f M.E),
      X ⊆ M.E → (P M X ↔ Q (M.map f hf) (f '' X))

namespace InvariantSetPred


protected instance instAnd {P P' Q Q'} [h : InvariantSetPred P Q]
    [h' : InvariantSetPred P' Q'] :
    InvariantSetPred.{u,v} (fun M X ↦ P M X ∧ P' M X) (fun M X ↦ Q M X ∧ Q' M X) where
  subset_ground_left _ _ _ h' := h.subset_ground_left h'.1
  subset_ground_right _ _ _ h' := h.subset_ground_right h'.1
  map_iff' α β M X f hf hX := by rw [h.map_iff' hf hX, h'.map_iff' hf hX]

protected lemma of_const (P : ∀ {α : Type u}, Set α → Prop)
    (Q : ∀ {β : Type v}, Set β → Prop) (hPQ : ∀ {α β} (f : α → β) X, Q (f '' X) ↔ P X) :
    InvariantSetPred.{u,v} (fun M X ↦ P X ∧ X ⊆ M.E) (fun M X ↦ Q X ∧ X ⊆ M.E) where
  subset_ground_left := by simp
  subset_ground_right := by simp
  map_iff' α β M X f hf hX := by
    rw [map_ground, and_iff_left (image_mono hX), and_iff_left hX, ← hPQ f X]

protected lemma and_setPred {P Q} [InvariantSetPred P Q] (P' : ∀ {α : Type u}, Set α → Prop)
    (Q' : ∀ {β : Type v}, Set β → Prop) (hPQ : ∀ {α β} (f : α → β) X, Q' (f '' X) ↔ P' X) :
    InvariantSetPred (fun M X ↦ P M X ∧ P' X) (fun N X ↦ Q N X ∧ Q' X) := by
  convert @InvariantSetPred.instAnd (P := P) (Q := Q) _ _ _ (InvariantSetPred.of_const P' Q' hPQ)
    using 4 with α M X β N Y
  · simp +contextual [InvariantSetPred.subset_ground_left (P := P) (Q := Q)]
  simp +contextual [InvariantSetPred.subset_ground_right (P := P) (Q := Q)]

protected instance instNot {P Q} [h : InvariantSetPred P Q] :
    InvariantSetPred.{u, v} (fun M X ↦ ¬ P M X ∧ X ⊆ M.E) (fun M X ↦ ¬ Q M X ∧ X ⊆ M.E) where
  subset_ground_left _ _ _ := And.right
  subset_ground_right _ _ _ := And.right
  map_iff' α β M X f hf hXE := by
    rw [← h.map_iff' _ hXE, map_ground, hf.image_subset_image_iff hXE subset_rfl]

protected instance instCompl {P Q} [h : InvariantSetPred.{u, v} P Q] :
    InvariantSetPred.{u, v} (fun M X ↦ P M (M.E \ X) ∧ X ⊆ M.E)
      (fun M X ↦ Q M (M.E \ X) ∧ X ⊆ M.E) where
  subset_ground_left _ _ _ := And.right
  subset_ground_right _ _ _ := And.right
  map_iff' α β M X f hf hXE := by
    rw [map_ground, ← hf.image_sdiff_subset hXE, ← h.map_iff' _ sdiff_subset,
      hf.image_subset_image_iff hXE subset_rfl]

protected instance instDual {P Q} [h : InvariantSetPred.{u, v} P Q] :
    InvariantSetPred.{u, v} (fun M X ↦ P M✶ X) (fun M X ↦ Q M✶ X) where
  subset_ground_left _ _ _ hP := by simpa using h.subset_ground_left hP
  subset_ground_right _ _ _ hP := by simpa using h.subset_ground_right hP
  map_iff' α β M X f hf hXE := by rw [map_dual, h.map_iff' (by simpa) (by simpa)]

protected instance instMinimal {P Q} [h : InvariantSetPred.{u, v} P Q] :
    InvariantSetPred.{u,v} (fun M X ↦ Minimal (P M) X) (fun M X ↦ Minimal (Q M) X) where
  subset_ground_left _ _ _ hP := h.subset_ground_left hP.1
  subset_ground_right _ _ _ hP := h.subset_ground_right hP.1
  map_iff' α β M X f hf hXE := by
    simp_rw [minimal_subset_iff, ← h.map_iff' _ hXE, and_congr_right_iff]
    refine fun hPX ↦ ⟨fun h' Y hQY hYX ↦ ?_, fun h' Y hY hYX ↦ ?_⟩
    · obtain ⟨Y, hY, rfl⟩ := subset_image_iff.1 (h.subset_ground_right hQY)
      rw [← h.map_iff' _ hY] at hQY
      rw [hf.image_subset_image_iff hY hXE] at hYX
      rw [h' hQY hYX]
    specialize h' (t := f '' Y) (by rwa [← h.map_iff' _ (hYX.trans hXE)]) (image_mono hYX)
    rwa [hf.image_eq_image_iff hXE (hYX.trans hXE)] at h'

protected instance instMaximal {P Q} [h : InvariantSetPred.{u, v} P Q] :
    InvariantSetPred.{u,v} (fun M X ↦ Maximal (P M) X) (fun M X ↦ Maximal (Q M) X) where
  subset_ground_left _ _ _ hP := h.subset_ground_left hP.1
  subset_ground_right _ _ _ hP := h.subset_ground_right hP.1
  map_iff' α β M X f hf hXE := by
    simp_rw [maximal_subset_iff, ← h.map_iff' _ hXE, and_congr_right_iff]
    refine fun hPX ↦ ⟨fun h' Y hQY hYX ↦ ?_, fun h' Y hY hYX ↦ ?_⟩
    · obtain ⟨Y, hY, rfl⟩ := subset_image_iff.1 (h.subset_ground_right hQY)
      rw [← h.map_iff' _ hY] at hQY
      rw [hf.image_subset_image_iff hXE hY] at hYX
      rw [h' hQY hYX]
    have hYE := h.subset_ground_left hY
    specialize h' (t := f '' Y) (by rwa [← h.map_iff' _ hYE]) (image_mono hYX)
    rwa [hf.image_eq_image_iff hXE hYE] at h'

instance instIndep : InvariantSetPred Indep Indep where
  subset_ground_left _ _ _ := Indep.subset_ground
  subset_ground_right _ _ _ := Indep.subset_ground
  map_iff' α β M X f hf hX := by rwa [map_image_indep_iff]

instance instCoindep : InvariantSetPred Coindep Coindep :=
  InvariantSetPred.instDual (h := instIndep)

instance instDep : InvariantSetPred Dep Dep := by
  convert InvariantSetPred.instNot (h := instIndep) with α M I <;> rw [dep_iff]

instance instBase : InvariantSetPred IsBase IsBase := by
  convert InvariantSetPred.instMaximal (h := instIndep) with α M B <;> rw [isBase_iff_maximal_indep]

instance instCodep : InvariantSetPred Codep Codep :=
  InvariantSetPred.instDual (h := instDep)

instance instSpanning : InvariantSetPred Spanning Spanning := by
  convert InvariantSetPred.instCompl (P := Coindep) (Q := Coindep) with α M X β N X
  · by_cases hX : X ⊆ M.E
    · rw [spanning_iff_compl_coindep, and_iff_left hX]
    exact iff_of_false (fun h ↦ hX h.subset_ground) <| by simp [hX]
  by_cases hX : X ⊆ N.E
  · rw [spanning_iff_compl_coindep, and_iff_left hX]
  exact iff_of_false (fun h ↦ hX h.subset_ground) <| by simp [hX]

instance instNonspanning : InvariantSetPred Nonspanning Nonspanning := by
  convert InvariantSetPred.instNot (P := Spanning) (Q := Spanning) <;>
  simp [nonspanning_iff]

instance cardLE {k : ℕ∞} : InvariantSetPred (fun M X ↦ X.encard ≤ k ∧ X ⊆ M.E)
    (fun M X ↦ X.encard ≤ k ∧ X ⊆ M.E) where
  subset_ground_left _ _ _ := And.right
  subset_ground_right _ _ _ := And.right
  map_iff' α β M X f hf hXE := by
    rw [(hf.mono hXE).encard_image, map_ground, hf.image_subset_image_iff hXE subset_rfl]

protected lemma map_iff {P Q} [hi : InvariantSetPred P Q] {Y : Set β} (hf : InjOn f M.E) :
    Q (M.map f hf) Y ↔ ∃ X, P M X ∧ Y = f '' X := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨X, hX, rfl⟩ := subset_image_iff.1 <| hi.subset_ground_right h
    rw [← hi.map_iff' _ hX] at h
    exact ⟨X, h, rfl⟩
  rintro ⟨X, hX, rfl⟩
  rwa [← hi.map_iff' _ (hi.subset_ground_left hX)]

protected lemma mapEquiv_iff {P Q} [hi : InvariantSetPred P Q] {Y : Set β} (f : α ≃ β) :
    Q (M.mapEquiv f) Y ↔ P M (f ⁻¹' Y) := by
  simp_rw [mapEquiv_eq_map, InvariantSetPred.map_iff f.injective.injOn (P := P) (Q := Q),
    f.eq_image_iff_symm_image_eq, f.image_symm_eq_preimage]
  grind

protected lemma mapEmbedding_iff {P Q} [hi : InvariantSetPred P Q] {Y : Set β} (f : α ↪ β) :
    Q (M.mapEmbedding f) Y ↔ ∃ X, P M X ∧ Y = f '' X := by
  simp_rw [mapEmbedding, InvariantSetPred.map_iff f.injective.injOn (P := P) (Q := Q)]

protected lemma map {P Q} [hi : InvariantSetPred P Q] {X : Set α} (hX : P M X) (hf : InjOn f M.E) :
    Q (M.map f hf) (f '' X) := by
  rw [InvariantSetPred.map_iff (P := P) (Q := Q)]
  exact ⟨X, hX, rfl⟩

end InvariantSetPred

class InvariantElemPred (P : ∀ {α : Type u}, Matroid α → α → Prop)
    (Q : ∀ {β : Type v}, Matroid β → β → Prop) where
  mem_ground_left : ∀ ⦃α : Type u⦄ ⦃M : Matroid α⦄ ⦃x⦄, P M x → x ∈ M.E
  subset_ground_right : ∀ ⦃β : Type v⦄ ⦃M : Matroid β⦄ ⦃x⦄, Q M x → x ∈ M.E
  map_iff' : ∀ ⦃α : Type u⦄ ⦃β : Type v⦄ ⦃M : Matroid α⦄ ⦃x⦄ ⦃f : α → β⦄ (hf : InjOn f M.E),
      x ∈ M.E → (P M x ↔ Q (M.map f hf) (f x))

class InvariantSetPred₂ (P : ∀ {α : Type u}, Matroid α → Set α → Set α → Prop)
    (Q : ∀ {β : Type v}, Matroid β → Set β → Set β → Prop) where
  subset_ground_left : ∀ ⦃α : Type u⦄ ⦃M : Matroid α⦄ ⦃X Y⦄, P M X Y → X ⊆ M.E ∧ Y ⊆ M.E
  subset_ground_right : ∀ ⦃β : Type v⦄ ⦃M : Matroid β⦄ ⦃X Y⦄, Q M X Y → X ⊆ M.E ∧ Y ⊆ M.E
  map_iff' : ∀ ⦃α : Type u⦄ ⦃β : Type v⦄ ⦃M : Matroid α⦄ ⦃X Y⦄ ⦃f : α → β⦄ (hf : InjOn f M.E),
      X ⊆ M.E → Y ⊆ M.E → (P M X Y ↔ Q (M.map f hf) (f '' X) (f '' Y))

end InvariantSetPred

-- protected class hasSupport (M : Matroid α) (γ : Type u) where
--   supported : γ → Prop

-- instance {M : Matroid α} : M.hasSupport α where
--   supported e := e ∈ M.E

-- instance {M : Matroid α} : M.hasSupport (Set α) where
--   supported X := X ⊆ M.E

-- instance {M : Matroid α} : M.hasSupport (List α) where
--   supported L := {e | e ∈ L} ⊆ M.E

-- instance {M : Matroid α} : M.hasSupport (Finset α) where
--   supported X := (X : Set α) ⊆ M.E

-- -- class hasTransfer (α : Type u) (β : Type v) (γ : Type u) (δ : Type v) where
-- --   apply : (α → β) → γ → δ
-- --   valid : γ → δ → Prop

-- protected class Transfer (γ : Type u → Sort u') (δ : Type v → Sort v') where
--   -- apply : ∀ ⦃α : Type u⦄ ⦃β : Type v⦄, (α → β) → γ α → δ β
--   equiv : ∀ {α : Type u} {β : Type v}, (α → β) → Matroid α → γ α → Matroid β → δ β → Prop

-- instance : Matroid.Transfer (id : Type u → Type u) (id : Type v → Type v) where
--   equiv f M x N y := x ∈ M.E ∧ y ∈ N.E ∧ y = f x

-- instance : Matroid.Transfer Set Set where
--   equiv f M x N y := x ⊆ M.E ∧ y ⊆ N.E ∧ y = f '' x

-- instance : Matroid.Transfer List List where
--   equiv f M L N L' := {e | e ∈ L} ⊆ M.E ∧ {e | e ∈ L'} ⊆ N.E ∧ L' = L.map f

-- instance Transfer.instPred (γ : Type u → Type u) (δ : Type v → Type v) [h : Matroid.Transfer γ δ]
--     Matroid.Transfer (fun α ↦ (γ α) → Prop) (fun β ↦ (δ β) → Prop) where
--   equiv f M x N y := ∀ a b, (h.equiv f M a N b) → (x a ↔ y b)

-- instance Transfer.instFun (γ γ' : Type u → Type u) (δ δ' : Type v → Type v)
--     [h : Matroid.Transfer γ δ] [h' : Matroid.Transfer γ' δ'] :
--     Matroid.Transfer (fun α ↦ (γ α) → (γ' α)) (fun β ↦ (δ β) → (δ' β)) where
--   equiv f M x N y := ∀ a b , h.equiv f M a N b → h'.equiv f M (x a) N (y b)

-- @[simp]
-- lemma Transfer.map_iff_of_setPred (P : Set α → Prop) (Q : Set β → Prop) (M : Matroid α)
--     (f : α → β) (hf : InjOn f M.E) :
--     Transfer.equiv (γ := fun α ↦ (Set α → Prop)) (δ := fun β ↦ (Set β → Prop))
--       f M P (M.map f hf) Q ↔ ∀ X ⊆ M.E, P X ↔ Q (f '' X) := by
--   change (∀ a b, ((_ ∧ _) → _)) ↔ _
--   refine ⟨fun h X hX ↦ h X (f '' X) ⟨hX, by grw [map_ground, hX], rfl⟩, fun h X Y ↦ ?_⟩
--   rintro ⟨hX, -, rfl⟩
--   exact h X hX

-- @[mk_iff]
-- class Invariant {γ : Type u → Sort u'} {δ : Type v → Sort v'} [hT : Matroid.Transfer γ δ]
--     (P : ∀ {α : Type u}, Matroid α → (γ α)) (Q : ∀ {β : Type v}, Matroid β → (δ β)) where
--   equiv_map : ∀ ⦃α : Type u⦄ ⦃β : Type v⦄ ⦃M : Matroid α⦄ ⦃f : α → β⦄ (hf : InjOn f M.E),
--       hT.equiv f M (P M) (M.map f hf) (Q (M.map f hf))

-- instance invariant_indep : Invariant Matroid.Indep.{u} Matroid.Indep.{v} where
--   equiv_map := by
--     simp only [Transfer.map_iff_of_setPred]
--     intro α β M f hf X hXE
--     rw [map_image_indep_iff hXE]


-- protected lemma map_iff {P : ∀ {α : Type u}, Matroid α → Set α → Prop}
--     {Q : ∀ {β : Type v}, Matroid β → Set β → Prop} [hi : Invariant P Q] {Y : Set β}
--     (hf : InjOn f M.E) : Q (M.map f hf) Y ↔ ∃ X, P M X ∧ Y = f '' X := by
--   simp only [invariant_iff, Transfer.map_iff_of_setPred] at hi
--   refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
--   ·


  -- refine ⟨fun h ↦ ?_, ?_⟩
  -- · obtain ⟨X, hX, rfl⟩ := subset_image_iff.1 <| hi.subset_ground_right h
  --   rw [← hi.map_iff' _ hX] at h
  --   exact ⟨X, h, rfl⟩
  -- rintro ⟨X, hX, rfl⟩
  -- rwa [← hi.map_iff' _ (hi.subset_ground_left hX)]



-- instance : Transfer (fun (α : Type u) ↦ (Set α → Prop)) (fun (β : Type v) ↦ (Set β → Prop))
--     infer_instance





  -- eq_apply_of_equiv : ∀ ⦃α : Type u⦄ ⦃β : Type v⦄ ⦃x : γ α⦄ ⦃y : δ β⦄, equiv x y → y = apply f x
  -- valid_left : ∀ ⦃α : Type u⦄, Matroid α → γ α → Prop
  -- valid_right : ∀ ⦃β : Type v⦄, Matroid β → δ β → Prop

-- instance (α : Type u) (β : Type v) : hasTransfer α β (Set α) (Set β) where
--   apply := Set.image

-- instance (α : Type u) (β : Type v) : hasTransfer α β α β where
--   apply := id

-- instance (α : Type u) (β : Type v) : hasTransfer α β (List α) (List β) where
--   apply := List.map


-- protected class hasAction (γ : Type u) (γ' : Type v) where
