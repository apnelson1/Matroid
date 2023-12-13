import Mathlib.Logic.Equiv.PartialEquiv
import Mathlib.Data.Set.Card

open Set Function PartialEquiv

variable {α β : Type*}

section ofSetEquiv

theorem Finite.exists_PartialEquiv_of_encard_eq [Nonempty α] [Nonempty β] {s : Set α} {t : Set β}
    (hfin : s.Finite) (h : s.encard = t.encard) :
    ∃ (e : PartialEquiv α β), e.source = s ∧ e.target = t := by

  obtain ⟨f, hf⟩ := hfin.exists_bijOn_of_encard_eq h
  exact ⟨hf.toPartialEquiv, rfl, hf.toPartialEquiv_target⟩

@[simps] protected noncomputable def PartialEquiv.ofSetEquiv [Nonempty α] [Nonempty β] {s : Set α}
    {t : Set β} [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)] (e : s ≃ t) : PartialEquiv α β where
  toFun x := if h : x ∈ s then e ⟨x,h⟩ else Classical.arbitrary β
  invFun y := if h : y ∈ t then e.symm ⟨y,h⟩ else Classical.arbitrary α
  source := s
  target := t
  map_source' _ h := by simp [h]
  map_target' _ h := by simp [h]
  left_inv' _ h := by simp [h]
  right_inv' _ h := by simp [h]

@[simp] theorem PartialEquiv.ofSetEquiv_apply_mem [Nonempty α] [Nonempty β] {s : Set α} {t : Set β}
    [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)] (e : s ≃ t) {x : α} (hx : x ∈ s):
    PartialEquiv.ofSetEquiv e x = e ⟨x,hx⟩ := by
  simp [hx]

end ofSetEquiv

variable [DecidableEq α] [DecidableEq β] {φ φ' : PartialEquiv α β} {a : α} {b : β}

/-- Extend the source/target of a `PartialEquiv` by setting `e a = b`. -/
@[simps] protected def PartialEquiv.insert (e : PartialEquiv α β) (ha : a ∉ e.source)
    (hb : b ∉ e.target) : PartialEquiv α β where
  toFun := update e a b
  invFun := update e.symm b a
  source := insert a e.source
  target := insert b e.target
  map_source' := by
    rintro x (rfl | hx)
    · rw [update_same]
      apply mem_insert
    rw [update_apply, if_neg (by rintro rfl; exact ha hx)]
    exact mem_insert_of_mem _ <| e.map_source hx
  map_target' := by
    rintro x (rfl | hx)
    · rw [update_same]
      apply mem_insert
    rw [update_apply, if_neg (by rintro rfl; exact hb hx)]
    exact mem_insert_of_mem _ <| e.map_target hx
  left_inv' := by
    rintro x (rfl | hx)
    · rw [update_same, update_same]
    rw [update_apply, update_apply, if_neg (show x ≠ a from fun h ↦ ha <| h ▸ hx),
      if_neg (by rintro rfl; exact hb <| e.map_source hx), e.left_inv hx]
  right_inv' := by
    rintro x (rfl | hx)
    · rw [update_same, update_same]
    rw [update_apply, update_apply, if_neg (show x ≠ b from fun h ↦ hb <| h ▸ hx),
      if_neg (by rintro rfl; exact ha <| e.map_target hx), e.right_inv hx]

theorem PartialEquiv.insert_apply_mem (e : PartialEquiv α β) (ha : a ∉ e.source) (hb : b ∉ e.target)
    {i : α} (hi : i ∈ e.source) : (e.insert ha hb) i = e i := by
  rw [insert_apply, update_apply, if_neg]
  exact fun h ↦ ha <| h ▸ hi

@[simp] theorem insert_symm (e : PartialEquiv α β) (ha : a ∉ e.source) (hb : b ∉ e.target) :
    (e.insert ha hb).symm = e.symm.insert hb ha := by
  ext <;> simp

theorem PartialEquiv.insert_apply_symm_mem (e : PartialEquiv α β) (ha : a ∉ e.source)
    (hb : b ∉ e.target) {j : β} (hj : j ∈ e.target) : (e.insert ha hb).symm j = e.symm j := by
  rw [insert_symm, insert_apply_mem]
  exact hj

/-- `φ ≤ φ'` means that the source and target of `φ` are contained in those of `φ'`, and that
  they agree on their common domain.  -/
instance {α β : Type*} : Preorder (PartialEquiv α β) where
  le φ φ' := φ.source ⊆ φ'.source ∧ ∀ {i}, i ∈ φ.source → φ' i = φ i
  le_refl φ := by simp [Subset.rfl]
  le_trans φ₁ φ₂ φ₃ h₁₂ h₂₃ := ⟨h₁₂.1.trans h₂₃.1, fun hi ↦ by rw [h₂₃.2 (h₁₂.1 hi), h₁₂.2 hi]⟩

theorem PartialEquiv.eq_of_mem_source (h : φ ≤ φ') (ha : a ∈ φ.source) : φ' a = φ a :=
  h.2 ha

theorem PartialEquiv.source_subset (h : φ ≤ φ') : φ.source ⊆ φ'.source :=
  h.1

theorem PartialEquiv.target_subset (h : φ ≤ φ') : φ.target ⊆ φ'.target := by
  rw [← φ.image_source_eq_target, ← φ'.image_source_eq_target]
  rintro _ ⟨x,hx,rfl⟩
  rw [← PartialEquiv.eq_of_mem_source h hx]
  exact mem_image_of_mem _ (source_subset h hx)

theorem PartialEquiv.symm_le_symm_of_le (h : φ ≤ φ') : φ.symm ≤ φ'.symm := by
  refine ⟨target_subset h, fun {i} hi ↦ φ'.injOn ?_ ?_ ?_⟩
  · exact φ'.map_target (target_subset h hi)
  · exact h.1 <| φ.map_target hi
  rw [eq_comm, h.2 (φ.map_target hi), φ.right_inv hi, φ'.right_inv (target_subset h hi)]

theorem PartialEquiv.symm_le_symm_iff_le : φ.symm ≤ φ'.symm ↔ φ ≤ φ' :=
  ⟨symm_le_symm_of_le, fun h ↦ by simpa using symm_le_symm_of_le h⟩

theorem PartialEquiv.lt_insert (ha : a ∉ φ.source) (hb : b ∉ φ.target) : φ < φ.insert ha hb := by
  refine ⟨⟨subset_insert _ _, fun hi ↦ φ.insert_apply_mem _ _ hi⟩, ?_⟩
  simp only [insert_source, not_and]
  exact fun h ↦ (ha <| h (Or.inl rfl)).elim
