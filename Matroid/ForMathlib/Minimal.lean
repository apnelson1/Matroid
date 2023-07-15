import Mathlib.Order.Minimal 
import Mathlib.Order.Bounds.Basic 
import Mathlib.Data.Set.Finite
import Mathlib.Data.Nat.Interval

variable {α : Type _} {r : α → α → Prop} {P : α → Prop}

lemma mem_maximals_iff [IsAntisymm α r] :
    x ∈ maximals r s ↔ x ∈ s ∧ ∀ ⦃y⦄, y ∈ s → r x y → x = y := by
  simp only [maximals, Set.mem_sep_iff, and_congr_right_iff]
  refine' fun _ ↦ ⟨fun h y hys hxy ↦ antisymm hxy (h hys hxy), fun h y hys hxy ↦ _⟩ 
  convert hxy <;> rw [h hys hxy]

lemma mem_maximals_setOf_iff [IsAntisymm α r] : 
    x ∈ maximals r (setOf P) ↔ P x ∧ ∀ ⦃y⦄, P y → r x y → x = y :=
  mem_maximals_iff

lemma mem_minimals_iff [IsAntisymm α r] :
    x ∈ minimals r s ↔ x ∈ s ∧ ∀ ⦃y⦄, y ∈ s → r y x → x = y := by 
  rw [←maximals_swap, @mem_maximals_iff _ _ _ _ (IsAntisymm.swap r)] 

lemma mem_minimals_setOf_iff [IsAntisymm α r] : 
    x ∈ minimals r (setOf P) ↔ P x ∧ ∀ ⦃y⦄, P y → r y x → x = y :=
  mem_minimals_iff

-- lemma maximals_dual [PartialOrder α] (s : Set α) : 
--   @maximals α (· ≤ ·) s = @minimals αᵒᵈ (· ≤ ·) s := rfl 

-- lemma minimals_dual [PartialOrder α] (s : Set α) :
--   @minimals α (· ≤ ·) s = @maximals αᵒᵈ (· ≤ ·) s := rfl

lemma mem_minimals_iff_forall_lt_not_mem' (rlt : α → α → Prop) [IsAntisymm α r] [IsTrans α r] 
    [IsNonstrictStrictOrder α r rlt] :
    x ∈ minimals r s ↔ x ∈ s ∧ ∀ ⦃y⦄, rlt y x → y ∉ s := by
  simp [minimals, right_iff_left_not_left_of r rlt, not_imp_not, imp.swap (a := _ ∈ _)]
  
lemma mem_minimals_iff_forall_ssubset_not_mem (s : Set (Set α)) : 
    x ∈ minimals (· ⊆ ·) s ↔ x ∈ s ∧ ∀ ⦃y⦄, y ⊂ x → y ∉ s := 
  mem_minimals_iff_forall_lt_not_mem' (· ⊂ ·)

lemma mem_minimals_iff_forall_lt_not_mem [PartialOrder α] {s : Set α} : 
    x ∈ minimals (· ≤ ·) s ↔ x ∈ s ∧ ∀ ⦃y⦄, y < x → y ∉ s := 
  mem_minimals_iff_forall_lt_not_mem' (· < ·)

lemma mem_maximals_iff_forall_lt_not_mem' (rlt : α → α → Prop) [IsAntisymm α r] [IsTrans α r] 
    [IsNonstrictStrictOrder α r rlt] :
    x ∈ maximals r s ↔ x ∈ s ∧ ∀ ⦃y⦄, rlt x y → y ∉ s := by
  simp [maximals, right_iff_left_not_left_of r rlt, not_imp_not, imp.swap (a := _ ∈ _)]

lemma mem_maximals_iff_forall_ssubset_not_mem {s : Set (Set α)} : 
    x ∈ maximals (· ⊆ ·) s ↔ x ∈ s ∧ ∀ ⦃y⦄, x ⊂ y → y ∉ s := 
  mem_maximals_iff_forall_lt_not_mem' (· ⊂ ·)

lemma mem_maximals_iff_forall_lt_not_mem [PartialOrder α] {s : Set α} : 
    x ∈ maximals (· ≤ ·) s ↔ x ∈ s ∧ ∀ ⦃y⦄, x < y → y ∉ s := 
  mem_maximals_iff_forall_lt_not_mem' (· < ·)

lemma minimals_eq_minimals_of_subset_of_forall [IsAntisymm α r] [IsTrans α r] (hts : t ⊆ s) 
    (h : ∀ x ∈ s, ∃ y ∈ t, r y x) : minimals r s = minimals r t := by
  refine Set.ext fun a ↦ ⟨fun ⟨has, hmin⟩ ↦ ⟨?_,fun b hbt ↦ hmin (hts hbt)⟩, 
    fun ⟨hat, hmin⟩ ↦ ⟨hts hat, fun b hbs hba ↦ ?_⟩⟩
  · obtain ⟨a', ha', haa'⟩ := h _ has
    rwa [antisymm (hmin (hts ha') haa') haa']
  obtain ⟨b', hb't, hb'b⟩ := h b hbs
  rwa [antisymm (hmin hb't (Trans.trans hb'b hba)) (Trans.trans hb'b hba)]
  
lemma maximals_eq_maximals_of_subset_of_forall [IsAntisymm α r] [IsTrans α r] (hts : t ⊆ s)
    (h : ∀ x ∈ s, ∃ y ∈ t, r x y) : maximals r s = maximals r t := 
  @minimals_eq_minimals_of_subset_of_forall _ _ _ _ (IsAntisymm.swap r) (IsTrans.swap r) hts h
  
section image_preimage

variable {s : β → β → Prop} {f : α → β} {x : Set α} {y : Set β}

open Set 

theorem minimals_image_of_rel_iff_rel (hf : ∀ ⦃a a'⦄, a ∈ x → a' ∈ x → (r a a' ↔ s (f a) (f a'))) :
    minimals s (f '' x) = f '' (minimals r x) := by
  ext a
  simp only [minimals, mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  constructor
  · rintro ⟨⟨a, ha, rfl⟩ , h⟩
    exact ⟨a, ⟨ha, fun y hy hya ↦ (hf ha hy).mpr (h _ hy ((hf hy ha).mp hya))⟩, rfl⟩
  rintro ⟨a,⟨⟨ha,h⟩,rfl⟩⟩ 
  exact ⟨⟨_, ha, rfl⟩, fun y hy hya ↦ (hf ha hy).mp (h hy ((hf hy ha).mpr hya))⟩ 
    
theorem maximals_image_of_rel_iff_rel_on 
    (hf : ∀ ⦃a a'⦄, a ∈ x → a' ∈ x → (r a a' ↔ s (f a) (f a'))) : 
    maximals s (f '' x) = f '' (maximals r x) :=
minimals_image_of_rel_iff_rel (fun _ _ a_1 a_2 ↦ hf a_2 a_1)

theorem RelEmbedding.minimals_image_eq (f : r ↪r s) (x : Set α) : 
    minimals s (f '' x) = f '' (minimals r x) := by
  rw [minimals_image_of_rel_iff_rel]; simp [f.map_rel_iff]

theorem RelEmbedding.maximals_image_eq (f : r ↪r s) (x : Set α) : 
    maximals s (f '' x) = f '' (maximals r x) := 
  (f.swap).minimals_image_eq x

lemma inter_minimals_preimage_inter_eq_of_rel_iff_rel_on
    (hf : ∀ ⦃a a'⦄, a ∈ x → a' ∈ x → (r a a' ↔ s (f a) (f a'))) (y : Set β) :
    x ∩ f ⁻¹' (minimals s ((f '' x) ∩ y)) = minimals r (x ∩ f ⁻¹' y) := by
  ext a
  simp only [minimals, mem_inter_iff, mem_image, and_imp, forall_exists_index, 
    forall_apply_eq_imp_iff₂, preimage_setOf_eq, mem_setOf_eq, mem_preimage]
  exact ⟨fun ⟨hax,⟨_,hay⟩,h2⟩ ↦ ⟨⟨hax, hay⟩, fun a₁ ha₁ ha₁y ha₁a ↦ 
          (hf hax ha₁).mpr (h2 _ ha₁ ha₁y ((hf ha₁ hax).mp ha₁a))⟩ ,
        fun ⟨⟨hax,hay⟩,h⟩ ↦ ⟨hax, ⟨⟨_, hax, rfl⟩, hay⟩, fun a' ha' ha'y hsa' ↦ 
          (hf hax ha').mp (h ha' ha'y ((hf ha' hax).mpr hsa'))⟩⟩ 

lemma inter_preimage_minimals_eq_of_rel_iff_rel_on_of_subset 
    (hf : ∀ ⦃a a'⦄, a ∈ x → a' ∈ x → (r a a' ↔ s (f a) (f a'))) (hy : y ⊆ f '' x) : 
    x ∩ f ⁻¹' (minimals s y) = minimals r (x ∩ f ⁻¹' y) := by
  rw [←inter_eq_self_of_subset_right hy, inter_minimals_preimage_inter_eq_of_rel_iff_rel_on hf, 
    preimage_inter, ←inter_assoc, inter_eq_self_of_subset_left (subset_preimage_image f x)]

lemma RelEmbedding.inter_preimage_minimals_eq (f : r ↪r s) (x : Set α) (y : Set β) : 
    x ∩ f⁻¹' (minimals s ((f '' x) ∩ y)) = minimals r (x ∩ f ⁻¹' y) :=
  inter_minimals_preimage_inter_eq_of_rel_iff_rel_on (by simp [f.map_rel_iff]) y

lemma RelEmbedding.inter_preimage_minimals_eq_of_subset (f : r ↪r s) (h : y ⊆ f '' x) : 
    x ∩ f ⁻¹' (minimals s y) = minimals r (x ∩ f ⁻¹' y) := by
  rw [inter_preimage_minimals_eq_of_rel_iff_rel_on_of_subset _ h]; simp [f.map_rel_iff]

lemma RelEmbedding.minimals_preimage_eq (f : r ↪r s) (y : Set β) :
  minimals r (f ⁻¹' y) = f ⁻¹' minimals s (y ∩ range f) := by
  convert (f.inter_preimage_minimals_eq univ y).symm; simp [univ_inter]; simp [inter_comm]

lemma inter_maximals_preimage_inter_eq_of_rel_iff_rel_on
    (hf : ∀ ⦃a a'⦄, a ∈ x → a' ∈ x → (r a a' ↔ s (f a) (f a'))) (y : Set β) :
    x ∩ f ⁻¹' (maximals s ((f '' x) ∩ y)) = maximals r (x ∩ f ⁻¹' y) := by
  apply inter_minimals_preimage_inter_eq_of_rel_iff_rel_on
  exact fun _ _ a b ↦ hf b a
  
lemma inter_preimage_maximals_eq_of_rel_iff_rel_on_of_subset 
    (hf : ∀ ⦃a a'⦄, a ∈ x → a' ∈ x → (r a a' ↔ s (f a) (f a'))) (hy : y ⊆ f '' x) : 
    x ∩ f ⁻¹' (maximals s y) = maximals r (x ∩ f ⁻¹' y) := by
  apply inter_preimage_minimals_eq_of_rel_iff_rel_on_of_subset _ hy
  exact fun _ _ a b ↦ hf b a

lemma RelEmbedding.inter_preimage_maximals_eq (f : r ↪r s) (x : Set α) (y : Set β) : 
    x ∩ f⁻¹' (maximals s ((f '' x) ∩ y)) = maximals r (x ∩ f ⁻¹' y) :=
  inter_minimals_preimage_inter_eq_of_rel_iff_rel_on (by simp [f.map_rel_iff]) y

lemma RelEmbedding.inter_preimage_maximals_eq_of_subset (f : r ↪r s) (h : y ⊆ f '' x) : 
    x ∩ f ⁻¹' (maximals s y) = maximals r (x ∩ f ⁻¹' y) := by
  rw [inter_preimage_maximals_eq_of_rel_iff_rel_on_of_subset _ h]; simp [f.map_rel_iff]

lemma RelEmbedding.maximals_preimage_eq (f : r ↪r s) (y : Set β) :
  maximals r (f ⁻¹' y) = f ⁻¹' maximals s (y ∩ range f) := by
  convert (f.inter_preimage_maximals_eq univ y).symm; simp [univ_inter]; simp [inter_comm]

end image_preimage
  
    -- minimals r (f ⁻¹' x) = f ⁻¹' (minimals s x) := by
  


-- theorem foo {s : Set (Set α)} {f : α → β} (hf : )


open Set

variable [PartialOrder α] {a b : α}

@[simp] theorem maximals_Iic (a : α) : maximals (· ≤ ·) (Iic a) = {a} :=
  Set.ext fun _ ↦ ⟨fun h ↦ h.1.antisymm (h.2 rfl.le h.1),
    fun h ↦ ⟨h.trans_le rfl.le, fun _ hba _ ↦ le_trans hba h.symm.le⟩⟩

@[simp] theorem minimals_Ici (a : α) : minimals (· ≤ ·) (Ici a) = {a} :=
  maximals_Iic (α := αᵒᵈ) a

theorem maximals_Icc (hab : a ≤ b) : maximals (· ≤ ·) (Icc a b) = {b} :=
  Set.ext fun x ↦ ⟨fun h ↦ h.1.2.antisymm (h.2 ⟨hab, rfl.le⟩ h.1.2),
    fun (h : x = b) ↦ ⟨⟨hab.trans_eq h.symm, h.le⟩, fun _ hy _ ↦ hy.2.trans_eq h.symm⟩⟩

theorem minimals_Icc (hab : a ≤ b) : minimals (· ≤ ·) (Icc a b) = {a} := by
  simp_rw [Icc, and_comm (a := (a ≤ _))]; exact maximals_Icc (α := αᵒᵈ) hab

theorem maximals_Ioc (hab : a < b) : maximals (· ≤ ·) (Ioc a b) = {b} :=
  Set.ext fun x ↦ ⟨fun h ↦ h.1.2.antisymm (h.2 ⟨hab, rfl.le⟩ h.1.2),
    fun (h : x = b) ↦ ⟨⟨hab.trans_eq h.symm, h.le⟩, fun _ hy _ ↦ hy.2.trans_eq h.symm⟩⟩

theorem minimals_Ico (hab : a < b) : minimals (· ≤ ·) (Ico a b) = {a} := by
  simp_rw [Ico, and_comm (a := _ ≤ _)]; exact maximals_Ioc (α := αᵒᵈ) hab



/-- This seems a strict improvement over the nonprimed version in mathlib - only the image needs to 
be finite, not the set itself.  -/
lemma Finite.exists_maximal_wrt' {α β : Type _} [PartialOrder β] (f : α → β) (s : Set α) 
    (h : (f '' s).Finite) (h₀ : s.Nonempty) : 
  (∃ a ∈ s, ∀ (a' : α), a' ∈ s → f a ≤ f a' → f a = f a') := by
  obtain  ⟨_ ,⟨a,ha,rfl⟩, hmax⟩ := Finite.exists_maximal_wrt id (f '' s) h (h₀.image f)
  exact ⟨a, ha, fun a' ha' hf ↦ hmax _ (mem_image_of_mem f ha') hf⟩


-- lemma finite_iff_bddAbove {α : Type _} [SemilatticeSup α] [LocallyFiniteOrder α] [OrderBot α] 
--     {s : Set α} : s.Finite ↔ BddAbove s :=
-- ⟨fun h ↦ ⟨h.toFinset.sup id, fun x hx ↦ Finset.le_sup (f := id) (by simpa : x ∈ h.toFinset)⟩,
--   fun ⟨m, hm⟩ ↦ (finite_Icc ⊥ m).subset (fun x hx ↦ ⟨bot_le, hm hx⟩)⟩
  
-- lemma finite_iff_bddBelow {α : Type _} [SemilatticeInf α] [LocallyFiniteOrder α] [OrderTop α]
--     {s : Set α} : s.Finite ↔ ∃ a, ∀ x ∈ s, a ≤ x :=
--   finite_iff_bddAbove (α := αᵒᵈ)

-- lemma finite_iff_bddBelow_bddAbove {α : Type _} [Nonempty α] [Lattice α] [LocallyFiniteOrder α] 
--     {s : Set α} : s.Finite ↔ BddBelow s ∧ BddAbove s := by
--   obtain (rfl | hs) := s.eq_empty_or_nonempty; simp
--   refine' ⟨fun h ↦ _, fun ⟨⟨a,ha⟩,⟨b,hb⟩⟩ ↦ (finite_Icc a b).subset (fun x hx ↦ ⟨ha hx,hb hx⟩ )⟩
--   obtain ⟨s,rfl⟩ := h.exists_finset_coe
--   exact ⟨⟨s.inf' (by simpa using hs) id, fun x hx ↦ Finset.inf'_le id (by simpa using hx)⟩, 
--     ⟨s.sup' (by simpa using hs) id, fun x hx ↦ Finset.le_sup' id (by simpa using hx)⟩⟩