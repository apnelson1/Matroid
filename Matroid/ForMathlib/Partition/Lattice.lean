import Matroid.ForMathlib.Partition.Constructor

open Set Function Relation

variable {α β ι ι' : Type*} {r : α → α → Prop} {f : ι → α} {a b c x y z : α} {i j : ι} {A B : Set α}


lemma not_disjoint_iff_inf_ne_bot [SemilatticeInf α] [OrderBot α] (a b : α) :
    ¬ Disjoint a b ↔ a ⊓ b ≠ ⊥ := by
  rw [not_iff_not]
  exact disjoint_iff

@[simp]
lemma sSup_sSup_image [CompleteLattice α] {S : Set (Set α)} : sSup (sSup '' S) = sSup (⋃₀ S) := by
  rw [sSup_sUnion, ← sSup_image]

namespace Partition

section Frame

variable [Order.Frame α] {s t u : α} {S T : Set α} {P Q : Partition α} {Ps : Set (Partition α)}
  {Pι : ι → Partition α}

@[simp]
lemma sSup_supp : (sSup Ps).supp = ⨆ P ∈ Ps, P.supp := by
  change (sSup' Ps).supp = _
  simp only [supp, sSup', sSup_sSup_image, sUnion_disjParts, sSup_diff_singleton_bot]
  rw [← iSup_image, ← sSup_sUnion, sUnion_image]

@[simp]
lemma iSup_supp (Pι : ι → Partition α) : (⨆ i, Pι i).supp = ⨆ i, (Pι i).supp := by
  conv_lhs => simp only [iSup]
  rw [sSup_supp]
  exact iSup_range

@[simp]
lemma iSup_supp_prop (P : Partition α) {p : Prop} : (⨆ _ : p, P).supp = ⨆ _ : p, P.supp := by
  conv_lhs => simp only [iSup]
  rw [sSup_supp]
  exact iSup_range

@[simp]
lemma sup_supp (P Q : Partition α) : (P ⊔ Q).supp = P.supp ⊔ Q.supp := by
  rw [← sSup_pair, sSup_supp]
  exact iSup_pair

-- @[simp]
-- lemma sInf_supp (S : Set (Partition α)) : (sInf S).supp = ⨅ P ∈ S, P.supp := by
--   change (sInf' S).supp = _
--   simp only [supp, sInf', ofIndependent_parts, sSup_diff_singleton_bot]




--   simp_rw [← domain_rel]
--   ext x
--   simp only [sInf_rel, mem_domain_iff, sInf_apply, iInf_apply, iInf_Prop_eq, Subtype.forall,
--     mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, domain_rel, mem_iInter]
--   exact ⟨fun ⟨y, hy⟩ P hPS ↦ (hy P hPS).left_mem,
--     fun h => ⟨x, fun P hPS => rel_self_of_mem_supp (h P hPS)⟩⟩

-- @[simp]
-- lemma iInf_supp (G : ι → Partition (Set α)) : (⨅ i, G i).supp = ⋂ i, (G i).supp := by
--   simp [iInf]

@[simp]
lemma inf_supp (P Q : Partition α) : (P ⊓ Q).supp = P.supp ⊓ Q.supp := by
  change (Partition.bind _ _ _).supp = _
  simp only [supp, Partition.bind, induce_parts, sSup_iUnion, sSup_inf_sSup, biSup_prod,
    sSup_diff_singleton_bot, sSup_image, iSup_subtype]
  rfl

@[simp]
lemma sSup_singleton (P : Partition α) : sSup {P} = P := by
  ext x
  simp

@[simp]
protected lemma iSup_const [Nonempty ι] (P : Partition α) : (⨆ _ : ι, P) = P := by
  ext x
  simp

@[simp]
lemma sup_self (P : Partition α) : P ⊔ P = P := by
  ext x
  simp

@[simp]
lemma sInf_singleton (P : Partition α) : sInf {P} = P := by
  ext x
  simp

@[simp]
protected lemma iInf_const [Nonempty ι] (P : Partition α) : (⨅ _ : ι, P) = P := by
  ext x
  simp

@[simp]
lemma inf_self (P : Partition α) : P ⊓ P = P := by
  ext x
  simp

@[simp]
lemma sSup_insert_bot (Ps : Set (Partition α)) : sSup (insert ⊥ Ps) = sSup Ps := by
  simp

@[simp]
lemma sSup_diff_singleton_bot (Ps : Set (Partition α)) : sSup (Ps \ {⊥}) = sSup Ps := by
  rw [← sSup_insert_bot, insert_diff_singleton, sSup_insert_bot]

lemma mem_sSup_of_mem (hPs : Ps.Nonempty) (ha : ∀ P ∈ Ps, a ∈ P) : a ∈ sSup Ps := by
  obtain ⟨P0, hP0⟩ := hPs
  change _ ∈ sSup' _
  simp only [← mem_parts, sSup'_parts, mem_image]
  use {a}, ?_, by simp
  simp only [mem_parts, singleton_mem_disjParts_iff, mem_iUnion, exists_prop]
  refine fun b => ⟨fun ⟨hba, ⟨Pb, hPbPs, hbPb⟩, _⟩ => Pb.eq_of_not_disjoint hbPb (ha Pb hPbPs) hba,
    ?_⟩
  rintro rfl
  simp only [disjoint_self, P0.ne_bot_of_mem (ha P0 hP0), not_false_eq_true, and_self, true_and]
  use P0, hP0, ha P0 hP0

lemma mem_iSup_of_mem [Nonempty ι] (hP : ∀ i, a ∈ Pι i) :
    a ∈ (⨆ i, Pι i) := by
  apply mem_sSup_of_mem (by use Pι (Classical.arbitrary ι), (Classical.arbitrary ι))
  rintro P ⟨i, rfl⟩
  exact hP i

lemma mem_sup_of_mem (hP : a ∈ P) (hQ : a ∈ Q) : a ∈ P ⊔ Q := by
  rw [← sSup_pair]
  exact mem_sSup_of_mem (by use P, mem_insert P {Q}) (by simp [hP, hQ])

lemma mem_sInf_of_mem (hPs : Ps.Nonempty) (hP : ∀ P ∈ Ps, a ∈ P) : a ∈ sInf Ps := by
  have : Nonempty Ps := hPs.to_subtype
  obtain ⟨P0, hP0S⟩ := hPs
  change _ ∈ sInf' _
  simp only [sInf', mem_ofIndependent_iff, mem_diff, mem_image, mem_pi, mem_univ, mem_parts,
    forall_const, Subtype.forall, mem_singleton_iff, P0.ne_bot_of_mem (hP P0 hP0S),
    not_false_eq_true, and_true]
  use fun _ ↦ a, hP, iInf_const

lemma mem_iInf_of_mem [Nonempty ι] (hP : ∀ i, a ∈ Pι i) : a ∈ (⨅ i, Pι i) := by
  apply mem_sInf_of_mem (by use Pι (Classical.arbitrary ι), (Classical.arbitrary ι))
  rintro P₁ ⟨i, rfl⟩
  exact hP i

lemma mem_inf_of_mem (hP : a ∈ P) (hQ : a ∈ Q) : a ∈ P ⊓ Q := by
  rw [← sInf_pair]
  exact mem_sInf_of_mem (by use P, mem_insert P {Q}) (by simp [hP, hQ])

@[simp]
lemma Agree.subset_sup_left (hPQ : P.Agree Q) : P ⊆ P ⊔ Q := by
  rintro p hP
  change p ∈ sSup' _
  simp only [sSup', mem_insert_iff, mem_singleton_iff, iUnion_iUnion_eq_or_left,
    iUnion_iUnion_eq_left, ← mem_parts, mem_image]
  use {p}, ?_, by simp
  rw [mem_parts, singleton_mem_disjParts_iff]
  rintro b
  simp only [mem_union, mem_parts, hP, true_or, and_true]
  obtain ⟨R, hPR, hQR⟩ := hPQ
  refine ⟨fun ⟨hbp, hb⟩ => R.eq_of_not_disjoint (hb.elim (hPR ·) (hQR ·)) (hPR hP) hbp, ?_⟩
  rintro rfl
  simp [mem_parts.mp hP, P.ne_bot_of_mem hP]

@[simp]
lemma Agree.subset_sup_right (hPQ : P.Agree Q) : Q ⊆ P ⊔ Q := by
  rw [sup_comm]
  exact hPQ.symm.subset_sup_left

@[simp]
lemma subset_sSup_of_agree (hPs : Ps.Pairwise Agree) (hP : P ∈ Ps) : P ⊆ sSup Ps := by
  rintro a haP
  simp only [mem_parts, mem_sSup_iff]
  use {a}, ?_, by simp
  rw [singleton_mem_disjParts_iff]
  rintro b
  simp only [mem_iUnion, mem_parts, exists_prop]
  refine ⟨fun ⟨hba, ⟨Pb, hPb, hbPb⟩, Pa, hPa, haPa⟩ => hPs.of_refl hPb hPa
  |>.eq_of_not_disjoint hbPb haPa hba, ?_⟩
  rintro rfl
  simp only [disjoint_self, P.ne_bot_of_mem haP, not_false_eq_true, and_self, true_and]
  use P, hP, haP

@[simp]
lemma subset_iSup_of_agree (hPι : Pairwise (Agree on Pι))
    (i : ι) : Pι i ⊆ ⨆ i, Pι i :=
  subset_sSup_of_agree hPι.range_pairwise <| mem_range_self i

@[simp]
lemma subset_biSup_of_agree {S : Set ι}
    (hS : S.Pairwise (Agree on Pι)) (hi : i ∈ S) : Pι i ⊆ ⨆ i ∈ S, Pι i := by
  rw [← sSup_image]
  refine subset_sSup_of_agree ?_ (by use i)
  rwa [pairwise_image_of_refl]

@[simp]
lemma Agree.inf_subset_left (hPQ : P.Agree Q) : P ⊓ Q ⊆ P := by
  rintro a ha
  obtain ⟨⟨b, hbP, c, hcQ, rfl⟩, habot⟩ := by simpa using ha
  obtain rfl := hPQ.eq_of_not_disjoint hbP hcQ <| disjoint_iff.not.mpr habot
  simpa

@[simp]
lemma Agree.inf_subset_right (hPQ : P.Agree Q) : P ⊓ Q ⊆ Q := by
  rw [inf_comm]
  exact hPQ.symm.inf_subset_left

@[simp]
lemma sInf_subset_of_agree (hPs : Ps.Pairwise Agree) (hP : P ∈ Ps) : sInf Ps ⊆ P := by
  have : Nonempty Ps := by use P
  rintro a ha
  obtain ⟨⟨f, hf, rfl⟩, habot⟩ := by simpa using ha
  suffices f = fun _ ↦ f ⟨P, hP⟩ by
    rw [this, iInf_const]
    exact hf P hP
  ext Q
  exact (hPs.of_refl Q.prop hP).eq_of_not_disjoint (hf Q Q.prop) (hf P hP)
  <| disjoint_iff.not.mpr <| ne_bot_of_le_ne_bot habot <| le_inf (iInf_le f _) (iInf_le f _)

@[simp]
lemma iInf_subset_of_agree {ι : Type*} {P : ι → Partition α} (hP : Pairwise (Agree on P))
    (i : ι) : ⨅ i, P i ⊆ P i :=
  sInf_subset_of_agree hP.range_pairwise <| mem_range_self i

@[simp]
lemma Agree.sup_parts (hPQ : P.Agree Q) : (P ⊔ Q).parts = P.parts ∪ Q.parts := by
  refine subset_antisymm ?_ <| union_subset hPQ.subset_sup_left hPQ.subset_sup_right
  rintro _ ⟨x, hx, rfl⟩
  rw [disjParts_eq_sUnion_of_agree <| pairwise_pair_of_symm hPQ] at hx
  simp only [Set.singleton, setOf_eq_eq_singleton, mem_insert_iff, mem_singleton_iff,
    iUnion_iUnion_eq_or_left, iUnion_iUnion_eq_left, mem_image, mem_union, mem_parts] at hx ⊢
  obtain ⟨y, h, rfl⟩ := hx
  simpa

lemma sup_parts_eq_union_iff_agree (P Q : Partition α) :
    (P ⊔ Q).parts = P.parts ∪ Q.parts ↔ P.Agree Q :=
  ⟨fun h => ⟨P ⊔ Q, (show P.parts ⊆ (P ⊔ Q).parts from h ▸ subset_union_left),
    (show Q.parts ⊆ (P ⊔ Q).parts from h ▸ subset_union_right)⟩, fun h => h.sup_parts⟩

@[simp]
lemma Agree.mem_sup_iff (hPQ : P.Agree Q) : s ∈ P ⊔ Q ↔ s ∈ P ∨ s ∈ Q := by
  change s ∈ (P ⊔ Q).parts ↔ _
  rw [hPQ.sup_parts]
  simp

@[simp]
lemma sSup_parts_of_agree (hPs : Ps.Pairwise Agree) : (sSup Ps).parts = ⋃ P ∈ Ps, P.parts := by
  refine subset_antisymm ?_ ?_; swap
  · simp only [iUnion_subset_iff]
    exact fun _ => subset_sSup_of_agree hPs
  rintro s ⟨x, hx, rfl⟩
  rw [disjParts_eq_sUnion_of_agree hPs] at hx
  simp only [Set.singleton, setOf_eq_eq_singleton, mem_image, mem_iUnion, mem_parts,
    exists_prop] at hx
  obtain ⟨y, h, rfl⟩ := hx
  simpa

@[simp]
lemma mem_sSup_iff_of_agree (hPs : Ps.Pairwise Agree) : s ∈ sSup Ps ↔ ∃ P ∈ Ps, s ∈ P := by
  change s ∈ (sSup Ps).parts ↔ ∃ P ∈ Ps, s ∈ P
  rw [sSup_parts_of_agree hPs]
  simp

@[simp]
lemma iSup_parts_of_agree (hPι : Pairwise (Agree on Pι)) :
    (⨆ i, Pι i).parts = ⋃ i, (Pι i).parts := by
  rw [iSup, sSup_parts_of_agree hPι.range_pairwise]
  simp

@[simp]
lemma mem_iSup_iff_of_agree (hPι : Pairwise (Agree on Pι)) :
    s ∈ ⨆ i, Pι i ↔ ∃ i, s ∈ (Pι i) := by
  change s ∈ (⨆ i, Pι i).parts ↔ ∃ i, s ∈ (Pι i)
  rw [iSup_parts_of_agree hPι]
  simp

@[simp]
lemma biSup_parts_of_agree {S : Set ι} (hS : S.Pairwise (Agree on Pι)) :
    (⨆ i ∈ S, Pι i).parts = ⋃ i ∈ S, (Pι i).parts := by
  rw [← sSup_image, sSup_parts_of_agree, biUnion_image]
  rwa [pairwise_image_of_refl]

@[simp]
lemma mem_biSup_iff_of_agree {S : Set ι} (hS : S.Pairwise (Agree on Pι)) :
    s ∈ ⨆ i ∈ S, Pι i ↔ ∃ i ∈ S, s ∈ (Pι i) := by
  change s ∈ (⨆ i ∈ S, Pι i).parts ↔ ∃ i ∈ S, s ∈ (Pι i)
  rw [biSup_parts_of_agree hS]
  simp

@[simp]
lemma Agree.inf_parts (hPQ : P.Agree Q) : (P ⊓ Q).parts = P.parts ∩ Q.parts := by
  refine subset_antisymm (subset_inter hPQ.inf_subset_left hPQ.inf_subset_right)
    fun a ⟨haP, haQ⟩ ↦ ?_
  simp only [mem_parts, mem_inf_iff, ne_eq, P.ne_bot_of_mem haP, not_false_eq_true, and_true]
  use a, haP, a, haQ, Std.min_self

@[simp]
lemma Agree.mem_inf_iff (hPQ : P.Agree Q) : s ∈ P ⊓ Q ↔ s ∈ P ∧ s ∈ Q := by
  change s ∈ (P ⊓ Q).parts ↔ _
  rw [hPQ.inf_parts]
  simp

@[simp]
lemma sInf_parts_of_agree (hPs : Ps.Pairwise Agree) (hPsne : Ps.Nonempty) :
    (sInf Ps).parts = ⋂ P ∈ Ps, P.parts := by
  refine subset_antisymm ?_ ?_
  · simp only [subset_iInter_iff]
    exact fun _ => sInf_subset_of_agree hPs
  rintro s hs
  have : Nonempty Ps := hPsne.to_subtype
  obtain ⟨P, hP⟩ := hPsne
  simp only [mem_iInter, mem_parts] at hs
  simp only [mem_parts, mem_sInf_iff, Subtype.forall, ne_eq, P.ne_bot_of_mem (hs P hP),
    not_false_eq_true, and_true]
  use fun _ ↦ s, hs, iInf_const

@[simp]
lemma mem_sInf_iff_of_agree (hPs : Ps.Pairwise Agree) (hPsne : Ps.Nonempty) :
    s ∈ sInf Ps ↔ ∀ P ∈ Ps, s ∈ P := by
  change s ∈ (sInf Ps).parts ↔ ∀ P ∈ Ps, s ∈ P
  rw [sInf_parts_of_agree hPs hPsne]
  simp

@[simp]
lemma iInf_parts_of_agree [Nonempty ι] {Pι : ι → Partition α}
    (hPι : Pairwise (Agree on Pι)) : (⨅ i, Pι i).parts = ⋂ i, (Pι i).parts := by
  rw [iInf, sInf_parts_of_agree hPι.range_pairwise (range_nonempty Pι)]
  simp

@[simp]
lemma mem_iInf_iff_of_agree [Nonempty ι] {Pι : ι → Partition α}
    (hPι : Pairwise (Agree on Pι)) : s ∈ ⨅ i, Pι i ↔ ∀ i, s ∈ (Pι i) := by
  change s ∈ (⨅ i, Pι i).parts ↔ ∀ i, s ∈ (Pι i)
  rw [iInf_parts_of_agree hPι]
  simp

-- @[simp]
-- lemma sSup_atomic (hPs : ∀ P ∈ Ps, P.Atomic) : (sSup Ps).Atomic := by
--   rintro a ha
--   simp only [mem_sSup_iff] at ha
--   simp_rw [atomic_iff_rel_le_eq] at hPs ⊢
--   rw [sSup_rel, ← transClosure_eq]
--   exact TransClosure.monotone <| by simpa

-- @[simp]
-- lemma iSup_atomic {ι : Type*} {S : ι → Partition (Set α)} (hS : ∀ i, (S i).Atomic) :
--     (⨆ i, S i).Atomic :=
--   sSup_atomic <| fun _ ⟨i, heq⟩ => heq ▸ hS i

-- @[simp]
-- lemma sup_atomic (P Q : Partition (Set α)) (hP : P.Atomic) (hQ : Q.Atomic) :
--     (P ⊔ Q).Atomic := by
--   rw [← sSup_pair]
--   exact sSup_atomic <| by simp [hP, hQ]

-- @[simp]
-- lemma sSup_discrete (S : Set (Set α)) :
--     sSup (Partition.discrete '' S) = Partition.discrete (⋃₀ S) :=
--   eq_discrete_of (sSup_atomic <| by simp) <| by simp [sUnion_eq_biUnion]

-- @[simp]
-- lemma iSup_discrete {ι : Type*} (S : ι → (Set α)) :
--   (⨆ i, Partition.discrete (S i)) = Partition.discrete (⋃ i, S i) :=
--   eq_discrete_of (iSup_atomic <| by simp) <| by simp

-- @[simp]
-- lemma sup_discrete (s t : Set α) :
--     Partition.discrete s ⊔ Partition.discrete t = Partition.discrete (s ∪ t) := by
--   simp_rw [← sSup_pair, ← image_pair, sSup_discrete, sUnion_pair]

-- @[simp↓]
-- lemma sSup_induce_of_agree (hPs : Ps.Pairwise Agree) (a : α) :
--     (sSup Ps).induce a = sSup ((Partition.induce · a) '' Ps) := by
--   ext x
--   rw [← mem_parts, induce_parts, sSup_parts_of_agree hPs, ← mem_parts, sSup_parts_of_agree]
--   simp only [mem_diff, mem_image, mem_iUnion, mem_parts, exists_prop, mem_singleton_iff,
--     iUnion_exists, biUnion_and', iUnion_iUnion_eq_right, induce_parts]
--   tauto
--   rintro - ⟨P, hP, rfl⟩ - ⟨Q, hQ, rfl⟩ _
--   have := hPs.of_refl hP hQ
--   sorry

-- @[simp↓]
-- lemma iSup_induce_of_agree {ι : Type*} {S : ι → Partition (Set α)} (hS : Pairwise (Agree on S))
--     (s : Set α) : (⨆ i, S i).induce s = ⨆ i, (S i).induce s := by
--   convert sSup_induce_of_agree hS.range_pairwise s
--   rw [← range_comp]
--   rfl

-- @[simp↓]
-- lemma Agree.induce_sup (hPQ : P.Agree Q) (s : Set α) :
--     (P ⊔ Q).induce s = P.induce s ⊔ Q.induce s := by
--   rw [← sSup_pair, sSup_induce_of_agree, image_pair, sSup_pair]
--   exact pairwise_pair_of_symm hPQ

-- @[simp↓]
-- lemma sInf_induce_of_nonempty {S : Set (Partition (Set α))} (hS' : S.Nonempty) (s : Set α) :
--     Partition.induce (sInf S) s = sInf ((Partition.induce · s) '' S) := by
--   ext x y
--   obtain ⟨P, hPS⟩ := hS'
--   simp +contextual only [induce_apply, sInf_rel, sInf_apply, iInf_apply, iInf_Prop_eq,
--     Subtype.forall, mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
--     exists_exists_and_eq_and, iff_def, and_self, implies_true, and_true, true_and]
--   intro h
--   specialize h P hPS
--   tauto

-- @[simp↓]
-- lemma iInf_induce_of_nonempty [Nonempty ι] {S : ι → Partition (Set α)} (s : Set α) :
--     (⨅ i, S i).induce s = ⨅ i, (S i).induce s := by
--   convert sInf_induce_of_nonempty (range_nonempty S) s
--   rw [← range_comp]
--   rfl

-- @[simp↓]
-- lemma induce_inf (P Q : Partition (Set α)) (s : Set α) :
--     (P ⊓ Q).induce s = P.induce s ⊓ Q.induce s := by
--   rw [← sInf_pair, sInf_induce_of_nonempty (by simp), image_pair, sInf_pair]

-- @[simp]
-- lemma induce_sInter (P : Partition (Set α)) {S : Set (Set α)} (hS : S.Nonempty) :
--     P.induce (⋂₀ S) = sInf (P.induce '' S) := by
--   ext x y
--   simp +contextual only [induce_apply, mem_sInter, sInf_rel, sInf_apply, iInf_apply,
--iInf_Prop_eq,
--     Subtype.forall, mem_image, exists_exists_and_eq_and, forall_exists_index, and_imp,
--     forall_apply_eq_imp_iff₂, iff_def, and_self, implies_true, true_and]
--   exact fun h => (h hS.some hS.some_mem).2.2

-- @[simp]
-- lemma induce_iInter (P : Partition (Set α)) [Nonempty ι] {S : ι → Set α} :
--     P.induce (⋂ i, S i) = ⨅ i, P.induce (S i) := by
--   change P.induce (⋂₀ range S) = _
--   rw [induce_sInter P (range_nonempty S), sInf_image, iInf_range]

-- @[simp]
-- lemma induce_inter (P : Partition (Set α)) (s t : Set α) :
--     P.induce (s ∩ t) = P.induce s ⊓ P.induce t := by
--   rw [← sInf_pair, ← sInter_pair, induce_sInter P (by simp), image_pair]

lemma powerset_sSup_pairwise_agree (hPs : Ps.Pairwise Agree) :
    ((sSup) '' Ps.powerset).Pairwise Agree := by
  rintro P ⟨p, hp, rfl⟩ Q ⟨q, hq, rfl⟩ hPQ
  rw [mem_powerset_iff] at hp hq
  use sSup Ps, ?_ <;> change Partition.parts _ ⊆ _
  <;> rw [sSup_parts_of_agree hPs, sSup_parts_of_agree (hPs.mono <| by assumption)]
  <;> exact biUnion_mono (by assumption) fun x a ⦃a⦄ a ↦ a

lemma sSup_agree_sSup_of_subset {Ps Ps₁ Ps₂ : Set (Partition α)} (hPs : Ps.Pairwise Agree)
    (hPs₁ : Ps₁ ⊆ Ps) (hPs₂ : Ps₂ ⊆ Ps) : (sSup Ps₁).Agree (sSup Ps₂) := by
  apply (powerset_sSup_pairwise_agree hPs).of_refl <;> exact mem_image_of_mem sSup (by assumption)

def relOrderEmb : Partition (Set α) ↪o (α → α → Prop) where
  toFun := (⇑)
  inj' _ _ := rel_inj_iff.mp
  map_rel_iff' := rel_le_iff_le

def suppBoundedLatticeHom : BoundedLatticeHom (Partition α) α where
  toFun := supp
  map_sup' := sup_supp
  map_inf' := inf_supp
  map_top' := supp_top
  map_bot' := supp_bot

lemma supp_disjoint_of_disjoint (h : Disjoint P Q) : Disjoint P.supp Q.supp :=
  h.map suppBoundedLatticeHom

end Frame

section Set

variable {P Q R : Partition (Set α)} {Ps : Set (Partition (Set α))} {Pι : ι → Partition (Set α)}

lemma disjoint_iff_rel_disjoint (P Q : Partition (Set α)) : Disjoint P Q ↔ Disjoint (⇑P) (⇑Q) := by
  refine ⟨fun h p hpP hpQ a b hpab => ?_, fun h => h.of_orderEmbedding relOrderEmb⟩
  simp only [Pi.bot_apply, «Prop».bot_eq_false]
  exact (supp_disjoint_of_disjoint h).notMem_of_mem_left (hpP a b hpab).left_mem
    (hpQ a b hpab).left_mem

--
instance {S : Set (Partition (Set α))} : Std.Symm α (sSup <| (⇑) '' S) where
  symm := sSup_symmtric (fun _ ⟨_, _, heq⟩ => heq ▸ inferInstance)

instance {S : Set (Partition (Set α))} : Std.Symm α (sInf <| (⇑) '' S) where
  symm := sInf_symmtric (fun _ ⟨_, _, heq⟩ => heq ▸ inferInstance)

instance {S : Set (Partition (Set α))} : IsTrans α (sInf <| (⇑) '' S) where
  trans := sInf_transitive (fun _ ⟨_, _, heq⟩ => heq ▸ inferInstance)

def relSup (P Q : Partition (Set α)) : Partition (Set α) := ofRel <| TransClosure (P ⊔ Q)

lemma le_relSup_left : P ≤ relSup P Q := by
  rw [← rel_le_iff_le, relSup, rel_ofRel_eq]
  exact le_trans le_sup_left (TransClosure.le_closure _)

lemma le_relSup_right : Q ≤ relSup P Q := by
  rw [← rel_le_iff_le, relSup, rel_ofRel_eq]
  exact le_trans le_sup_right (TransClosure.le_closure _)

lemma relSup_le (hPR : P ≤ R) (hQR : Q ≤ R) : relSup P Q ≤ R := by
  rw [← rel_le_iff_le] at hPR hQR
  rw [← rel_le_iff_le, relSup, rel_ofRel_eq]
  exact ClosureOperator.closure_min (sup_le hPR hQR) R.rel_transitive

lemma relSup_eq_sup (P Q : Partition (Set α)) : relSup P Q = P ⊔ Q :=
  le_antisymm (relSup_le le_sup_left le_sup_right) (sup_le le_relSup_left le_relSup_right)

def relsSup (Ps : Set (Partition (Set α))) : Partition (Set α) :=
  ofRel <| TransClosure (sSup <| (⇑) '' Ps)

lemma le_relsSup (hP : P ∈ Ps) : P ≤ relsSup Ps := by
  rw [← rel_le_iff_le, relsSup, rel_ofRel_eq]
  exact le_trans (le_sSup <| mem_image_of_mem (⇑) hP) (TransClosure.le_closure _)

lemma relsSup_le (hPs : ∀ P ∈ Ps, P ≤ Q) : relsSup Ps ≤ Q := by
  rw [← rel_le_iff_le, relsSup, rel_ofRel_eq]
  refine TransClosure.closure_min (sSup_le ?_) Q.rel_transitive
  rintro s ⟨s', hs', rfl⟩
  exact rel_le_iff_le.mpr (hPs s' hs')

lemma relsSup_eq_sSup : relsSup Ps = sSup Ps :=
  le_antisymm (relsSup_le (fun _ => le_sSup)) (sSup_le (fun _ => le_relsSup))

def relsInf (Ps : Set (Partition (Set α))) : Partition (Set α) :=
  ofRel <| sInf <| (⇑) '' Ps

lemma le_relsInf (hP : ∀ P ∈ Ps, Q ≤ P) : Q ≤ relsInf Ps := by
  rw [← rel_le_iff_le, relsInf, rel_ofRel_eq]
  refine le_sInf <| ?_
  rintro s ⟨s', hs', rfl⟩
  exact rel_le_iff_le.mpr <| hP s' hs'

lemma relsInf_le (hP : P ∈ Ps) : relsInf Ps ≤ P := by
  rw [← rel_le_iff_le, relsInf, rel_ofRel_eq]
  exact sInf_le (mem_image_of_mem (⇑) hP)

lemma relsInf_eq_sInf : relsInf Ps = sInf Ps :=
  le_antisymm (le_sInf (fun _ => relsInf_le)) (le_relsInf (fun _ => sInf_le))

@[simp]
lemma sup_rel (P Q : Partition (Set α)) : ⇑(P ⊔ Q) = TransClosure (⇑P ⊔ ⇑Q) := by
  rw [← relSup_eq_sup]
  change ⇑(ofRel _) = _
  rw [rel_ofRel_eq]

@[simp↓]
lemma Agree.sup_rel (hPQ : P.Agree Q) : ⇑(P ⊔ Q) = ⇑P ⊔ ⇑Q := by
  ext x y
  rw [Partition.sup_rel]
  refine ⟨fun h => ?_, TransGen.single⟩
  induction h with
  | single hxy => exact hxy
  | tail _ hxy IH => exact hPQ.sup_rel_trans IH hxy

lemma Agree.sup_rel_left_of_mem (hPQ : P.Agree Q) (hx : x ∈ P.supp) : ⇑(P ⊔ Q) x y ↔ ⇑P x y := by
  rw [hPQ.sup_rel]
  refine ⟨fun h => ?_, fun h => by aesop⟩
  obtain (hP | hQ) := h
  · exact hP
  exact hPQ.rel_of_right_of_mem hx hQ

lemma Agree.partOf_left_mem (hPQ : P.Agree Q) (hx : x ∈ P.supp) : P.partOf x ∈ P ⊔ Q := by
  rw [← relSup_eq_sup]
  simp only [partOf_mem_iff_rel_iff, hx, hPQ.sup_rel_left_of_mem hx, relSup_eq_sup, implies_true,
    and_self]

lemma Agree.sup_rel_right_of_mem (hPQ : P.Agree Q) (hx : x ∈ Q.supp) : ⇑(P ⊔ Q) x y ↔ ⇑Q x y := by
  rw [hPQ.sup_rel]
  refine ⟨fun h => ?_, fun h => by aesop⟩
  obtain (hP | hQ) := h
  · exact hPQ.rel_of_left_of_mem hx hP
  exact hQ

lemma Agree.partOf_right_mem (hPQ : P.Agree Q) (hx : x ∈ Q.supp) : Q.partOf x ∈ P ⊔ Q := by
  rw [sup_comm]
  exact hPQ.symm.partOf_left_mem hx

@[simp]
lemma inf_rel (P Q : Partition (Set α)) : ⇑(P ⊓ Q) = ⇑P ⊓ ⇑Q := by
  ext x y
  simp only [Pi.inf_apply, inf_Prop_eq]
  refine ⟨fun h => ?_, fun ⟨⟨p, hpP, hxp, hyp⟩, ⟨q, hqQ, hxq, hyq⟩⟩ => ?_⟩
  · obtain ⟨a, haPQ, hxa, hya⟩ := h
    obtain ⟨⟨p, hpP, q, hqQ, rfl⟩, hne⟩ := (by simpa using haPQ); clear haPQ
    exact ⟨⟨p, hpP, hxa.1, hya.1⟩, ⟨q, hqQ, hxa.2, hya.2⟩⟩
  use p ⊓ q, ?_, ?_, ?_ <;> simp_all only [inf_eq_inter, mem_inf_iff, bot_eq_empty, and_self,
    mem_inter_iff]
  use ⟨p, hpP, q, hqQ, rfl⟩
  rw [← nonempty_iff_ne_empty, inter_nonempty_iff_exists_left]
  use x

@[simp]
lemma sSup_rel (S : Set (Partition (Set α))) : ⇑(sSup S) = TransClosure (sSup <| (⇑) '' S) := by
  rw [← relsSup_eq_sSup]
  change ⇑(ofRel _) = _
  rw [rel_ofRel_eq]

@[simp↓]
lemma sSup_rel_of_agree {S : Set (Partition (Set α))} (hS : S.Pairwise Agree) :
    ⇑(sSup S) = (sSup <| (⇑) '' S) := by
  ext x y
  rw [Partition.sSup_rel]
  refine ⟨fun h => ?_, TransGen.single⟩
  induction h with
  | single hxy => exact hxy
  | tail _ hxy IH =>
    simp only [sSup_apply, iSup_apply, iSup_Prop_eq, Subtype.exists, mem_image, exists_prop,
      exists_exists_and_eq_and] at hxy IH ⊢
    obtain ⟨Q, hQS, hQ⟩ := hxy
    obtain ⟨P, hPS, hP⟩ := IH
    exact ⟨P, hPS, (hS.of_refl hPS hQS).trans_left hP hQ⟩

lemma sSup_rel_of_agree_of_mem {S : Set (Partition (Set α))} (hS : S.Pairwise Agree) (hP : P ∈ S)
    (hx : x ∈ P.supp) : ⇑(sSup S) x y ↔ ⇑P x y := by
  rw [sSup_rel_of_agree hS]
  simp only [sSup_apply, iSup_apply, iSup_Prop_eq, Subtype.exists, mem_image, exists_prop,
    exists_exists_and_eq_and]
  exact ⟨fun ⟨Q, hQ, hQx⟩ => (hS.of_refl hP hQ).rel_of_right_of_mem hx hQx, fun h => ⟨P, hP, h⟩⟩

@[simp]
lemma sInf_rel (S : Set (Partition (Set α))) : ⇑(sInf S) = sInf ((⇑) '' S) := by
  rw [← relsInf_eq_sInf]
  change ⇑(ofRel _) = _
  rw [rel_ofRel_eq]

@[simp]
lemma iSup_rel {ι : Type*} (G : ι → Partition (Set α)) :
    ⇑(⨆ i, G i) = TransClosure (⨆ i, ⇑(G i)) := by
  change ⇑(sSup (range G)) = _
  rw [← relsSup_eq_sSup, relsSup, rel_ofRel_eq, iSup, ← range_comp]
  rfl

@[simp↓]
lemma iSup_rel_of_agree {ι : Type*} {S : ι → Partition (Set α)} (hS : Pairwise (Agree on S)) :
    ⇑(⨆ i, S i) = (⨆ i, ⇑(S i)) := by
  convert sSup_rel_of_agree hS.range_pairwise
  rw [← range_comp]
  rfl

lemma iSup_rel_of_agree_of_mem {ι : Type*} {S : ι → Partition (Set α)} (hS : Pairwise (Agree on S))
    {i : ι} (hx : x ∈ (S i).supp) : ⇑(⨆ i, S i) x y ↔ ⇑(S i) x y := by
  rw [iSup_rel_of_agree hS]
  simp only [iSup_apply, iSup_Prop_eq]
  exact ⟨fun ⟨j, hj⟩ => (hS.of_refl i j).rel_of_right_of_mem hx hj, fun h => ⟨i, h⟩⟩

@[simp]
lemma iInf_rel {ι : Type*} (G : ι → Partition (Set α)) : ⇑(⨅ i, G i) = ⨅ i, ⇑(G i) := by
  change ⇑(sInf (range G)) = _
  rw [← relsInf_eq_sInf, relsInf, rel_ofRel_eq, iInf, ← range_comp]
  rfl
