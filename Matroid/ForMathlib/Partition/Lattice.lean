import Matroid.ForMathlib.Partition.Set

open Set Function Relation

variable {α β ι ι' : Type*} {r : α → α → Prop} {f : ι → α} {x y z : α}

namespace Partition

section Set

variable {s t u : Set α} {S T : Set (Set α)} {P Q : Partition (Set α)}


instance {S : Set (Partition (Set α))} : IsSymm α (sSup <| (⇑) '' S) where
  symm := sSup_symmtric (fun _ ⟨_, _, heq⟩ => heq ▸ inferInstance)

instance {S : Set (Partition (Set α))} : IsSymm α (sInf <| (⇑) '' S) where
  symm := sInf_symmtric (fun _ ⟨_, _, heq⟩ => heq ▸ inferInstance)

instance {S : Set (Partition (Set α))} : IsTrans α (sInf <| (⇑) '' S) where
  trans := sInf_transitive (fun _ ⟨_, _, heq⟩ => heq ▸ inferInstance)

instance : CompleteLattice (Partition (Set α)) where
  sup P Q := ofRel <| TransClosure (P ⊔ Q)
  le_sup_left P Q := by
    rw [← rel_le_iff_le, rel_ofRel_eq]
    exact le_trans le_sup_left (TransClosure.le_closure _)
  le_sup_right P Q := by
    rw [← rel_le_iff_le, rel_ofRel_eq]
    exact le_trans le_sup_right (TransClosure.le_closure _)
  sup_le r s t hrt hst := by
    rw [← rel_le_iff_le] at hrt hst
    rw [← rel_le_iff_le, rel_ofRel_eq]
    exact ClosureOperator.closure_min (sup_le hrt hst) t.rel_transitive
  inf P Q := ofRel <| P ⊓ Q
  inf_le_left P Q := by
    rw [← rel_le_iff_le, rel_ofRel_eq]
    exact inf_le_left
  inf_le_right P Q := by
    rw [← rel_le_iff_le, rel_ofRel_eq]
    exact inf_le_right
  le_inf P Q R hPQR hPQR' := by
    rw [← rel_le_iff_le] at hPQR hPQR'
    rw [← rel_le_iff_le, rel_ofRel_eq]
    exact le_inf hPQR hPQR'
  sSup s := ofRel (TransClosure (sSup <| (⇑) '' s))
  le_sSup S P hPS := by
    rw [← rel_le_iff_le, rel_ofRel_eq]
    exact le_trans (le_sSup <| mem_image_of_mem (⇑) hPS) (TransClosure.le_closure _)
  sSup_le S r hrS := by
    rw [← rel_le_iff_le, rel_ofRel_eq]
    refine TransClosure.closure_min (sSup_le ?_) r.rel_transitive
    rintro s ⟨s', hs', rfl⟩
    exact rel_le_iff_le.mpr (hrS s' hs')
  sInf S := ofRel (sInf <| (⇑) '' S)
  le_sInf S r hrS := by
    rw [← rel_le_iff_le, rel_ofRel_eq]
    refine le_sInf <| ?_
    rintro s ⟨s', hs', rfl⟩
    exact rel_le_iff_le.mpr <| hrS s' hs'
  sInf_le S r hrS := by
    rw [← rel_le_iff_le, rel_ofRel_eq]
    exact sInf_le <| mem_image_of_mem (⇑) hrS
  le_top r := by simp
  bot_le r := by simp

@[simp]
lemma sup_rel (P Q : Partition (Set α)) : ⇑(P ⊔ Q) = TransClosure (⇑P ⊔ ⇑Q) := by
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

lemma Agree.sup_rel_right_of_mem (hPQ : P.Agree Q) (hx : x ∈ Q.supp) : ⇑(P ⊔ Q) x y ↔ ⇑Q x y := by
  rw [hPQ.sup_rel]
  refine ⟨fun h => ?_, fun h => by aesop⟩
  obtain (hP | hQ) := h
  · exact hPQ.rel_of_left_of_mem hx hP
  exact hQ

@[simp]
lemma inf_rel (P Q : Partition (Set α)) : ⇑(P ⊓ Q) = ⇑P ⊓ ⇑Q := by
  change ⇑(ofRel _) = _
  rw [rel_ofRel_eq]

@[simp]
lemma sSup_rel (S : Set (Partition (Set α))) : ⇑(sSup S) = TransClosure (sSup <| (⇑) '' S) := by
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
  change ⇑(ofRel _) = _
  rw [rel_ofRel_eq]

@[simp]
lemma iSup_rel {ι : Type*} (G : ι → Partition (Set α)) :
    ⇑(⨆ i, G i) = TransClosure (⨆ i, ⇑(G i)) := by
  change ⇑(ofRel _) = _
  rw [rel_ofRel_eq, iSup, ← range_comp]
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
  change ⇑(ofRel _) = _
  rw [rel_ofRel_eq, iInf, ← range_comp]
  rfl

@[simp]
lemma sSup_supp (S : Set (Partition (Set α))) : (sSup S).supp = ⋃ P ∈ S, P.supp := by
  simp_rw [← domain_rel]
  ext x
  simp only [sSup_rel, mem_domain_iff, mem_iUnion, exists_prop]
  refine ⟨fun ⟨y, hy⟩ ↦ ?_, ?_⟩
  · induction hy with
  | single h =>
    simp only [sSup_apply, iSup_apply, iSup_Prop_eq, Subtype.exists, mem_image, exists_prop,
      exists_exists_and_eq_and] at h
    obtain ⟨r, hrS, hr⟩ := h
    exact ⟨r, hrS, _, hr⟩
  | tail _ _ IH => exact IH
  · rintro ⟨P, hPS, y, hPxy⟩
    refine ⟨y, Relation.TransGen.single ?_⟩
    simp only [sSup_apply, iSup_apply, iSup_Prop_eq, Subtype.exists, mem_image, exists_prop,
      exists_exists_and_eq_and]
    exact ⟨P, hPS, hPxy⟩

@[simp]
lemma iSup_supp {ι : Type*} (G : ι → Partition (Set α)) : (⨆ i, G i).supp = ⋃ i, (G i).supp := by
  simp [iSup]

@[simp]
lemma sup_supp (P Q : Partition (Set α)) : (P ⊔ Q).supp = P.supp ∪ Q.supp := by
  rw [← sSup_pair, sSup_supp]
  simp

@[simp]
lemma sInf_supp (S : Set (Partition (Set α))) : (sInf S).supp = ⋂ P ∈ S, P.supp := by
  simp_rw [← domain_rel]
  ext x
  simp only [sInf_rel, mem_domain_iff, sInf_apply, iInf_apply, iInf_Prop_eq, Subtype.forall,
    mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, domain_rel, mem_iInter]
  exact ⟨fun ⟨y, hy⟩ P hPS ↦ (hy P hPS).left_mem,
    fun h => ⟨x, fun P hPS => rel_self_of_mem_supp (h P hPS)⟩⟩

@[simp]
lemma iInf_supp {ι : Type*} (G : ι → Partition (Set α)) : (⨅ i, G i).supp = ⋂ i, (G i).supp := by
  simp [iInf]

@[simp]
lemma inf_supp (P Q : Partition (Set α)) : (P ⊓ Q).supp = P.supp ∩ Q.supp := by
  rw [← sInf_pair, sInf_supp]
  simp

@[simp]
lemma Agree.subset_sup_left (hPQ : P.Agree Q) : P ⊆ P ⊔ Q := by
  rw [subset_iff_rel, hPQ.sup_rel]
  simp only [Pi.sup_apply, sup_Prop_eq, iff_self_or]
  exact fun _ _ ↦ rel_of_right_of_mem hPQ

@[simp]
lemma Agree.subset_sup_right (hPQ : P.Agree Q) : Q ⊆ P ⊔ Q := by
  rw [sup_comm]
  exact hPQ.symm.subset_sup_left

@[simp]
lemma subset_sSup_of_agree {S : Set (Partition (Set α))} (hS : S.Pairwise Agree) (hP : P ∈ S) :
    P ⊆ sSup S := by
  rw [subset_iff_rel, sSup_rel]
  refine fun x y hxP ↦ ⟨fun hxy => TransGen.single ?_, fun hxy => ?_⟩
  · simp only [sSup_apply, iSup_apply, iSup_Prop_eq, Subtype.exists, mem_image, exists_prop,
    exists_exists_and_eq_and]
    use P
  induction hxy with
  | single hxy =>
    obtain ⟨Q, hQS, hQ⟩ := by simpa using hxy
    exact (hS.of_refl hP hQS).trans_left (rel_self_of_mem_supp hxP) hQ
  | tail _ hxy IH =>
    obtain ⟨Q, hQS, hQ⟩ := by simpa using hxy
    exact (hS.of_refl hP hQS).trans_left IH hQ

@[simp]
lemma subset_iSup_of_agree {ι : Type*} {P : ι → Partition (Set α)} (hP : Pairwise (Agree on P))
    (i : ι) : P i ⊆ ⨆ i, P i :=
  subset_sSup_of_agree hP.range_pairwise <| mem_range_self i

@[simp]
lemma Agree.inf_subset_left (hPQ : P.Agree Q) : P ⊓ Q ⊆ P := by
  rw [agree_iff_rel] at hPQ
  rw [subset_iff_rel, inf_rel]
  refine fun x y hxP ↦ ⟨(·.1), fun hxy => ⟨hxy, ?_⟩⟩
  rw [inf_supp] at hxP
  rwa [← hPQ x _ hxP.1 hxP.2]

@[simp]
lemma Agree.inf_subset_right (hPQ : P.Agree Q) : P ⊓ Q ⊆ Q := by
  rw [inf_comm]
  exact hPQ.symm.inf_subset_left

@[simp]
lemma sInf_subset_of_agree {S : Set (Partition (Set α))} (hS : S.Pairwise Agree) (hP : P ∈ S) :
    sInf S ⊆ P := by
  rw [subset_iff_rel]
  simp only [sInf_supp, mem_iInter, sInf_rel, sInf_apply, iInf_apply, iInf_Prop_eq, Subtype.forall,
    mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  exact fun x y hxP ↦ ⟨fun hxy => hxy P hP,
    fun hxy Q hQS => (hS.of_refl hQS hP).trans_left (rel_self_of_mem_supp (hxP Q hQS)) hxy⟩

@[simp]
lemma iInf_subset_of_agree {ι : Type*} {P : ι → Partition (Set α)} (hP : Pairwise (Agree on P))
    (i : ι) : ⨅ i, P i ⊆ P i :=
  sInf_subset_of_agree hP.range_pairwise <| mem_range_self i

@[simp]
lemma Agree.sup_parts (hPQ : P.Agree Q) : (P ⊔ Q) = P.parts ∪ Q.parts := by
  refine subset_antisymm ?_ <| union_subset hPQ.subset_sup_left hPQ.subset_sup_right
  rintro s ⟨x, hx, rfl⟩
  simp only [transClosure_codomain, mem_codomain_iff, Pi.sup_apply, sup_Prop_eq, mem_union,
    mem_parts, SetLike.mem_coe] at hx ⊢
  obtain ⟨y, hPyx | hQyx⟩ := hx
  · left
    convert partOf_mem hPyx.right_mem using 1
    ext z
    rw [mem_fiber_iff, mem_partOf_iff, ← Partition.sup_rel, rel_comm, rel_comm (x := z)]
    exact hPQ.sup_rel_left_of_mem hPyx.right_mem
  right
  convert partOf_mem hQyx.right_mem using 1
  ext z
  rw [mem_fiber_iff, mem_partOf_iff, ← Partition.sup_rel, rel_comm, rel_comm (x := z)]
  exact hPQ.sup_rel_right_of_mem hQyx.right_mem

@[simp]
lemma Agree.mem_sup_iff (hPQ : P.Agree Q) : s ∈ P ⊔ Q ↔ s ∈ P ∨ s ∈ Q := by
  change s ∈ (P ⊔ Q).parts ↔ _
  rw [mem_parts, hPQ.sup_parts]
  simp

@[simp]
lemma sSup_parts_of_agree {S : Set (Partition (Set α))} (hS : S.Pairwise Agree) :
    sSup S = ⋃ P ∈ S, P.parts := by
  refine subset_antisymm ?_ ?_; swap
  · simp only [iUnion_subset_iff]
    exact fun _ => subset_sSup_of_agree hS
  rintro s ⟨x, hx, rfl⟩
  simp only [transClosure_codomain, mem_codomain_iff, sSup_apply, iSup_apply, iSup_Prop_eq,
    Subtype.exists, mem_image, exists_prop, exists_exists_and_eq_and, mem_iUnion, mem_parts,
    SetLike.mem_coe] at hx ⊢
  obtain ⟨y, P, hPS, hPyx⟩ := hx
  use P, hPS
  convert partOf_mem hPyx.right_mem using 1
  ext z
  rw [mem_fiber_iff, mem_partOf_iff, ← Partition.sSup_rel, rel_comm, rel_comm (x := z)]
  exact sSup_rel_of_agree_of_mem hS hPS hPyx.right_mem

@[simp]
lemma mem_sSup_iff_of_agree {S : Set (Partition (Set α))} (hS : S.Pairwise Agree) :
    s ∈ sSup S ↔ ∃ P ∈ S, s ∈ P := by
  change s ∈ (sSup S).parts ↔ ∃ P ∈ S, s ∈ P
  rw [mem_parts, sSup_parts_of_agree hS]
  simp

@[simp]
lemma iSup_parts_of_agree {ι : Type*} {S : ι → Partition (Set α)} (hS : Pairwise (Agree on S)) :
    ⨆ i, S i = ⋃ i, (S i).parts := by
  rw [iSup, sSup_parts_of_agree hS.range_pairwise]
  simp

@[simp]
lemma mem_iSup_iff_of_agree {ι : Type*} {S : ι → Partition (Set α)} (hS : Pairwise (Agree on S)) :
    s ∈ ⨆ i, S i ↔ ∃ i, s ∈ (S i) := by
  change s ∈ (⨆ i, S i).parts ↔ ∃ i, s ∈ (S i)
  rw [mem_parts, iSup_parts_of_agree hS]
  simp

@[simp]
lemma Agree.inf_parts (hPQ : P.Agree Q) : P ⊓ Q = P.parts ∩ Q.parts := by
  refine subset_antisymm (subset_inter hPQ.inf_subset_left hPQ.inf_subset_right) ?_
  rintro s ⟨hsP, hsQ⟩
  simp only [mem_parts, SetLike.mem_coe] at hsP hsQ ⊢
  obtain ⟨x, hxs, rfl⟩ := exists_partOf_iff_mem.mp hsP
  obtain ⟨_, H⟩ := partOf_mem_iff_rel_iff.mp hsQ
  simp_rw [rel_comm (x := x)] at H
  use x, ?_
  · ext y
    simp [H]
  simp only [mem_codomain_iff, Pi.inf_apply, ← H, min_self]
  exact ⟨x, rel_self_of_mem_supp hxs⟩

@[simp]
lemma Agree.mem_inf_iff (hPQ : P.Agree Q) : s ∈ P ⊓ Q ↔ s ∈ P ∧ s ∈ Q := by
  change s ∈ (P ⊓ Q).parts ↔ _
  rw [mem_parts, hPQ.inf_parts]
  simp

@[simp]
lemma sInf_parts_of_agree {S : Set (Partition (Set α))} (hS : S.Pairwise Agree) (hS' : S.Nonempty) :
    sInf S = ⋂ P ∈ S, P.parts := by
  refine subset_antisymm ?_ ?_
  · simp only [subset_iInter_iff]
    exact fun _ => sInf_subset_of_agree hS
  rintro s hs
  rw [SetLike.mem_coe, exists_partOf_iff_mem]
  simp only [mem_iInter, mem_parts, SetLike.mem_coe, sInf, ofRel_supp, mem_domain_iff, iInf_apply,
    iInf_Prop_eq, Subtype.forall, mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂] at hs ⊢
  have hs' := hs hS'.some hS'.some_mem
  obtain ⟨x, hx⟩ := nonempty_of_mem hs'
  use x, ?_
  · ext y
    simp only [mem_partOf_iff, rel_ofRel_eq, iInf_apply, iInf_Prop_eq, Subtype.forall, mem_image,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨t, ht, hyt, hxt⟩ := h hS'.some hS'.some_mem
      obtain rfl := eq_of_mem_of_mem ht hs' hxt hx
      exact hyt
    rintro P hPS
    use s, hs P hPS
  use x
  exact fun P hPS => rel_of_mem_of_mem (hs P hPS) hx hx

@[simp]
lemma mem_sInf_iff_of_agree {S : Set (Partition (Set α))} (hS : S.Pairwise Agree)
    (hS' : S.Nonempty) : s ∈ sInf S ↔ ∀ P ∈ S, s ∈ P := by
  change s ∈ (sInf S).parts ↔ ∀ P ∈ S, s ∈ P
  rw [mem_parts, sInf_parts_of_agree hS hS']
  simp

@[simp]
lemma iInf_parts_of_agree {ι : Type*} [Nonempty ι] {S : ι → Partition (Set α)}
    (hS : Pairwise (Agree on S)) : ⨅ i, S i = ⋂ i, (S i).parts := by
  rw [iInf, sInf_parts_of_agree hS.range_pairwise (range_nonempty S)]
  simp

@[simp]
lemma mem_iInf_iff_of_agree {ι : Type*} [Nonempty ι] {S : ι → Partition (Set α)}
    (hS : Pairwise (Agree on S)) : s ∈ ⨅ i, S i ↔ ∀ i, s ∈ (S i) := by
  change s ∈ (⨅ i, S i).parts ↔ ∀ i, s ∈ (S i)
  rw [mem_parts, iInf_parts_of_agree hS]
  simp

@[simp]
lemma sSup_atomic {S : Set (Partition (Set α))} (hS : ∀ P ∈ S, P.Atomic) :
    (sSup S).Atomic := by
  simp_rw [atomic_iff_rel_le_eq] at hS ⊢
  rw [sSup_rel, ← transClosure_eq]
  exact TransClosure.monotone <| by simpa

@[simp]
lemma iSup_atomic {ι : Type*} {S : ι → Partition (Set α)} (hS : ∀ i, (S i).Atomic) :
    (⨆ i, S i).Atomic :=
  sSup_atomic <| fun _ ⟨i, heq⟩ => heq ▸ hS i

@[simp]
lemma sup_atomic (P Q : Partition (Set α)) (hP : P.Atomic) (hQ : Q.Atomic) :
    (P ⊔ Q).Atomic := by
  rw [← sSup_pair]
  exact sSup_atomic <| by simp [hP, hQ]

@[simp]
lemma sSup_discrete (S : Set (Set α)) :
    sSup (Partition.discrete '' S) = Partition.discrete (⋃₀ S) :=
  eq_discrete_of (sSup_atomic <| by simp) <| by simp [sUnion_eq_biUnion]

@[simp]
lemma iSup_discrete {ι : Type*} (S : ι → (Set α)) :
  (⨆ i, Partition.discrete (S i)) = Partition.discrete (⋃ i, S i) :=
  eq_discrete_of (iSup_atomic <| by simp) <| by simp

@[simp]
lemma sup_discrete (s t : Set α) :
    Partition.discrete s ⊔ Partition.discrete t = Partition.discrete (s ∪ t) := by
  simp_rw [← sSup_pair, ← image_pair, sSup_discrete, sUnion_pair]

@[simp↓]
lemma sSup_induce_of_agree {S : Set (Partition (Set α))} (hS : S.Pairwise Agree) (s : Set α) :
    induce (sSup S) s = sSup ((Partition.induce · s) '' S) := by
  ext x y
  simp only [sSup_rel, induce_apply, hS, ↓sSup_rel_of_agree, sSup_apply, iSup_apply, iSup_Prop_eq,
    Subtype.exists, mem_image, exists_prop, exists_exists_and_eq_and]
  refine ⟨fun h => TransGen.single (by aesop), fun h => ?_⟩
  induction h with
  | single hxy => aesop
  | tail h1 h2 IH =>
    expose_names
    obtain ⟨hxs, hbs, P, hPS, hPxb⟩ := IH
    obtain ⟨Q, hQS, hbs, hcs, hQbc⟩ := by simpa using h2
    exact ⟨hxs, hcs, P, hPS, (hS.of_refl hPS hQS).trans_left hPxb hQbc⟩

@[simp↓]
lemma iSup_induce_of_agree {ι : Type*} {S : ι → Partition (Set α)} (hS : Pairwise (Agree on S))
    (s : Set α) : (⨆ i, S i).induce s = ⨆ i, (S i).induce s := by
  convert sSup_induce_of_agree hS.range_pairwise s
  rw [← range_comp]
  rfl

@[simp↓]
lemma Agree.induce_sup (hPQ : P.Agree Q) (s : Set α) :
    (P ⊔ Q).induce s = P.induce s ⊔ Q.induce s := by
  rw [← sSup_pair, sSup_induce_of_agree, image_pair, sSup_pair]
  exact pairwise_pair_of_symm hPQ

@[simp↓]
lemma sInf_induce_of_nonempty {S : Set (Partition (Set α))} (hS' : S.Nonempty) (s : Set α) :
    induce (sInf S) s = sInf ((Partition.induce · s) '' S) := by
  ext x y
  obtain ⟨P, hPS⟩ := hS'
  simp +contextual only [induce_apply, sInf_rel, sInf_apply, iInf_apply, iInf_Prop_eq,
    Subtype.forall, mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    exists_exists_and_eq_and, iff_def, and_self, implies_true, and_true, true_and]
  intro h
  specialize h P hPS
  tauto

@[simp↓]
lemma iInf_induce_of_nonempty [Nonempty ι] {S : ι → Partition (Set α)} (s : Set α) :
    (⨅ i, S i).induce s = ⨅ i, (S i).induce s := by
  convert sInf_induce_of_nonempty (range_nonempty S) s
  rw [← range_comp]
  rfl

@[simp↓]
lemma induce_inf (P Q : Partition (Set α)) (s : Set α) :
    (P ⊓ Q).induce s = P.induce s ⊓ Q.induce s := by
  rw [← sInf_pair, sInf_induce_of_nonempty (by simp), image_pair, sInf_pair]

-- Compl does not exist
