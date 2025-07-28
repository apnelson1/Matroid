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

@[simp]
lemma inf_rel (P Q : Partition (Set α)) : ⇑(P ⊓ Q) = ⇑P ⊓ ⇑Q := by
  change ⇑(ofRel _) = _
  rw [rel_ofRel_eq]

@[simp]
lemma sSup_rel (S : Set (Partition (Set α))) : ⇑(sSup S) = TransClosure (sSup <| (⇑) '' S) := by
  change ⇑(ofRel _) = _
  rw [rel_ofRel_eq]

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

@[simp]
lemma iInf_rel {ι : Type*} (G : ι → Partition (Set α)) :
    ⇑(⨅ i, G i) = ⨅ i, ⇑(G i) := by
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

-- Compl does not exist
