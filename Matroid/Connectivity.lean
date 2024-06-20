import Matroid.Minor.Rank
import Matroid.Modular
import Matroid.ForMathlib.Data.Set.Finite

open Set

variable {α : Type*} {M : Matroid α}

namespace Matroid

section Connected

variable {C K : Set α} {e f g : α}

def ConnectedTo (M : Matroid α) (e f : α) := (e = f ∧ e ∈ M.E) ∨ ∃ C, M.Circuit C ∧ e ∈ C ∧ f ∈ C

lemma ConnectedTo.exists_circuit_of_ne (h : M.ConnectedTo e f) (hne : e ≠ f) :
    ∃ C, M.Circuit C ∧ e ∈ C ∧ f ∈ C := by
  simpa [ConnectedTo, hne] using h

lemma Circuit.mem_connectedTo_mem (hC : M.Circuit C) (heC : e ∈ C) (hfC : f ∈ C) :
    M.ConnectedTo e f :=
  .inr ⟨C, hC, heC, hfC⟩

lemma connectedTo_self (he : e ∈ M.E) : M.ConnectedTo e e :=
    .inl ⟨rfl, he⟩

lemma ConnectedTo.symm (h : M.ConnectedTo e f) : M.ConnectedTo f e := by
  obtain (⟨rfl, hef⟩ | ⟨C, hC, heC, hfC⟩) := h
  · exact connectedTo_self hef
  exact .inr ⟨C, hC, hfC, heC⟩

lemma connectedTo_comm : M.ConnectedTo e f ↔ M.ConnectedTo f e :=
  ⟨ConnectedTo.symm, ConnectedTo.symm⟩

@[aesop unsafe 10% (rule_sets := [Matroid])]
lemma ConnectedTo.mem_ground_left (h : M.ConnectedTo e f) : e ∈ M.E := by
  obtain (⟨rfl, hef⟩ | ⟨C, hC, heC, -⟩) := h
  · exact hef
  exact hC.subset_ground heC

@[aesop unsafe 10% (rule_sets := [Matroid])]
lemma ConnectedTo.mem_ground_right (h : M.ConnectedTo e f) : f ∈ M.E :=
  h.symm.mem_ground_left

@[simp] lemma connectedTo_self_iff : M.ConnectedTo e e ↔ e ∈ M.E :=
    ⟨fun h ↦ h.mem_ground_left, connectedTo_self⟩

lemma ConnectedTo.nonloop_left_of_ne (h : M.ConnectedTo e f) (hef : e ≠ f) : M.Nonloop e := by
  obtain ⟨C, hC, heC, hfC⟩ := h.exists_circuit_of_ne hef
  exact hC.nonloop_of_mem ⟨e, heC, f, hfC, hef⟩ heC

lemma ConnectedTo.nonloop_right_of_ne (h : M.ConnectedTo e f) (hef : e ≠ f) : M.Nonloop f :=
  h.symm.nonloop_left_of_ne hef.symm

lemma ConnectedTo.to_dual (h : M.ConnectedTo e f) : M✶.ConnectedTo e f := by
  obtain (rfl | hne) := eq_or_ne e f; exact connectedTo_self h.mem_ground_left
  obtain ⟨C, hC, heC, hfC⟩ := h.exists_circuit_of_ne hne
  have hpara : (M ／ (C \ {e,f})).Parallel e f := by
    rw [parallel_iff_circuit hne]
    apply hC.contract_diff_circuit (by simp) (by simp [pair_subset_iff, heC, hfC])
  obtain ⟨B, hB, heB⟩ := hpara.nonloop_left.exists_mem_base
  have hK := fundCocct_cocircuit heB hB
  refine Circuit.mem_connectedTo_mem hK.of_contract.circuit (mem_fundCocct _ _ _) ?_
  exact hpara.mem_cocircuit_of_mem hK (mem_fundCocct _ _ _)

lemma ConnectedTo.of_dual (h : M✶.ConnectedTo e f) : M.ConnectedTo e f := by
  simpa using h.to_dual

@[simp] lemma connectedTo_dual_iff : M✶.ConnectedTo e f ↔ M.ConnectedTo e f :=
  ⟨ConnectedTo.of_dual, ConnectedTo.to_dual⟩

lemma Cocircuit.mem_connectedTo_mem (hK : M.Cocircuit K) (heK : e ∈ K) (hfK : f ∈ K) :
    M.ConnectedTo e f :=
  (hK.circuit.mem_connectedTo_mem heK hfK).of_dual

lemma ConnectedTo.exists_cocircuit_of_ne (h : M.ConnectedTo e f) (hne : e ≠ f) :
    ∃ K, M.Cocircuit K ∧ e ∈ K ∧ f ∈ K :=
  h.to_dual.exists_circuit_of_ne hne

lemma ConnectedTo.of_restrict {R : Set α} (hR : R ⊆ M.E) (hef : (M ↾ R).ConnectedTo e f) :
    M.ConnectedTo e f := by
  obtain (rfl | hne) := eq_or_ne e f
  · simp [hR hef.mem_ground_left]
  obtain ⟨C, hC, heC, hfC⟩ := hef.exists_circuit_of_ne hne
  rw [restrict_circuit_iff] at hC
  exact hC.1.mem_connectedTo_mem heC hfC

lemma ConnectedTo.of_delete {D : Set α} (hef : (M ＼ D).ConnectedTo e f) : M.ConnectedTo e f := by
  rw [delete_eq_restrict] at hef; apply hef.of_restrict diff_subset

lemma ConnectedTo.of_contract {C : Set α} (hef : (M ／ C).ConnectedTo e f) : M.ConnectedTo e f := by
  replace hef := hef.to_dual
  rw [contract_dual_eq_dual_delete] at hef
  exact hef.of_delete.of_dual

lemma ConnectedTo.of_minor {N : Matroid α} (hef : N.ConnectedTo e f) (h : N ≤m M) :
    M.ConnectedTo e f := by
  obtain ⟨C, D, -, -, -, rfl⟩ := h; exact hef.of_delete.of_contract

private lemma connectedTo_of_indep_hyperplane_of_not_coloop {I : Set α} (hI : M.Indep I)
    (hI' : M.Hyperplane I) (heI : e ∈ M.E \ I) (hfI : f ∈ I) (hf : ¬ M.Coloop f) :
    M.ConnectedTo e f := by
  have hB : M.Base (insert e I) := by
    refine Indep.base_of_spanning ?_ (hI'.spanning_of_ssuperset (ssubset_insert heI.2))
    · rwa [hI.insert_indep_iff_of_not_mem heI.2, hI'.flat.cl]
  simp only [hB.mem_coloop_iff_forall_not_mem_fundCct (.inr hfI), mem_diff, mem_insert_iff, not_or,
    and_imp, not_forall, Classical.not_imp, not_not, exists_prop, exists_and_left] at hf
  obtain ⟨x, hx, hxe, hxI, hfC⟩ := hf
  have hxi : M.Indep ((insert x I) \ {e}) := by
    rw [diff_singleton_eq_self (by simp [Ne.symm hxe, heI.2]), hI.insert_indep_iff_of_not_mem hxI,
      hI'.flat.cl]
    exact ⟨hx, hxI⟩
  have hC := Base.fundCct_circuit hB (show x ∈ M.E \ insert e I by simp [hx, hxI, hxe])

  refine hC.mem_connectedTo_mem (by_contra fun heC ↦ ?_) hfC

  have hss := subset_diff_singleton (fundCct_subset_insert x (insert e I)) heC
  simp only [insert_comm, mem_singleton_iff, insert_diff_of_mem] at hss
  exact hC.dep.not_indep (hxi.subset hss)

lemma ConnectedTo.trans {e₁ e₂ : α} (h₁ : M.ConnectedTo e₁ f) (h₂ : M.ConnectedTo f e₂) :
    M.ConnectedTo e₁ e₂ := by
  obtain (rfl | hne) := eq_or_ne e₁ e₂; simp [h₁.mem_ground_left]
  obtain (rfl | hne₁) := eq_or_ne e₁ f; assumption
  obtain (rfl | hne₂) := eq_or_ne f e₂; assumption
  obtain ⟨K₁, hK₁, he₁K₁, hfK₁⟩ := h₁.exists_cocircuit_of_ne hne₁
  obtain ⟨C₂, hC₂, hfC₂, he₂C₂⟩ := h₂.exists_circuit_of_ne hne₂

  by_cases he₂K₁ : e₂ ∈ K₁; exact (hK₁.mem_connectedTo_mem he₁K₁ he₂K₁)

  have hC₂i : M.Indep (C₂ \ K₁) := (hC₂.diff_singleton_indep hfC₂).subset
      (subset_diff_singleton diff_subset (by simp [hfK₁]))

  have hH := hK₁.compl_hyperplane

  obtain ⟨J, hJ, he₂J⟩ :=
    hC₂i.subset_basis_of_subset (diff_subset_diff_left hC₂.subset_ground) hH.subset_ground

  refine (connectedTo_of_indep_hyperplane_of_not_coloop ?_
    (hH.basis_hyperplane_delete hJ) ?_ ?_ ?_).of_delete
  · simp [disjoint_sdiff_right, hJ.indep]
  · simpa [h₁.mem_ground_left, he₁K₁] using
      not_mem_subset hJ.subset (by simp [he₁K₁, h₁.mem_ground_left])
  · exact he₂J ⟨he₂C₂, he₂K₁⟩

  refine Circuit.not_coloop_of_mem ?_ he₂C₂
  rwa [delete_circuit_iff, and_iff_right hC₂, disjoint_iff_inter_eq_empty, ← inter_diff_assoc,
    diff_eq_empty, ← inter_diff_assoc, inter_eq_self_of_subset_left hC₂.subset_ground]

def Connected (M : Matroid α) := M.Nonempty ∧ ∀ ⦃e f⦄, e ∈ M.E → f ∈ M.E → M.ConnectedTo e f

lemma Connected.to_dual (hM : M.Connected) : M✶.Connected :=
  ⟨by have := hM.1; apply dual_nonempty, fun _ _ he hf ↦ (hM.2 he hf).to_dual⟩

lemma Connected.of_dual (hM : M✶.Connected) : M.Connected := by
  simpa using hM.to_dual

@[simp] lemma connected_dual_iff : M✶.Connected ↔ M.Connected :=
  ⟨Connected.of_dual, Connected.to_dual⟩

lemma Coloop.not_connected (he : M.Coloop e) (hE : M.E.Nontrivial) : ¬ M.Connected := by
  obtain ⟨f, hfE, hfe⟩ := hE.exists_ne e
  rintro ⟨-, hconn⟩
  obtain ⟨K, hK, heK, -⟩ := (hconn he.mem_ground hfE).exists_circuit_of_ne hfe.symm
  exact he.not_mem_circuit hK heK

lemma Loop.not_connected (he : M.Loop e) (hE : M.E.Nontrivial) : ¬ M.Connected := by
  rw [← connected_dual_iff]
  exact he.dual_coloop.not_connected hE

lemma Connected.loopless (hM : M.Connected) (hE : M.E.Nontrivial) : M.Loopless := by
  rw [loopless_iff_forall_not_loop]
  exact fun e _ hl ↦ hl.not_connected hE hM

lemma Connected.exists_circuit_of_ne (h : M.Connected) (he : e ∈ M.E) (hf : f ∈ M.E) (hne : e ≠ f) :
    ∃ C, M.Circuit C ∧ e ∈ C ∧ f ∈ C :=
  (h.2 he hf).exists_circuit_of_ne hne

lemma Connected.exists_circuit (h : M.Connected) (hM : M.E.Nontrivial) (he : e ∈ M.E)
    (hf : f ∈ M.E) : ∃ C, M.Circuit C ∧ e ∈ C ∧ f ∈ C := by
  obtain (rfl | hne) := eq_or_ne e f
  · obtain (he' | he') := em (M.Coloop e)
    · exact False.elim <| he'.not_connected hM h
    obtain ⟨C, hC, heC⟩ := exists_mem_circuit_of_not_coloop he he'
    exact ⟨C, hC, heC, heC⟩
  exact (h.2 he hf).exists_circuit_of_ne hne

lemma singleton_connected (hM : M.E = {e}) : M.Connected :=
  ⟨⟨by simp [hM]⟩, by simp [hM]⟩

-- theorem Connected.finite_of_finitary_of_cofinitary (hM : M.Connected) [Finitary M] [Finitary M✶] :
--     M.Finite := by

--   let goodSet := {I : Set α // Set.Infinite {C | M.Circuit C ∧ I ⊆ C}}

--   set I' : ℕ → goodSet := sorry

--   set I : ℕ → Set α := fun i ↦ (I' i).1

--   have hI_strict : StrictMono I := sorry
--   -- have hI_strict : ∀ ⦃i j⦄, i < j → I i ⊂ I j := sorry
--   have hIC : ∀ i, ∃ C, M.Circuit C ∧ I i ⊂ C := by
--     intro i
--     obtain ⟨C, hC⟩ := (I' (i+1)).2.nonempty
--     exact ⟨C, hC.1, ssubset_of_ssubset_of_subset (hI_strict (Nat.lt.base i)) hC.2⟩

--   set I₀ := ⋃ i, I i with hI₀_def

--   have hI₀ : M.Indep I₀ := by
--     rw [indep_iff_forall_finite_subset_indep]
--     intro J hJss hJfin
--     rw [hJfin.subset_iUnion_mono_iff hI_strict.monotone] at hJss
--     obtain ⟨i, hJi⟩ := hJss
--     obtain ⟨C, hC, hssu⟩ := hIC i
--     exact (hC.ssubset_indep hssu).subset hJi

--   obtain ⟨B, hB, hIB⟩ := hI₀.exists_base_superset

--   obtain ⟨e, heI1, -⟩ := exists_of_ssubset <| hI_strict (show 0 < 1 by norm_num)
--   obtain ⟨K,hK, hKB⟩ := hB.indep.exists_cocircuit_inter_eq_mem (show e ∈ _ from sorry)

--   have hufin := hK.finite.biUnion (t := fun x ↦ I₀ ∩ (M.fundCct x B)) sorry

--   obtain ⟨m, hem, hb⟩ : ∃ m, e ∈ I m ∧ ∀ x ∈ K, I₀ ∩ M.fundCct x B ⊆ I m := by
--     have h:= hufin.subset_iUnion_mono_iff hI_strict.monotone
--     simp only [iUnion_subset_iff, inter_subset_left, implies_true, true_iff] at h
--     obtain ⟨m', hm'⟩ := h
--     refine ⟨m' + 1, ?_, fun x hx ↦ (hm' x hx).trans (hI_strict.monotone <| Nat.le_add_right m' 1)⟩
--     exact hI_strict.monotone (Nat.le_add_left 1 _) heI1


--   obtain ⟨Cm, hCm, hImCm⟩ := hIC m
--   have hnt := hCm.cocircuit_inter_nontrivial hK ⟨e, hImCm.subset hem, (hKB.symm.subset rfl).1⟩
--   obtain ⟨f, ⟨hfCm, hfK⟩, hfe⟩ := hnt.exists_ne e

--   have foo : ∃ C', (M ／ (B \ I₀)).Circuit C' ∧ (I m) ⊆ C' := sorry

  -- have := hCm.ssubset_indep (X := M.fundCct f B)




  -- set x : ℕ → α := sorry
  -- have hinj : Function.Injective x := sorry
  -- have hx : ∀ t, ∃ C, M.Circuit C ∧ ∀ i ≤ t, x i ∈ C := sorry

  -- have hxE : range x ⊆ M.E := by
  --   rintro _ ⟨i, hi, rfl⟩; obtain ⟨C, hC⟩ := hx i; exact hC.1.subset_ground (hC.2 i rfl.le)

  -- have hI : M.Indep (range x) := by
  --   rw [indep_iff_forall_finite_subset_indep]
  --   simp_rw [subset_range_iff_exists_image_eq]
  --   rintro _ ⟨J, rfl⟩ hfin
  --   have hJfin := hfin.of_finite_image (hinj.injOn _)
  --   obtain ⟨b, (hb : ∀ _, _)⟩ := hJfin.bddAbove
  --   obtain ⟨C', hC'⟩ := hx (b+1)

  --   apply hC'.1.ssubset_indep (ssubset_of_ne_of_subset ?_ ?_)
  --   · rintro rfl
  --     simp_rw [hinj.mem_set_image] at hC'
  --     linarith [hb _ <| hC'.2 _ rfl.le]
  --   rintro _ ⟨i, hi, rfl⟩
  --   exact hC'.2 _ ((hb _ hi).trans (by simp))

  -- obtain ⟨B, hB, hIB⟩ := hI.exists_base_superset

  -- have : ∃ b : ℕ, ∀ e ∈ M.fundCocct (x 0) B, M.fundCct e B ⊂ insert e (x '' Iic b) := sorry


      -- simp_rw [InjOn.mem_of_mem_image (hinj.injOn J) Subset.rfl] at hC'
    -- intro J hJX hJfin
    -- obtain ⟨J, rfl, hinj⟩ := exists_image_eq_injOn_of_subset_range hJX

    -- obtain ⟨b, (hb : ∀ _, _)⟩ := hJfin.bddAbove
    -- obtain ⟨C', hC'⟩ := hx (b+1)
    -- apply hC'.1.ssubset_indep (ssubset_of_ne_of_subset ?_ ?_)
    -- · rintro rfl
    --   have :=
    -- simp_rw [subset_range_iff_exists_image_eq]
    -- rintro _ ⟨C, rfl⟩ hC



  -- classical
  -- refine ⟨not_infinite.1 fun hinf ↦ ?_⟩
  -- have hnt := hinf.nontrivial
  -- obtain ⟨e, he⟩ := hinf.nonempty

  -- -- There are infinitely many circuits containing `e`. Let `eCs` be a sequence of them.
  -- have hCs0 : {C | e ∈ C ∧ M.Circuit C}.Infinite := by
  --   intro hfin
  --   have _ := hfin.to_subtype
  --   have hfin' := @Finite.Set.finite_biUnion (ι := Set α) (t := id) _ (by assumption)
  --     (fun C hC ↦ Finite.to_subtype (by exact hC.2.finite))
  --   obtain ⟨f, hfE, hf⟩ := (hinf.diff hfin').nonempty
  --   simp only [mem_setOf_eq, id_eq, mem_iUnion, exists_prop, not_exists, not_and, and_imp] at hf
  --   obtain ⟨C', hC', heC', hfC'⟩ := hM.exists_circuit hnt he hfE
  --   exact hf _ heC' hC' hfC'
  -- obtain eCs := Set.Infinite.natEmbedding _ hCs0

  -- -- Let `Z` be the union of the `eCs`. This set is countably infinite; pick an enumeration
  -- -- `x` of `Z` starting from `e`.
  -- set Z := (⋃ i, (eCs i).1)
  -- have heZ : e ∈ Z := mem_iUnion_of_mem 0 (eCs 0).2.1
  -- obtain x' : ℕ ≃ Z := by
  --   refine Nonempty.some <| @nonempty_equiv_of_countable  _ _ _ _ ?_ ?_
  --   · simp only [mem_setOf_eq, coe_setOf, countable_coe_iff, Z]
  --     exact countable_iUnion fun i ↦ Finite.countable ((eCs i).2.2.finite.to_subtype)
  --   exact Infinite.to_subtype <| infinite_iUnion <| Subtype.val_injective.comp eCs.injective

  -- set x : ℕ ≃ Z := (Equiv.swap 0 (x'.symm ⟨e,heZ⟩)).trans x'
  -- have hx0 : x 0 = e := by simp [x]

  -- let nextCs (Cs : Set (Set α)) (x : α) :=
  --   if {C ∈ Cs | x ∈ C}.Infinite then {C ∈ Cs | x ∈ C} else {C ∈ Cs | x ∉ C}

  -- let Cs : ℕ → Set (Set α) :=  Nat.rec (range (Subtype.val ∘ eCs))
  --   (fun i Cs' ↦ nextCs Cs' (x (i+1)))

  -- set ind := {i | ∀ C ∈ Cs i, (x i).1 ∈ C} with hind








    -- simp at this
    -- have _ : ∀ C : {C | e ∈ C ∧ M.Circuit C}, C.1.Finite := sorry

    -- have := hfin.iUnion (s := id) (fun C hC ↦ hC.2.finite) ()

  -- obtain ⟨C₀, hC₀, heC₀,-⟩ := hM.exists_circuit hnt he he

  -- have hI : ∃ I ⊂ C₀, e ∈ I ∧ ∃ (Cs : Set (Set α)), (∀ C ∈ Cs, M.Circuit C ∧ C ∩ C₀ = I)
  --   ∧ Cs.PairwiseDisjoint id := by
  --   sorry
  -- -- have _ := hM.loopless hnt
  -- -- have _ : M✶.Loopless := hM.to_dual.loopless hnt
  -- -- obtain ⟨e, he⟩ := hinf.nonempty
  -- -- have := M✶.not_loop e
  -- have := (M✶.nonloop_of_not_loop he (M✶.not_loop e)).exists_mem_cocircuit




end Connected

section conn

variable {B B' I I' J K X Y : Set α}

lemma Indep.encard_inter_add_erk_dual_eq_of_cl_eq_cl (hI : M.Indep I) (hI' : M.Indep I')
    (hII' : M.cl I = M.cl I') (hJ : M.Indep J) :
    (I ∩ J).encard + (M ↾ (I ∪ J))✶.erk = (I' ∩ J).encard + (M ↾ (I' ∪ J))✶.erk := by
  obtain ⟨K, hK, hIK⟩ := hI.subset_basis_of_subset (subset_union_left (s := I) (t := J))
  have hsk := (hK.indep.subset_skew_diff hIK)
  rw [skew_iff_cl_skew_left] at hsk
  have' hdj := hsk.disjoint_of_indep_subset_right (hK.indep.diff _) Subset.rfl

  have hb : ∀ ⦃B⦄, M.Basis B (M.cl I) → (M ／ (K \ I)).Basis B (B ∪ J \ (K \ I)) ∧ (K \ I ⊆ B ∪ J) := by
    refine fun B hB ↦ ⟨Indep.basis_of_subset_of_subset_cl ?_ ?_ ?_, ?_⟩
    · rw [(hK.indep.diff _).contract_indep_iff]
      exact ⟨hdj.mono_left hB.subset,
        hsk.union_indep_of_indep_subsets hB.indep hB.subset (hK.indep.diff _) Subset.rfl⟩

    · exact subset_union_left
    · rw [contract_cl_eq, subset_diff, disjoint_union_left, and_iff_left disjoint_sdiff_left,
        and_iff_left (hdj.mono_left hB.subset), ← cl_union_cl_left_eq, hB.cl_eq_cl, cl_cl,
        cl_union_cl_left_eq, union_diff_self, union_eq_self_of_subset_left hIK, hK.cl_eq_cl]
      exact union_subset (hB.subset.trans (M.cl_subset_cl subset_union_left))
        (M.subset_cl_of_subset (diff_subset.trans subset_union_right))

    rw [diff_subset_iff, union_comm B, ← union_assoc]
    exact hK.subset.trans <| subset_union_left

  have hb' : ∀ ⦃B⦄, M.Basis B (M.cl I) →
      (B ∩ J).encard + (M ／ (K \ I) ↾ (B ∪ J \ (K \ I)))✶.erk = (J \ (K \ I)).encard := by
    intro B hB
    rw [(hb hB).1.erk_dual_restrict, union_diff_left,
      ← encard_diff_add_encard_inter (J \ (K \ I)) B, add_comm, inter_comm _ B,
      inter_diff_distrib_left, (hdj.mono_left hB.subset).inter_eq, diff_empty]

  have hind : ∀ Y, (M ↾ (Y ∪ J)).Indep (K \ I) := by
    intro Y
    rw [restrict_indep_iff, and_iff_right (hK.indep.diff I), diff_subset_iff, union_comm Y,
      ← union_assoc]
    exact hK.subset.trans subset_union_left
  have hI'b := hII'.symm ▸ hI'.basis_cl
  rw [← (hind I).contract_er_dual_eq,  ← (hind I').contract_er_dual_eq,
    restrict_contract_eq_contract_restrict _ (hb hI.basis_cl).2,
    restrict_contract_eq_contract_restrict _ (hb hI'b).2,
    union_diff_distrib, sdiff_eq_left.2 disjoint_sdiff_right,
    union_diff_distrib, sdiff_eq_left.2 (hdj.mono_left hI'b.subset), hb' hI.basis_cl, hb' hI'b]

lemma Basis'.encard_dual_switch_switch_eq {I I' J J' X Y : Set α}
    (hI : M.Basis' I X) (hI' : M.Basis' I' X) (hJ : M.Basis' J Y) (hJ' : M.Basis' J' Y) :
    (I ∩ J).encard + (M ↾ (I ∪ J))✶.erk = (I' ∩ J').encard + (M ↾ (I' ∪ J'))✶.erk := by
  rw [hI.indep.encard_inter_add_erk_dual_eq_of_cl_eq_cl hI'.indep
      (by rw [hI.cl_eq_cl, hI'.cl_eq_cl]) hJ.indep,
    inter_comm, union_comm, hJ.indep.encard_inter_add_erk_dual_eq_of_cl_eq_cl hJ'.indep
      (by rw [hJ.cl_eq_cl, hJ'.cl_eq_cl]) hI'.indep, inter_comm, union_comm]

lemma Basis.encard_dual_switch_switch_eq {I I' J J' X Y : Set α}
    (hI : M.Basis I X) (hI' : M.Basis I' X) (hJ : M.Basis J Y) (hJ' : M.Basis J' Y) :
    (I ∩ J).encard + (M ↾ (I ∪ J))✶.erk = (I' ∩ J').encard + (M ↾ (I' ∪ J'))✶.erk :=
  hI.basis'.encard_dual_switch_switch_eq hI'.basis' hJ.basis' hJ'.basis'

noncomputable def conn (M : Matroid α) (X Y : Set α) : ℕ∞ :=
  let I := (M.exists_basis' X).choose
  let J := (M.exists_basis' Y).choose
  (I ∩ J).encard + (M ↾ (I ∪ J))✶.erk

lemma conn_comm (M : Matroid α) (X Y : Set α) :
    M.conn X Y = M.conn Y X := by
  simp_rw [conn, union_comm, inter_comm]

lemma Basis'.conn_eq (hI : M.Basis' I X) (hJ : M.Basis' J Y) :
    M.conn X Y = (I ∩ J).encard + (M ↾ (I ∪ J))✶.erk := by
  simp_rw [conn, hI.encard_dual_switch_switch_eq (M.exists_basis' X).choose_spec hJ
    (M.exists_basis' Y).choose_spec]

lemma Basis.conn_eq (hI : M.Basis I X) (hJ : M.Basis J Y) :
    M.conn X Y = (I ∩ J).encard + (M ↾ (I ∪ J))✶.erk :=
  hI.basis'.conn_eq hJ.basis'

lemma Indep.conn_eq (hI : M.Indep I) (hJ : M.Indep J) :
    M.conn I J = (I ∩ J).encard + (M ↾ (I ∪ J))✶.erk :=
  hI.basis_self.conn_eq hJ.basis_self

lemma Basis'.conn_eq_of_disjoint (hI : M.Basis' I X) (hJ : M.Basis' J Y) (hXY : Disjoint X Y) :
    M.conn X Y = (M ↾ (I ∪ J))✶.erk := by
  rw [hI.conn_eq hJ, (hXY.mono hI.subset hJ.subset).inter_eq, encard_empty, zero_add]

lemma conn_eq_encard_of_diff {F : Set α} (hXY : Disjoint X Y) (hI : M.Basis' I X)
    (hJ : M.Basis' J Y) (hFIJ : F ⊆ I ∪ J)  (hF : M.Basis' ((I ∪ J) \ F) (X ∪ Y)) :
    M.conn X Y = F.encard := by
  have hF' : M.Basis ((I ∪ J) \ F) (I ∪ J) := by
    refine hF.basis_inter_ground.basis_subset diff_subset
      (subset_inter (union_subset_union hI.subset hJ.subset)
      (union_subset hI.indep.subset_ground hJ.indep.subset_ground))
  rw [hI.conn_eq hJ, hF'.erk_dual_restrict, diff_diff_cancel_left hFIJ,
    (hXY.mono hI.subset hJ.subset).inter_eq, encard_empty, zero_add]

lemma conn_eq_encard_of_diff' {F : Set α} (hXY : Disjoint X Y) (hI : M.Basis' I X)
    (hJ : M.Basis' J Y) (hFI : F ⊆ I)  (hF : M.Basis' ((I \ F) ∪ J) (X ∪ Y)) :
    M.conn X Y = F.encard := by
  apply conn_eq_encard_of_diff hXY hI hJ (hFI.trans subset_union_left)
  rwa [union_diff_distrib, (sdiff_eq_left (x := J)).2 ]
  exact (hXY.symm.mono hJ.subset (hFI.trans hI.subset))

lemma er_add_er_eq_er_union_add_conn (M : Matroid α) (X Y : Set α) :
    M.er X + M.er Y = M.er (X ∪ Y) + M.conn X Y := by
  obtain ⟨I, hI⟩ := M.exists_basis' X
  obtain ⟨J, hJ⟩ := M.exists_basis' Y
  obtain ⟨B, hB⟩ := M.exists_basis' (I ∪ J)
  have hB' : M.Basis' B (X ∪ Y) := by
    rw [basis'_iff_basis_cl, ← cl_cl_union_cl_eq_cl_union, ← hI.cl_eq_cl, ← hJ.cl_eq_cl,
       cl_cl_union_cl_eq_cl_union, ← hB.cl_eq_cl]
    exact ⟨hB.indep.basis_cl, hB.subset.trans (union_subset_union hI.subset hJ.subset)⟩
  rw [hI.conn_eq hJ, ← hI.encard, ← hJ.encard, ← encard_union_add_encard_inter, ← hB'.encard,
    ← (base_restrict_iff'.2 hB).encard_compl_eq, restrict_ground_eq, ← add_assoc, add_comm B.encard,
    add_assoc, add_comm B.encard, encard_diff_add_encard_of_subset hB.subset, add_comm]

lemma conn_cl_left (M : Matroid α) (X Y : Set α) :
    M.conn X Y = M.conn (M.cl X) Y := by
  obtain ⟨I, hI⟩ := M.exists_basis' X
  obtain ⟨J, hJ⟩ := M.exists_basis' Y
  rw [hI.conn_eq hJ, hI.basis_cl_right.basis'.conn_eq hJ]

lemma conn_cl_right (M : Matroid α) (X Y : Set α) :
    M.conn X Y = M.conn X (M.cl Y) := by
  rw [conn_comm, conn_cl_left, conn_comm]

lemma conn_cl_cl (M : Matroid α) (X Y : Set α) :
    M.conn X Y = M.conn (M.cl X) (M.cl Y) := by
  rw [conn_cl_left, conn_cl_right]

lemma conn_mono_left {X' : Set α} (M : Matroid α) (hX : X' ⊆ X) (Y : Set α) :
    M.conn X' Y ≤ M.conn X Y := by
  obtain ⟨I', hI'⟩ := M.exists_basis' X'
  obtain ⟨I, hI, hII'⟩ := hI'.indep.subset_basis'_of_subset (hI'.subset.trans hX)
  obtain ⟨J, hJ⟩ := M.exists_basis' Y
  rw [hI'.conn_eq hJ, hI.conn_eq hJ]
  refine add_le_add (encard_le_card (inter_subset_inter_left _ hII')) (Minor.erk_le ?_)
  rw [dual_minor_iff]
  exact (Restriction.of_subset M (union_subset_union_left _ hII')).minor

lemma conn_mono_right {Y' : Set α} (M : Matroid α) (X : Set α) (hY : Y' ⊆ Y) :
    M.conn X Y' ≤ M.conn X Y := by
  rw [conn_comm, conn_comm _ X]
  exact M.conn_mono_left hY _

lemma conn_mono {X' Y' : Set α} (M : Matroid α) (hX : X' ⊆ X) (hY : Y' ⊆ Y) :
    M.conn X' Y' ≤ M.conn X Y :=
  ((M.conn_mono_left hX Y').trans (M.conn_mono_right _ hY))

@[simp] lemma empty_conn (M : Matroid α) (X : Set α) : M.conn ∅ X = 0 := by
  obtain ⟨I, hI⟩ := M.exists_basis' X
  rw [(M.empty_indep.basis_self.basis').conn_eq hI, empty_inter, encard_empty,
    erk_dual_restrict_eq_zero_iff.2 (by simpa using hI.indep), zero_add]

@[simp] lemma conn_empty (M : Matroid α) (X : Set α) : M.conn X ∅ = 0 := by
  rw [conn_comm, empty_conn]

lemma conn_subset (M : Matroid α) (hXY : X ⊆ Y) : M.conn X Y = M.er X := by
  obtain ⟨I, hI⟩ := M.exists_basis' X
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_basis'_of_subset (hI.subset.trans hXY)
  rw [hI.conn_eq hJ, inter_eq_self_of_subset_left hIJ, union_eq_self_of_subset_left hIJ,
    hJ.indep.erk_dual_restrict_eq, ← hI.encard, add_zero]

lemma conn_eq_zero (M : Matroid α) (hX : X ⊆ M.E := by aesop_mat) (hY : Y ⊆ M.E := by aesop_mat) :
    M.conn X Y = 0 ↔ M.Skew X Y := by
  obtain ⟨I, hI⟩ := M.exists_basis X
  obtain ⟨J, hJ⟩ := M.exists_basis Y
  rw [skew_iff_cl_skew, conn_cl_cl, ← hI.cl_eq_cl, ← hJ.cl_eq_cl, ← skew_iff_cl_skew,
    ← conn_cl_cl, hI.indep.conn_eq hJ.indep, add_eq_zero_iff, encard_eq_zero,
    ← disjoint_iff_inter_eq_empty, erk_dual_restrict_eq_zero_iff,
    hI.indep.skew_iff_disjoint_union_indep hJ.indep]

lemma conn_eq_conn_inter_ground (M : Matroid α) (X Y : Set α) :
    M.conn X Y = M.conn (X ∩ M.E) (Y ∩ M.E) := by
  rw [conn_cl_cl, ← cl_inter_ground, ← cl_inter_ground _ Y, ← conn_cl_cl]

lemma conn_eq_conn_inter_ground_left (M : Matroid α) (X Y : Set α) :
    M.conn X Y = M.conn (X ∩ M.E) Y := by
  rw [conn_cl_left, ← cl_inter_ground, ← conn_cl_left]

/-- Connectivity to complement is self-dual. -/
lemma conn_compl_dual (M : Matroid α) (X : Set α) : M.conn X (M.E \ X) = M✶.conn X (M.E \ X) := by
  suffices ∀ X ⊆ M.E, M.conn X (M.E \ X) = M✶.conn X (M.E \ X) by
    rw [conn_eq_conn_inter_ground_left, M✶.conn_eq_conn_inter_ground_left,
      show M.E \ X = M.E \ (X ∩ M.E) by simp, this _ inter_subset_right, dual_ground]
  intro X hX

  obtain ⟨I, hI⟩ := M.exists_basis X
  obtain ⟨J, hJ⟩ := M.exists_basis (M.E \ X)
  obtain ⟨BX, hBX, hIBX⟩ := hI.indep.subset_basis_of_subset
    (subset_union_left (s := I) (t := J))
  have hIJE : M.Spanning (I ∪ J) := by
    rw [spanning_iff_cl, ← cl_cl_union_cl_eq_cl_union, hI.cl_eq_cl, hJ.cl_eq_cl,
      cl_cl_union_cl_eq_cl_union, union_diff_cancel hX, cl_ground]

  have hBXb : M.Base BX := by rw [← basis_ground_iff, ← hIJE.cl_eq]; exact hBX.basis_cl_right

  obtain rfl : I = BX ∩ X := hI.eq_of_subset_indep (hBXb.indep.inter_right _)
    (subset_inter hIBX hI.subset) inter_subset_right

  have hBXdual := hBXb.compl_inter_basis_of_inter_basis hI
  rw [diff_inter_diff, union_comm, ← diff_diff] at hBXdual

  obtain ⟨BY, hBY, hJBY⟩ := hJ.indep.subset_basis_of_subset (subset_union_right (s := BX ∩ X))
  have hBYb : M.Base BY := by rw [← basis_ground_iff, ← hIJE.cl_eq]; exact hBY.basis_cl_right

  obtain rfl : J = BY ∩ (M.E \ X) := hJ.eq_of_subset_indep (hBYb.indep.inter_right _)
    (subset_inter hJBY hJ.subset) inter_subset_right

  have hBYdual := hBYb.compl_inter_basis_of_inter_basis hJ
  rw [diff_inter_diff, union_comm, ← diff_diff, diff_diff_cancel_left hX] at hBYdual

  rw [hBYdual.basis'.conn_eq_of_disjoint hBXdual.basis' disjoint_sdiff_right,
    hI.basis'.conn_eq_of_disjoint hJ.basis' disjoint_sdiff_right, hBX.erk_dual_restrict,
    union_diff_distrib, diff_eq_empty.2 inter_subset_left, empty_union,
    Basis.erk_dual_restrict (hBYb.compl_base_dual.basis_ground.basis_subset _ _)]

  · rw [union_diff_distrib, diff_eq_empty.2 (diff_subset_diff_left hX), empty_union, diff_diff,
      diff_diff, ← union_assoc, union_comm, ← diff_diff, diff_diff_cancel_left hBYb.subset_ground,
      ← diff_diff, inter_diff_distrib_left, inter_eq_self_of_subset_left hBYb.subset_ground,
      diff_self_inter]
  · rw [← union_diff_cancel hX, union_diff_distrib, union_diff_cancel hX, diff_diff, diff_diff]
    refine union_subset_union_right _ (diff_subset_diff_right ?_)
    simp only [union_subset_iff, subset_union_left, true_and]
    exact hBX.subset.trans (union_subset_union inter_subset_right inter_subset_left)

  exact union_subset (diff_subset.trans hX) (diff_subset.trans diff_subset)

end conn

section separation

variable {k : ℕ} {P : Set α → Prop} {a b : α}

protected structure Partition (M : Matroid α) where
  left : Set α
  right : Set α
  disjoint : Disjoint left right
  union_eq : left ∪ right = M.E

@[simps] def Partition.symm (P : M.Partition) : M.Partition where
  left := P.2
  right := P.1
  disjoint := P.disjoint.symm
  union_eq := by rw [← P.union_eq, union_comm]

@[simps] def Partition.dual (P : M.Partition) : M✶.Partition where
  left := P.1
  right := P.2
  disjoint := P.disjoint
  union_eq := P.union_eq

@[simps] def Partition.of_subset (A : Set α) (hX : A ⊆ M.E := by aesop_mat) : M.Partition where
  left := A
  right := M.E \ A
  disjoint := disjoint_sdiff_right
  union_eq := by simp [hX]

@[simp, aesop unsafe 10% (rule_sets := [Matroid])]
lemma Partition.left_subset_ground (P : M.Partition) : P.1 ⊆ M.E := by
  rw [← P.union_eq]; apply subset_union_left

@[simp, aesop unsafe 10% (rule_sets := [Matroid])]
lemma Partition.right_subset_ground (P : M.Partition) : P.2 ⊆ M.E := by
  rw [← P.union_eq]; apply subset_union_right

noncomputable abbrev Partition.conn (P : M.Partition) : ℕ∞ := M.conn P.1 P.2

lemma Partition.compl_left (P : M.Partition) : M.E \ P.1 = P.2 := by
  simp [← P.union_eq, P.disjoint.symm]

lemma Partition.compl_right (P : M.Partition) : M.E \ P.2 = P.1 := by
  simp [← P.union_eq, P.disjoint]

@[simp] lemma Partition.conn_symm (P : M.Partition) : P.symm.conn = P.conn :=
  M.conn_comm _ _

@[simp] lemma Partition.conn_dual (P : M.Partition) : P.dual.conn = P.conn := by
  change M✶.conn _ _ = M.conn _ _
  rw [← P.compl_left, conn_compl_dual, P.compl_left]; rfl

@[simp] lemma Partition.conn_eq_zero_iff {P : M.Partition} : P.conn = 0 ↔ M.Skew P.1 P.2 :=
  M.conn_eq_zero P.left_subset_ground P.right_subset_ground

def Partition.IsTutteSep (P : M.Partition) (k : ℕ) :=
  P.conn < k ∧ k ≤ P.1.encard ∧ k ≤ P.2.encard

lemma connected_iff_not_exists_tutteSep [M.Nonempty] :
    M.Connected ↔ ¬ ∃ (P : M.Partition), P.IsTutteSep 1 := by
  rw [iff_not_comm]
  simp only [Connected, show M.Nonempty by assumption, true_and, not_forall, Classical.not_imp,
    exists_and_left, exists_prop, exists_and_left, Partition.IsTutteSep, Nat.cast_one,
    ENat.lt_one_iff, one_le_encard_iff_nonempty]
  simp only [Partition.conn_eq_zero_iff, and_self,
    skew_iff_forall_circuit (Partition.disjoint _) (Partition.left_subset_ground _)
      (Partition.right_subset_ground _)]

  refine ⟨fun ⟨P, ⟨hc, hA, hB⟩⟩ ↦ ?_, fun ⟨x, y, hy, hx, h⟩ ↦ ?_⟩
  · obtain ⟨a, ha⟩ := hA
    obtain ⟨b, hb⟩ := hB
    refine ⟨a, b, by simp [P.union_eq.symm, hb], by simp [P.union_eq.symm, ha], fun hconn ↦ ?_⟩
    obtain ⟨C, hC, haC, hbC⟩ := hconn.exists_circuit_of_ne (P.disjoint.ne_of_mem ha hb)
    obtain (hCA | hCB) := hc C hC (hC.subset_ground.trans_eq P.union_eq.symm)
    · exact P.disjoint.ne_of_mem (hCA hbC) hb rfl
    exact P.symm.disjoint.ne_of_mem (hCB haC) ha rfl
  refine ⟨Partition.of_subset {z | M.ConnectedTo x z} (fun z hz ↦ hz.mem_ground_right),
    ?_, ⟨x, by simpa⟩, ⟨y, by simp [hy, h]⟩⟩
  simp only [Partition.of_subset_left, Partition.of_subset_right, union_diff_self]
  rintro C hC -
  obtain ⟨e, he⟩ := hC.nonempty
  by_cases hex : M.ConnectedTo x e
  · refine .inl (fun y hy ↦ hex.trans <| hC.mem_connectedTo_mem he hy )
  refine .inr fun z hzC ↦ ⟨hC.subset_ground hzC, fun (hz : M.ConnectedTo x z) ↦ ?_⟩
  exact hex <| hz.trans <| hC.mem_connectedTo_mem hzC he

-- def TutteConnected (k : ℕ) := ¬ ∃



end separation
