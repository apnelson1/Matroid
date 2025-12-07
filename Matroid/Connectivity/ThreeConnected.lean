import Matroid.Connectivity.Infinite
import Matroid.ForMathlib.Data.Set.Subsingleton
import Matroid.ForMathlib.GCongr

open Set Matroid.Partition

namespace Matroid

section separation

set_option linter.style.longLine false


variable {α : Type*} {N M : Matroid α} {j k : ℕ∞} {a b e f : α} {A B X Y : Set α}

-- abbrev ThreeConnected (M : Matroid α) := M.IsTutteConnected 3

-- abbrev InternallyThreeConnected (M : Matroid α) := M.IsInternallyConnected 3


section Minor

lemma VerticallyConnected.contract {C : Set α} (h : M.VerticallyConnected (k + M.eRk C)) :
    (M ／ C).VerticallyConnected k := by
  wlog hCE : C ⊆ M.E generalizing C with aux
  · rw [← M.contract_inter_ground_eq]
    exact aux (h.mono (by grw [eRk_mono _ inter_subset_left])) inter_subset_right
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one; simp
  rw [add_right_comm] at h
  refine verticallyConnected_iff_forall.2 fun P hPconn hP ↦ ?_
  have hl := h.not_isVerticalSeparation (P := P.ofContractLeft)
    (by grw [ENat.add_one_le_add_one_iff, eConn_ofContractLeft, eLocalConn_le_eRk_right,
    add_right_comm, hPconn])
  rw [isVerticalSeparation_iff_nonspanning, ofContractLeft_left, ofContractLeft_right] at hl
  rw [isVerticalSeparation_iff_nonspanning, contract_nonspanning_iff,
    contract_nonspanning_iff] at hP
  simp [hP.1.1, hP.2.1.subset subset_union_left] at hl

lemma VerticallyConnected.contract_of_top (h : M.VerticallyConnected ⊤) (C : Set α) :
    (M ／ C).VerticallyConnected ⊤ :=
  (h.mono le_top).contract

lemma TutteConnected.contract {C : Set α} (h : M.TutteConnected (k + M.eRk C + 1))
    (hnt : 2 * (k + M.eRk C) < M.E.encard + 1) : (M ／ C).TutteConnected (k + 1) := by
  obtain rfl | hne := eq_or_ne k 0; simp
  wlog hCE : C ⊆ M.E generalizing C with aux
  · specialize aux (C := C ∩ M.E)
    grw [M.eRk_mono inter_subset_left, imp_iff_right inter_subset_right,
      contract_inter_ground_eq] at aux
    exact aux h hnt
  have hnt' := Order.le_of_lt_add_one hnt
  have hgirth := h.le_girth hnt'
  have hC : M.Indep C := indep_of_eRk_add_one_lt_girth (by enat_to_nat! <;> omega) hCE
  have hfin : C.Finite := not_infinite.1 fun hinf ↦ by
    simp [hC.eRk_eq_encard, hinf.encard_eq] at hnt
  rw [tutteConnected_iff_verticallyConnected_girth]
  refine ⟨(h.verticallyConnected.mono ?_).contract, ?_⟩
  · grw [add_right_comm]
  · have hle := hgirth.trans (M.girth_le_girth_contract_add C)
    · rwa [add_right_comm, WithTop.add_le_add_iff_right
        (M.isRkFinite_of_finite hfin).eRk_lt_top.ne] at hle
  grw [hC.eRk_eq_encard, ← encard_diff_add_encard_of_subset hCE, ← contract_ground] at hnt
  enat_to_nat! <;> omega

lemma TutteConnected.delete {D : Set α} (h : M.TutteConnected (k + M✶.eRk D + 1))
    (hnt : 2 * (k + M✶.eRk D) < M.E.encard + 1) : (M ＼ D).TutteConnected (k + 1) :=
  dual_contract_dual .. ▸ (h.dual.contract (by simpa)).dual

lemma TutteConnected.contractElem (h : M.TutteConnected (k + 1)) (hnt : 2 * k < M.E.encard + 1)
    (e : α) : (M ／ {e}).TutteConnected k := by
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one; simp
  refine TutteConnected.contract (h.mono (by grw [eRk_singleton_le])) ?_
  grw [eRk_singleton_le]
  assumption

/-- I believe that this is false if the assumption is relaxed to `2 * k ≤ M.E.encard`
in the case where `k = ⊤` and `M` is a free extension of a nontrivial sparse paving matroid by `e`-/
lemma TutteConnected.deleteElem (h : M.TutteConnected (k + 1)) (hnt : 2 * k < M.E.encard + 1)
    (e : α) : (M ＼ {e}).TutteConnected k := by
  simpa using (h.dual.contractElem (by simpa) e).dual

end Minor

/-- Any element can be deleted or contracted from a `k`-connected tame uniform matroid to preserve
`k`-connectedness. The proof is mostly the discharging of trivialities. -/
lemma IsUniform.contract_or_delete_tutteConnected_of_tutteConnected [M.Tame] (hM : M.IsUniform)
    (hconn : M.TutteConnected k) (e : α) :
    (M ／ {e}).TutteConnected k ∨ (M ＼ {e}).TutteConnected k := by
  wlog hfin : M.RankFinite generalizing M with aux
  · have := M.tame_dual
    rw [← tutteConnected_dual_iff, or_comm, ← tutteConnected_dual_iff, dual_contract, dual_delete]
    exact aux hM.dual (by simpa) <|
      (or_iff_right hfin).1 hM.sparsePaving.rankFinite_or_rankFinite_dual
  wlog he : e ∈ M.E generalizing with aux
  · rw [← contract_inter_ground_eq, singleton_inter_eq_empty.2 he, contract_empty]
    exact .inl hconn
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one
  · simp
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one
  · simp
  obtain ⟨E, r, hle, rfl⟩ := hM.exists_eq_unifOn
  simp only [unifOn_ground_eq] at he
  obtain hE | hE := E.subsingleton_or_nontrivial
  · exact .inl <| tutteConnected_of_subsingleton (hE.anti diff_subset) _
  obtain rfl | r := r
  · simp [hE.not_subsingleton] at hconn
  obtain ⟨F, heF, hFne, rfl⟩ : ∃ F, e ∉ F ∧ F.Nonempty ∧ insert e F = E :=
    ⟨E \ {e}, by simp, hE.diff_singleton_nonempty .., insert_diff_self_of_mem he⟩
  rw [unifOn_insert_contractElem heF, unifOn_delete_eq, insert_diff_self_of_notMem heF]
  simp only [unifOn_tutteConnected_iff hle, Nat.cast_add, Nat.cast_one, ENat.add_one_le_add_one_iff,
    ← add_assoc, encard_insert_of_notMem heF, two_mul, add_right_comm (r : ℕ∞) 1 r,
    ENat.add_one_inj] at hconn
  simp only [Nat.cast_add, Nat.cast_one, encard_insert_of_notMem heF,
    ENat.add_one_le_add_one_iff] at hle
  rw [unifOn_tutteConnected_iff hle]
  obtain h_eq | hlt := hle.eq_or_lt
  · eomega
  rw [unifOn_tutteConnected_iff (by simpa using Order.add_one_le_of_lt hlt)]
  eomega

/-- If `(P₁, P₂)` and `(Q₁, Q₂)` are partitions of matroids with the same ground set and both
with sides of size at least `k`, then either `P₁ ∩ Q₁` and `P₂ ∩ Q₂` both have size at least `k/2`,
or `P₁ ∩ Q₂` and `P₂ ∩ Q₁` both have size at least `k/2`. -/
lemma Partition.exists_large_diagonal {M N : Matroid α} (hNM : M.E = N.E) {P : M.Partition}
    {Q : N.Partition} (hP1 : 2 * k + 1 ≤ P.1.encard) (hP2 : 2 * k + 1 ≤ P.2.encard)
    (hQ1 : 2 * k + 1 ≤ Q.1.encard) (hQ2 : 2 * k + 1 ≤ Q.2.encard) :
      (k + 1 ≤ (P.1 ∩ Q.1).encard ∧ k + 1 ≤ (P.2 ∩ Q.2).encard)
    ∨ (k + 1 ≤ (P.1 ∩ Q.2).encard ∧ k + 1 ≤ (P.2 ∩ Q.1).encard) := by
  rw [← Q.union_inter_left P.left (P.left_subset_ground.trans_eq hNM)] at hP1
  rw [← Q.union_inter_left P.right (P.right_subset_ground.trans_eq hNM)] at hP2
  rw [← P.union_inter_right Q.left (Q.left_subset_ground.trans_eq hNM.symm)] at hQ1
  rw [← P.union_inter_right Q.right (Q.right_subset_ground.trans_eq hNM.symm)] at hQ2
  rw [encard_union_eq (by simp)] at hP1 hP2 hQ1 hQ2
  eomega

-- Bixby's lemma.
set_option maxHeartbeats 1000000 in
theorem TutteConnected.internallyConnected_three_contractElem_or_deleteElem
    (hM : M.TutteConnected 3) (e : α) :
    (M ／ {e}).InternallyConnected 3 ∨ (M ＼ {e}).InternallyConnected 3 := by
  obtain heE | heE := em' <| e ∈ M.E
  · simp [contractElem_of_notMem_ground heE, hM.internallyConnected]
  rw [show (3 : ℕ∞) = 1 + 1 + 1 from rfl] at *
  obtain hle | hgt := le_or_gt M.E.encard 4
  · have hfin : M.Finite := by
      rw [finite_iff, ← encard_lt_top_iff]
      enat_to_nat!
    have hU := hM.isUniform_of_encard_le (by eomega)
    obtain (h | h) := hU.contract_or_delete_tutteConnected_of_tutteConnected hM e
    · exact .inl h.internallyConnected
    exact .inr h.internallyConnected
  have hc := hM.contractElem (by eomega) e
  have hd := hM.deleteElem (by eomega) e
  -- Choose bad partitions `P` and `Q` of `M ／ e` and `M ＼ e` respectively.
  simp_rw [hc.internallyConnected_iff_forall, hd.internallyConnected_iff_forall, ENat.add_one_inj]
  by_contra! hcon
  obtain ⟨⟨P, hPconn, hP⟩, ⟨Q, hQconn, hQ⟩⟩ := hcon
  wlog hle : 2 ≤ (P.1 ∩ Q.1).encard ∧ 2 ≤ (P.2 ∩ Q.2).encard generalizing Q with aux
  · obtain (⟨h1, h2⟩ | ⟨h1,h2⟩) := exists_large_diagonal (P := P) (Q := Q) (k := 1) (by simp)
      (by simpa [hPconn] using hP.encard_left_ge)
      (by simpa [hPconn] using hP.encard_right_ge)
      (by simpa [hQconn] using hQ.encard_left_ge)
      (by simpa [hQconn] using hQ.encard_right_ge)
    · eomega
    exact aux Q.symm (by simpa) (by simpa) ⟨h1, h2⟩
  -- Since both sides of `P` and `Q` have size at least three,
  -- we can assume wlog that `P₁ ∩ Q₁` and `P₂ ∩ Q₂` are nontrivial.
  have heP : e ∉ P.left := by simpa using P.disjoint_left_contract
  have heQ : e ∉ Q.left := by simpa using Q.disjoint_left_delete
  have hle' := M.eConn_inter_add_eConn_insert_union_le (C := P.left) (D := Q.left) heP heQ
  simp [hPconn, hQconn] at hle'
  obtain h1 | h1 : M.eConn (P.1 ∩ Q.1) ≤ 1 ∨ M.eConn (insert e (P.1 ∪ Q.1)) ≤ 1 := by eomega
  · let P' := P.ofContractRight.inter Q.ofDeleteRight
    have hleft : P'.left = P.1 ∩ Q.1 := by simp [P']
    have hright : P'.right = insert e (P.2 ∪ Q.2) := by simp [P', insert_union]
    have hP'conn : P'.eConn ≤ 1 := by simpa [P', ← Partition.eConn_left]
    refine hM.not_isTutteSeparation (P := P') (by simpa) ?_
    grw [P'.isTutteSeparation_iff_add_one_le_encard (by generalize P'.eConn = a at *; enat_to_nat),
      hP'conn, hleft, one_add_one_eq_two, and_iff_right hle.1, hright,
      ← encard_le_encard (subset_insert ..),
      ← encard_le_encard subset_union_left, ← hP.encard_right_ge, add_assoc, one_add_one_eq_two]
    simp
  let P' := P.ofContractLeft.union Q.ofDeleteLeft
  have hPl : P.left ∩ Q.left ⊆ P'.left := by
    simp only [union_left, ofContractLeft_left, union_singleton, ofDeleteLeft_left, union_insert,
      mem_union, mem_insert_iff, true_or, insert_eq_of_mem, P']
    grind
  have hPr : P'.right = P.right ∩ Q.right := by simp [P']
  have hP'conn : P'.eConn ≤ 1 := by simpa [P', ← P'.eConn_left, insert_union]
  refine hM.not_isTutteSeparation (P := P') (by simpa) ?_
  grw [Partition.isTutteSeparation_iff_add_one_le_encard
    (by generalize P'.eConn = a at *; enat_to_nat), hP'conn, hPr,
    one_add_one_eq_two, and_iff_left hle.2, ← encard_le_encard hPl, hle.1]

/-- If `e` is a nonloop element of a `k`-connected matroid `M`
such that `M / e` is weakly `(k + 1)`-connected but `M` is not,
then `e` belongs to a rank-`k` cocircuit of `M`. -/
lemma TutteConnected.exists_of_weaklyConnected (hM : M.TutteConnected k) (he : M.IsNonloop e)
    (h_not_conn : ¬ M.WeaklyConnected (k + 1)) (h_conn : (M ／ {e}).WeaklyConnected (k + 1)) :
    ∃ K, M.IsCocircuit K ∧ M.eRk K = k ∧ e ∈ K := by
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one
  · simp at h_not_conn
  -- We can assume that `e` is in `M`, since otherwise `M / {e} = M`.
  -- Since `M` is `2`-connectd but not weakly 3-connected, there is a strong separation `P` with
  -- connectivity `1`. We may assume `e ∈ P.left`.
  simp only [hM.weaklyConnected_add_one_iff, not_forall, exists_prop, not_not] at h_not_conn
  obtain ⟨P, hPconn, hP⟩ := h_not_conn
  have heE := he.mem_ground
  wlog heP : e ∈ P.left generalizing P with aux
  · exact aux P.symm (by simpa) (by simpa) <| by
      rwa [P.symm_left, ← P.compl_left, mem_diff, and_iff_left heP]
  have hePr : e ∉ P.right := by rwa [← compl_left, mem_diff, and_iff_right heE, not_not]
  -- Since `P` is a strong separation of `M`, it follows that `P.right` is dependent and codependent
  -- in `M ／ e`, and that `P.left ＼ e` is dependent in `M ／ e`. Since `P \ e` fails to be a strong
  -- separation in `M`, all that can go wrong is that `P.left \ e` is coindependent in `M`.
  have h_coindep : M.Coindep (P.left \ {e}) := by
    have hstrong := weaklyConnected_iff_forall.1 h_conn (P.contract {e})
      (by grw [P.eConn_contract_le, hPconn])
    rw [isStrongSeparation_iff] at hstrong
    have hcd := hP.codep_right.delete_of_disjoint (D := {e}) (by simpa)
    rw [← dual_contract, dep_dual_iff] at hcd
    have hld := hP.dep_left.contract_of_indep (I := {e}) (he.indep.inter_left _)
    simp only [contract_left, hld, contract_right, diff_singleton_eq_self hePr,
      hP.dep_right.contract_of_disjoint (C := {e}) (by simpa), hcd, and_self,
      and_true, true_and] at hstrong
    rwa [not_codep_iff, coindep_contract_iff, and_iff_left disjoint_sdiff_left] at hstrong
  -- Since `P.left \ e` is coindependent and `P.left` is codependent in `M`, we see that
  -- `P.left \ e` cospans `e` in `M`. Therefore there is a cocircuit `K` with `e ∈ K ⊆ P.left`.
  have hcl : e ∈ M✶.closure (P.left \ {e}) := by
    rw [h_coindep.indep.mem_closure_iff_of_notMem (by simp), insert_diff_self_of_mem heP]
    exact hP.codep_left
  obtain ⟨K, hKss, hK : M.IsCocircuit K, heK⟩ := exists_isCircuit_of_mem_closure hcl (by simp)
  have hKE := hK.subset_ground
  -- Nullity/connectivity arguments now give that `K` must have rank at most `2`.
  refine ⟨K, hK, le_antisymm ?_ ?_, heK⟩
  · grw [M.eRk_mono hKss, insert_diff_self_of_mem heP, ← M.eConn_add_nullity_dual_eq_eRk P.left,
      P.eConn_left, hPconn, ← insert_diff_self_of_mem heP, nullity_insert_eq_add_one hcl (by simp),
      h_coindep.nullity_eq]
    rfl
  by_contra! hlt
  refine hM.not_isTutteSeparation (P := M.partition K hK.subset_ground) ?_ ?_
  · simp only [eConn_partition]
    rw [← M.eConn_add_nullity_dual_eq_eRk K, hK.nullity_eq, ENat.add_one_lt_add_one_iff] at hlt
    exact Order.add_one_le_of_lt hlt
  rw [isTutteSeparation_iff, partition_left .., partition_right .., and_iff_right (.inr hK.dep)]
  refine .inl <| hP.dep_right.superset ?_ diff_subset
  grw [← P.compl_left, hKss, insert_diff_self_of_mem heP]

-- lemma TutteConnected.exists_deleteElement_weaklyConnected_three [M.Finite]
--     (h : M.TutteConnected 3) : ∃ e ∈ M.E, (M ＼ {e}).WeaklyConnected 3 := by
--   by_contra! hcon
--   rw [show (3 : ℕ∞) = 2 + 1 from rfl] at *
--   have aux (e : α) : ∃ x, (M ＼ {e} ／ {x}).WeaklyConnected (2 + 1) := by
--     have h' :

-- `x` element of a matroid `M` => if either `N = M ／ x` or `N = M ＼ x` has a separation
-- `(A,B)` with `λ = k`, then either `A` or `B` has a partition into two sets,
-- where `λ(A₁) ≤ k` or `λ(A₂) ≤ k` in `M`.

variable {N : Matroid α}

def Partition.AdherentIn (P : N.Partition) (M : Matroid α) : Prop :=
    ∃ (X Y : Set α), Disjoint X Y ∧ M.eConn X = N.eConn X ∧ M.eConn Y = N.eConn Y ∧
    (X ∪ Y = P.left ∨ X ∪ Y = P.right)

lemma Partition.AdherentIn.symm {P : N.Partition} (h : P.AdherentIn M) : P.symm.AdherentIn M := by
  obtain ⟨X, Y, hdj, hX, hY, hXY | hXY⟩ := h
  · exact ⟨Y, X, hdj.symm, hY, hX, .inr (union_comm _ _ ▸ hXY)⟩
  exact ⟨Y, X, hdj.symm, hY, hX, .inl (union_comm _ _ ▸ hXY)⟩

@[simp]
lemma Partition.adherentIn_symm_iff {P : N.Partition} : P.symm.AdherentIn M ↔ P.AdherentIn M :=
  ⟨fun h ↦ by simpa using h.symm, Partition.AdherentIn.symm⟩

lemma Partition.AdherentIn.dual {P : N.Partition} (hP : P.AdherentIn M) : P.dual.AdherentIn M✶ := by
  obtain ⟨X, Y, hXY, hX, hY, h | h⟩ := hP
  · exact ⟨X, Y, hXY, by simpa, by simpa, .inl h⟩
  exact ⟨X, Y, hXY, by simpa, by simpa, .inr h⟩

lemma Partition.AdherentIn.of_dual {P : N.Partition} (hP : P.dual.AdherentIn M) :
    P.AdherentIn M✶ := by
  obtain ⟨X, Y, hXY, hX, hY, h | h⟩ := hP
  · exact ⟨X, Y, hXY, by simpa using hX, by simpa using hY, .inl h⟩
  exact ⟨X, Y, hXY, by simpa using hX, by simpa using hY, .inr h⟩

@[simp]
lemma Partition.adherentIn_dual_iff {P : N.Partition} : P.dual.AdherentIn M ↔ P.AdherentIn M✶ :=
  ⟨Partition.AdherentIn.of_dual, fun h ↦ by simpa using h.dual⟩

@[simp]
lemma Partition.copy_adherentIn_iff {N N' : Matroid α} {P : N.Partition} (h_eq : N = N') :
    (P.copy h_eq).AdherentIn M ↔ P.AdherentIn M := by
  simp [AdherentIn, h_eq]

def AdheresTo (N M : Matroid α) : Prop := ∀ (P : N.Partition), P.AdherentIn M

@[simp] lemma adheresTo_self (M : Matroid α) : M.AdheresTo M :=
  fun P ↦ ⟨P.left, ∅, by simp⟩

lemma contractElem_or_deleteElem_adheresTo (M : Matroid α) (e : α) :
    (N ／ {e}).AdheresTo M ∨ (N ＼ {e}).AdheresTo M := by
  simp only [AdheresTo]
  by_contra! hcon
  obtain ⟨⟨P, hP⟩, Q, hQ⟩ := hcon
  wlog hle1 : M.eConn (P.1 ∩ Q.2) ≤ M.eConn (P.2 ∩ Q.2) generalizing M N with aux
  · push_neg at hle1
    refine aux (M := M✶) (N := N✶) (Q.dual.copy (by simp)) (by simpa) (P.dual.copy (by simp))
      (by simpa) ?_
    simp
  wlog hle1 : M.eConn (P.1 ∩ Q.1) ≤ M.eConn (P.2 ∩ Q.2) generalizing P Q with aux
  · push_neg at hle1
    exact aux P.symm (by simpa) Q.symm (by simpa) (by simpa using hle1.le)


    -- apply aux P.symm (fun X Y hdk h1 h2 ↦ ?_)

    -- rw [symm_left, symm_right, and_comm]

  sorry
