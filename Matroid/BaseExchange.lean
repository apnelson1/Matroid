module

public import Matroid.Flat.Hyperplane
public import Matroid.ForMathlib.FinDiff

@[expose] public section

variable {α : Type*} {M : Matroid α} {E I B C H K X Y : Set α} {k : ℕ∞} {e f : α}

namespace Matroid

open Set


section IsFreeBase

variable {B B' : Set α}

/-- A free base is one where exchanging any two elements gives a base. -/
@[mk_iff]
structure IsFreeBase (M : Matroid α) (B : Set α) : Prop where
  isBase : M.IsBase B
  isBase_of_exchange : ∀ B' ⊆ M.E, B'.IsExchange B → M.IsBase B'

@[aesop unsafe 10% (rule_sets := [Matroid]), grind →]
lemma IsFreeBase.subset_ground (h : M.IsFreeBase B) : B ⊆ M.E :=
  h.isBase.subset_ground

lemma IsFreeBase.isBase_insert_diff_singleton (h : M.IsFreeBase B) (he : e ∈ B) (hf : f ∈ M.E \ B) :
    M.IsBase (insert f (B \ {e})) :=
  h.isBase_of_exchange _ (by grind [h.isBase.subset_ground]) (isExchange_sdiff_insert he hf.2).symm

lemma IsFreeBase.compl_dual (hB : M.IsFreeBase B) : M✶.IsFreeBase (M.E \ B) := by
  refine ⟨hB.isBase.compl_isBase_dual, fun B' hB' hB'ex ↦ ?_⟩
  have h1 := (isExchange_sdiff_right_comm hB' hB.isBase.subset_ground).1 hB'ex
  have h2 := (hB.isBase_of_exchange _ sdiff_subset h1).compl_isBase_dual
  rwa [sdiff_sdiff_cancel_left (by simpa)] at h2

lemma isFreeBase_dual_iff (hB : B ⊆ M.E) : M✶.IsFreeBase B ↔ M.IsFreeBase (M.E \ B) := by
  refine ⟨fun h ↦ by simpa using h.compl_dual, fun h ↦ ?_⟩
  rw [← sdiff_sdiff_cancel_left hB]
  exact h.compl_dual

lemma IsFreeBase.indep_of_ssubset_insert (hB : M.IsFreeBase B) (hI : I ⊂ insert e B)
    (he : e ∈ M.E := by aesop_mat) : M.Indep I := by
  by_cases! he : e ∉ (I \ B)
  · exact hB.isBase.indep.subset <| by grind
  obtain ⟨f, hf⟩ := exists_of_ssubset hI
  refine (hB.isBase_insert_diff_singleton (e := f) (f := e) ?_ ?_).indep.subset ?_ <;>
  grind

instance : GroundedPred IsFreeBase := ⟨fun _ _ _ h ↦ h.1.subset_ground⟩

instance : InvariantFun IsFreeBase IsFreeBase where
  of_empty := by simp [isFreeBase_iff]
  map_eq α β M f hf B (hBE : B ⊆ M.E) := by
    simp only [isFreeBase_iff, TransferClass.pure_transfer, TransferClass.set_transfer,
      map_ground, forall_subset_image_iff, eq_iff_iff, map_image_isBase_iff hBE]
    simp only [map_isBase_iff, and_congr_right_iff]
    refine fun hB ↦ ⟨fun h' B' hB'E h ↦ ⟨B', h' B' hB'E ?_, rfl⟩, fun h B' hB' hB'B ↦ ?_⟩
    · rwa [isExchange_image_iff_of_injOn hf hB'E hBE] at h
    specialize h B' hB'
    rw [isExchange_image_iff_of_injOn hf hB' hBE, imp_iff_right hB'B] at h
    obtain ⟨B₀, hB₀, heq⟩ := h
    rw [hf.image_eq_image_iff hB' hB₀.subset_ground] at heq
    rwa [heq]

end IsFreeBase

lemma IsBase.isBase_of_indep_of_finDiff (hB : M.IsBase B) (hI : M.Indep I) (hBI : FinDiff B I) :
    M.IsBase I := by
  obtain ⟨B', hB', hIB'⟩ := hI.exists_isBase_superset
  have hfin' : FinDiff B B' := by
    rw [finDiff_iff, hB'.encard_sdiff_comm hB, and_iff_left rfl]
    exact hBI.sdiff_finite.subset (sdiff_subset_sdiff_right hIB')
  rwa [(hBI.symm.trans hfin').eq_of_subset hIB']

lemma IsBase.isBase_of_spanning_of_finDiff {S : Set α} (hB : M.IsBase B) (hS : M.Spanning S)
    (hBS : FinDiff B S) : M.IsBase S := by
  rw [← M.dual_dual, dual_isBase_iff]
  exact hB.compl_isBase_dual.isBase_of_indep_of_finDiff hS.compl_coindep <|
    hBS.sdiff_right hB.subset_ground hS.subset_ground

lemma IsBase.eq_of_isBase_finDiff_finDiff_subset {Y : Set α} (hB : M.IsBase B) (hBX : B.FinDiff X)
    (hC : M.IsBase C) (hCY : C.FinDiff Y) (hXY : X ⊆ Y) : X = Y := by
  by_cases hss : Y ⊆ X ∪ C
  · have hd' := hCY.sdiff_sdiff (P := Y \ X) (by grind) sdiff_subset
    rw [sdiff_sdiff_cancel_left hXY] at hd'
    have h' := hd'.trans hBX.symm
    have hb := (hB.isBase_of_indep_of_finDiff (hC.indep.subset sdiff_subset) h'.symm)
    grind [hb.eq_of_subset_isBase hC sdiff_subset]
  obtain ⟨e, hecY, heXC⟩ := not_subset.1 hss
  obtain ⟨f, hf⟩ := hCY.sdiff_nonempty_of_nonempty ⟨e, by grind⟩
  have hlt : ((insert f (Y \ {e})) \ (X ∪ C)).encard < (Y \ (X ∪ C)).encard := by
    have hss : (insert f (Y \ {e})) \ (X ∪ C) ⊂ Y \ (X ∪ C) :=
      ssubset_iff_exists.2 ⟨by grind, e, by grind⟩
    exact ((hCY.symm.sdiff_finite.subset (by grind)).subset hss.subset).encard_lt_encard hss
  have hwin := hB.eq_of_isBase_finDiff_finDiff_subset (Y := insert f (Y \ {e})) hBX hC ?_ (by grind)
  · grind
  exact hCY.trans_exchange <| isExchange_sdiff_insert hecY hf.2
termination_by (Y \ (X ∪ C)).encard

/-- The collection of sets that are `FinDiff` of some base is an antichain.
(for a finite-rank matroid `M`, these are the sets whos cardinality is the rank of `M`.)-/
lemma isAntichain_setOf_finDiff_isBase (M : Matroid α) :
    IsAntichain (· ⊆ ·) {X | ∃ B, M.IsBase B ∧ B.FinDiff X} :=
  fun _ ⟨_, hB, hBX⟩ _ ⟨_, hC, hCY⟩ hne hXY ↦ hne <|
    hB.eq_of_isBase_finDiff_finDiff_subset hBX hC hCY hXY

lemma IsBase.finDiff_iff_encard_eq_eRank [M.RankFinite] (hB : M.IsBase B) :
    FinDiff B X ↔ X.encard = M.eRank := by
  rw [hB.finite.finDiff_iff_encard_eq, eq_comm, hB.encard_eq_eRank]

lemma IsCircuitHyperplane.insert_diff_singleton_isBase (hH : M.IsCircuitHyperplane H)
    (he : e ∈ H) (hf : f ∈ M.E \ H) : M.IsBase (insert f (H \ {e})) := by
  have hclosure := hH.isHyperplane.closure_insert_eq hf.2 hf.1
  rw [← closure_insert_closure_eq_closure_insert, ← hH.isCircuit.closure_sdiff_singleton_eq e,
    closure_insert_closure_eq_closure_insert, ← spanning_iff_closure_eq (insert_subset hf.1
    (sdiff_subset.trans hH.subset_ground))] at hclosure
  apply hclosure.isBase_of_indep
  rw [← (hH.isCircuit.sdiff_singleton_indep he).notMem_closure_iff_of_notMem (fun hf' ↦ hf.2 hf'.1),
    hH.isCircuit.closure_sdiff_singleton_eq e, hH.isHyperplane.isFlat.closure]
  exact hf.2

lemma IsCircuit.isHyperplane_of_forall_isBase_of_isExchange (hC : M.IsCircuit C)
    (hex : ∀ B ⊆ M.E, B.IsExchange C → M.IsBase B) (hCE : C ⊂ M.E) : M.IsHyperplane C := by
  obtain ⟨f, hfE, hfC⟩ := exists_of_ssubset hCE
  obtain ⟨e, heC⟩ := hC.nonempty
  have hb := hex (insert f (C \ {e})) (by grind) (isExchange_sdiff_insert heC hfC).symm
  convert hb.isHyperplane_of_closure_diff_singleton (mem_insert ..)
  rw [insert_sdiff_self_of_notMem (by grind)]
  refine (hC.subset_closure_sdiff_singleton e).antisymm fun x hx ↦ by_contra fun hxC ↦ ?_
  have hb' := hex (insert x (C \ {e})) (by grind) (isExchange_sdiff_insert heC hxC).symm
  rw [(hC.sdiff_singleton_indep heC).mem_closure_iff_of_notMem (by grind)] at hx
  exact hx.not_indep hb'.indep

lemma IsCircuitHyperplane.isBase_of_isExchange (hH : M.IsCircuitHyperplane H) (hB : B ⊆ M.E)
    (hHB : H.IsExchange B) : M.IsBase B := by
  obtain ⟨e, he, f, hf, rfl⟩ := hHB.exists
  apply hH.insert_diff_singleton_isBase he.1 (by grind)

/-- `M.IsNonbase K` means that `K` is not a base, but differs from a base by a finite
number of exchanges. For a matroid of rank `r ≠ ∞`, this amounts to saying that `K` is a
dependent `r`-set. -/
@[mk_iff]
structure IsNonbase (M : Matroid α) (K : Set α) : Prop where
  subset_ground : K ⊆ M.E
  not_isBase : ¬ M.IsBase K
  exists_findiff : ∃ B, M.IsBase B ∧ B.FinDiff K

attribute [aesop unsafe 10% (rule_sets := [Matroid]), grind →] IsNonbase.subset_ground

instance : GroundedPred IsNonbase := ⟨fun _ _ _ ↦ IsNonbase.subset_ground⟩

instance : InvariantFun IsNonbase IsNonbase where
  of_empty := by simp [isNonbase_iff]
  map_eq α β M f hf X (hXE : X ⊆ M.E) := by
    simp only [isNonbase_iff, and_iff_right hXE, TransferClass.pure_transfer,
      TransferClass.set_transfer, map_ground, image_subset_iff, map_isBase_iff, not_exists, not_and,
      ↓existsAndEq, and_true, eq_iff_iff]
    refine ⟨fun ⟨hX, B, hB, hBX⟩ ↦ ⟨hXE.trans (subset_preimage_image ..),
      ⟨fun B' hB' hB'X ↦ hX ?_, ?_⟩⟩, fun ⟨_, hXnb, B, hB, hBX⟩ ↦ ⟨fun hX ↦ by grind, ⟨B, hB, ?_⟩⟩⟩
    · rw [hf.image_eq_image_iff hXE hB'.subset_ground] at hB'X
      rwa [hB'X]
    · refine ⟨B, hB, ?_⟩
      rwa [finDiff_image_iff_of_injOn hf hB.subset_ground hXE]
    rwa [← finDiff_image_iff_of_injOn hf hB.subset_ground hXE]

lemma IsNonbase.compl_isNonbase_dual (h : M.IsNonbase K) : M✶.IsNonbase (M.E \ K) := by
  refine ⟨sdiff_subset, ?_, ?_⟩
  · simpa [inter_eq_self_of_subset_right h.subset_ground] using h.not_isBase
  obtain ⟨B, hB, hBK⟩ := h.exists_findiff
  exact ⟨M.E \ B, hB.compl_isBase_dual, hBK.sdiff_right hB.subset_ground h.subset_ground⟩

lemma isNonbase_dual_iff (hK : K ⊆ M.E := by aesop_mat) :
    M✶.IsNonbase K ↔ M.IsNonbase (M.E \ K) :=
  ⟨fun h ↦ by simpa using h.compl_isNonbase_dual, fun h ↦ by
    simpa [sdiff_sdiff_cancel_left hK] using h.compl_isNonbase_dual⟩

lemma IsNonbase.dep (h : M.IsNonbase K) : M.Dep K := by
  obtain ⟨B, hB, hBK⟩ := h.exists_findiff
  rw [← not_indep_iff h.subset_ground]
  exact fun hK ↦ h.not_isBase <| hB.isBase_of_indep_of_finDiff hK hBK

lemma IsNonbase.nonspanning (h : M.IsNonbase K) : M.Nonspanning K := by
  obtain ⟨B, hB, hBK⟩ := h.exists_findiff
  rw [← not_spanning_iff h.subset_ground]
  exact fun hK ↦ h.not_isBase <| hB.isBase_of_spanning_of_finDiff hK hBK

lemma isNonbase_iff_encard [M.RankFinite] (hKE : K ⊆ M.E) :
    M.IsNonbase K ↔ K.encard = M.eRank ∧ ¬ M.IsBase K := by
  refine ⟨fun h ↦ ?_, fun ⟨hKr, hK⟩ ↦ ⟨hKE, hK, ?_⟩⟩
  · obtain ⟨B, hB, hBK⟩ := h.exists_findiff
    rw [← hBK.encard_eq_encard, and_iff_right hB.encard_eq_eRank]
    exact h.not_isBase
  obtain ⟨B, hB⟩ := M.exists_isBase
  exact ⟨B, hB, by rw [hB.finite.finDiff_iff_encard_eq, hKr, hB.encard_eq_eRank]⟩

lemma isNonbase_iff_not_isBase [M.RankFinite] (hKE : K ⊆ M.E) (hKcard : K.encard = M.eRank) :
    M.IsNonbase K ↔ ¬ M.IsBase K := by
  rw [isNonbase_iff_encard hKE, and_iff_right hKcard]
