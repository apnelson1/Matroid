import Mathlib.Topology.CWComplex.Classical.Graph
import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Matroid.Graph.Planarity.Topology.Circuit
import Matroid.Graph.Forest
import Matroid.ForMathlib.Analysis.Normed.Module.Connected

open Metric Set Graph Topology.RelCWComplex Topology.CWComplex Function Set.Notation

-- def finOneHomeo (K : Type*) [TopologicalSpace K] : (Fin 1 → K) ≃ₜ K :=
--   Homeomorph.funUnique (Fin 1) K

namespace Topology.RelCWComplex

variable {E ι : Type*} [TopologicalSpace E] {K C D : Set E} [CWComplex K] {n m : ℕ} {x : E}
  {u v : cell K 0} {e f : cell K 1}

@[simp]
lemma map_target_eq (e : cell K n) : (map n e).target = openCell n e :=
  (map n e).image_source_eq_target.symm.trans <| source_eq n e ▸ rfl

@[simps! apply symm_apply source]
def mapOne (e : cell K 1) : PartialEquiv E ℝ :=
  (map 1 e).symm.transEquiv (Homeomorph.funUnique (Fin 1) ℝ)

@[simp]
lemma mapOne_target (e : cell K 1) : (mapOne e).target = ball 0 1 := by
  ext x
  simp only [mapOne, PartialEquiv.transEquiv_target, PartialEquiv.symm_target, source_eq,
    mem_preimage, mem_ball, dist_zero_right, Real.norm_eq_abs]
  change ‖(fun _ : Fin 1 ↦ x)‖ < 1 ↔ |x| < 1
  simp

lemma isPathConnected_openCell (e : cell K n) : IsPathConnected (openCell n e) :=
  (isPathConnected_ball zero_lt_one).image' ((continuousOn n e).mono ball_subset_closedBall)

@[simp]
lemma openCell_nonempty (e : cell K n) : (openCell n e).Nonempty := by
  use (map n e 0), 0, by simp

def openCellStratum (K : Set E) [RelCWComplex K D] (n : ℕ) : Set E := ⋃ e : cell K n, openCell n e

@[simp]
lemma mem_openCellStratum_iff : x ∈ openCellStratum K n ↔ ∃ e : cell K n, x ∈ openCell n e := by
  simp [openCellStratum]

lemma openCell_subset_openCellStratum (e : cell K n) : openCell n e ⊆ openCellStratum K n :=
  fun _ ↦ mem_iUnion_of_mem e

lemma openCellStratum_disjoint_openCell_of_ne_dim (hmn : m ≠ n) (e : cell K n) :
    Disjoint (openCellStratum K m) (openCell n e) := by
  rw [openCellStratum, disjoint_iUnion_left]
  exact fun _ ↦ disjoint_openCell_of_ne (by simp [Sigma.ext_iff, hmn])

lemma disjoint_openCellStratum_of_ne (hmn : m ≠ n) :
    Disjoint (openCellStratum K m) (openCellStratum K n) := by
  simp_rw [openCellStratum, disjoint_iUnion_left, disjoint_iUnion_right]
  exact fun e f ↦ disjoint_openCell_of_ne (by simp [Sigma.ext_iff, hmn])

lemma iUnion_openCellStratum_eq_complex : ⋃ n : ℕ, openCellStratum K n = K := by
  simpa [openCellStratum] using CWComplex.iUnion_openCell_eq_complex (C := K)

lemma disjoint_preimage_subtypeval_openCell_one {i j : cell K 1} (hij : i ≠ j) :
    Disjoint ((Subtype.val : ⋃ e : cell K 1, openCell 1 e → E) ⁻¹' openCell 1 i)
      ((Subtype.val : ⋃ e : cell K 1, openCell 1 e → E) ⁻¹' openCell 1 j) := by
  rw [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_notMem]
  intro z hz
  rw [Set.mem_inter_iff, Set.mem_preimage, Set.mem_preimage] at hz
  rcases hz with ⟨hzi, hzj⟩
  have hdis := disjoint_openCell_of_ne (by simp [Sigma.ext_iff, hij] :
    (⟨1, i⟩ : Σ n, cell K n) ≠ ⟨1, j⟩)
  rw [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_notMem] at hdis
  exact hdis z.val (Set.mem_inter hzi hzj)

lemma not_isCircuit_range_subset_openCell_one {f : Circle → E} (hf : IsEmbedding f)
    (hr : range f ⊆ openCell 1 e) : False := by
  /- Embed `Circle` into `ℝ` through the open `1`-cell chart and apply `not_isCircuit_real`. -/
  let g : Circle → ℝ := fun x ↦ (map 1 e).symm (f x) 0
  have htarget (x : Circle) : f x ∈ (map 1 e).target := by
    rw [← (map 1 e).image_source_eq_target, source_eq]
    simpa [openCell] using hr (mem_range_self x)
  have hg_cont : Continuous g :=
    (continuous_apply 0).comp <| (continuousOn_symm 1 e).comp_continuous hf.continuous htarget
  have hg_inj : Injective g := by
    intro x y hxy
    have hfin : (map 1 e).symm (f x) = (map 1 e).symm (f y) := by
      ext i
      fin_cases i
      exact hxy
    exact hf.injective <| (map 1 e).symm.injOn (htarget x) (htarget y) hfin
  exact not_isCircuit_real (range g) ⟨g, (hg_cont.isClosedEmbedding hg_inj).isEmbedding, rfl⟩

lemma exists_Ioo_subset_image_Ioo_of_continuousOn_injOn {a t b : unitInterval}
    {g : unitInterval → ℝ} (hat : a < t) (htb : t < b) (hg_cont : ContinuousOn g (Icc a b))
    (hg_inj : InjOn g (Icc a b)) : ∃ l r, l < g t ∧ g t < r ∧ Ioo l r ⊆ g '' Ioo a b := by
  have hab : a ≤ b := hat.le.trans htb.le
  have ht_mem : t ∈ Icc a b := ⟨hat.le, htb.le⟩
  obtain hmono | hanti := hg_cont.strictMonoOn_of_injOn_Icc' hab hg_inj
  · exact ⟨g a, g b, hmono (left_mem_Icc.mpr hab) ht_mem hat,
      hmono ht_mem (right_mem_Icc.mpr hab) htb, intermediate_value_Ioo hab hg_cont⟩
  exact ⟨g b, g a, hanti ht_mem (right_mem_Icc.mpr hab) htb,
    hanti (left_mem_Icc.mpr hab) ht_mem hat, intermediate_value_Ioo' hab hg_cont⟩

lemma linePoint_mem_openCell_one (e : cell K 1) {r : ℝ} (hr : |r| < 1) :
    map 1 e (fun _ ↦ r) ∈ openCell 1 e := ⟨fun _ ↦ r, by simp [hr], rfl⟩

lemma linePoint_coord_one (e : cell K 1) {r : ℝ} (hr : |r| < 1) :
    (map 1 e).symm (map 1 e (fun _ ↦ r)) 0 = r := by
  suffices (map 1 e).symm (map 1 e (fun _ ↦ r)) = (fun _ ↦ r) by rw [this]
  refine PartialEquiv.left_inv _ ?_
  simp [hr, source_eq]

lemma map_zero_notMem_openCell_one (u : cell K 0) (e : cell K 1) : map 0 u 0 ∉ openCell 1 e :=
  disjoint_openCell_of_ne (by simp [Sigma.ext_iff] : (⟨0, u⟩ : Σ n, cell K n) ≠ ⟨1, e⟩)
    |>.notMem_of_mem_left (map_zero_mem_openCell 0 u)

variable [T2Space E]

lemma disjoint_closedCell_openCell_sameDim_of_ne {e f : cell K n} (h : e ≠ f) :
    Disjoint (closedCell n e) (openCell n f) := by
  rw [← cellFrontier_union_openCell_eq_closedCell, disjoint_union_left]
  refine ⟨?_, disjoint_openCell_of_ne (by simp [Sigma.ext_iff, h] : (_ : Σ n, _) ≠ _)⟩
  exact (disjoint_skeletonLT_openCell le_rfl).mono (cellFrontier_subset_skeletonLT n e) Subset.rfl

lemma disjoint_closedCell_openCell_of_lt {e : cell K n} {f : cell K m} (hmn : n < m) :
    Disjoint (closedCell n e) (openCell m f) :=
  (disjoint_skeleton_openCell (by exact_mod_cast hmn)).mono_left (closedCell_subset_skeleton n e)

@[simp]
lemma not_disjoint_iff_eq_of_le (e : cell K n) (f : cell K m) (hmn : n ≤ m) :
    ¬ Disjoint (closedCell n e) (openCell m f) ↔ ∃ (h : n = m), e = h ▸ f := by
  rw [← not_iff_comm]
  simp only [not_exists]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain hlt | rfl := lt_or_eq_of_le hmn
    · exact (disjoint_skeleton_openCell (by exact_mod_cast hlt)).mono_left
        (closedCell_subset_skeleton n e)
    simp only [forall_const, ← ne_eq] at h
    rw [← cellFrontier_union_openCell_eq_closedCell, disjoint_union_left]
    refine ⟨?_, disjoint_openCell_of_ne (by simp [Sigma.ext_iff, h] : (_ : Σ n, _) ≠ _)⟩
    exact (disjoint_skeletonLT_openCell le_rfl).mono (cellFrontier_subset_skeletonLT n e) Subset.rfl
  rintro rfl rfl
  rw [disjoint_comm, disjoint_of_subset_iff_left_eq_empty (openCell_subset_closedCell n e)] at h
  exact (openCell_nonempty e).ne_empty h

@[simp]
lemma closedCell_diff_openCell_eq_cellFrontier (e : cell K n) :
    closedCell n e \ openCell n e = cellFrontier n e := by
  rw [← cellFrontier_union_openCell_eq_closedCell]
  exact Set.union_diff_cancel_right
    ((disjoint_skeletonLT_openCell le_rfl).mono_left (cellFrontier_subset_skeletonLT n e)).le_bot

lemma isOpen_openCell_skeleton (e : cell K n) : IsOpen (↑(skeleton K n) ↓∩ openCell n e) := by
  let A : Set E := ↑(skeleton K n) \ openCell n e
  have hpre : (↑(skeleton K n) ↓∩ openCell n e)ᶜ =
      ((fun x : (skeleton K n : Set E) ↦ (x : E)) ⁻¹' A) := by
    simp [A, Set.ext_iff]
  rw [← isClosed_compl_iff, hpre]
  refine CWComplex.isClosed_of_disjoint_openCell_or_isClosed_inter_closedCell
    (diff_subset.trans (skeleton K n).subset_complex) (fun m hm j ↦ ?_)
    |>.preimage continuous_subtype_val
  by_cases hmn : m ≤ n
  · right
    rw [diff_inter_right_comm, inter_diff_assoc]
    obtain h | h := em (Disjoint (closedCell m j) (openCell n e))
    · rw [h.sdiff_eq_left]
      exact (skeleton K ↑n).closed.inter isClosed_closedCell
    obtain ⟨rfl, rfl⟩ := (not_disjoint_iff_eq_of_le j e hmn).mp h
    rw [closedCell_diff_openCell_eq_cellFrontier j]
    exact (skeleton K ↑m).closed.inter isClosed_cellFrontier
  · exact Or.inl <| (disjoint_skeleton_openCell (by simpa using hmn)).mono_left diff_subset

lemma openCellStratum_subset_skeleton : openCellStratum K n ⊆ skeleton K n :=
  iUnion_subset (openCell_subset_skeleton n)

lemma disjoint_skeletonLT_openCellStratum {n : ℕ∞} (hnm : n ≤ m) :
    Disjoint (skeletonLT K n : Set E) (openCellStratum K m) := by
  rw [openCellStratum, disjoint_iUnion_right]
  exact fun _ ↦ disjoint_skeletonLT_openCell hnm

lemma iUnion_openCellStratum_eq_skeletonLT (n : ℕ∞) :
    ⋃ (m : ℕ) (_ : (m : ℕ∞) < n), openCellStratum K m = skeletonLT K n := by
  simpa [openCellStratum] using CWComplex.iUnion_openCell_eq_skeletonLT (C := K) n

lemma iUnion_openCellStratum_eq_skeleton (n : ℕ∞) :
    ⋃ (m : ℕ) (_ : (m : ℕ∞) < n + 1), openCellStratum K m = skeleton K n := by
  simpa [openCellStratum] using CWComplex.iUnion_openCell_eq_skeleton (C := K) n

lemma isClosed_preimage_openCellStratum (e : cell K n) :
    IsClosed (((↑) : openCellStratum K n → E) ⁻¹' openCell n e) := by
  have hpre_closed : ((↑) : openCellStratum K n → E) ⁻¹' openCell n e =
      ((↑) : openCellStratum K n → E) ⁻¹' closedCell n e := by
    ext x
    refine ⟨(openCell_subset_closedCell n e ·), fun hxcl ↦ ?_⟩
    obtain ⟨f, hxf⟩ := mem_openCellStratum_iff.mp x.prop
    obtain rfl | hef := eq_or_ne e f
    · exact hxf
    exact (disjoint_closedCell_openCell_sameDim_of_ne hef |>.notMem_of_mem_left hxcl) hxf |>.elim
  exact hpre_closed ▸ isClosed_closedCell.preimage continuous_subtype_val

lemma isOpen_preimage_openCellStratum (e : cell K n) :
    IsOpen (((↑) : openCellStratum K n → E) ⁻¹' openCell n e) := by
  let f : openCellStratum K n → skeleton K n := fun x ↦ ⟨x, openCellStratum_subset_skeleton x.prop⟩
  have hf : Continuous f := continuous_subtype_val.subtype_mk _
  exact (isOpen_openCell_skeleton e).preimage hf

lemma isClopen_preimage_openCellStratum (e : cell K n) :
    IsClopen (((↑) : openCellStratum K n → E) ⁻¹' openCell n e) :=
  ⟨isClosed_preimage_openCellStratum e, isOpen_preimage_openCellStratum e⟩

lemma pathComponentIn_openCellStratum {v : E} {e : cell K n}
    (hv : v ∈ openCell n e) : pathComponentIn (openCellStratum K n) v = openCell n e := by
  let T : Set E := openCellStratum K n
  have hclopen : IsClopen ((Subtype.val : T → E) ⁻¹' openCell n e) :=
    isClopen_preimage_openCellStratum e
  ext x
  refine ⟨fun ⟨P, hP⟩ => ?_, fun hx => ?_⟩
  · let PT : unitInterval → T := fun t => ⟨P t, hP t⟩
    have hPT : Continuous PT := P.continuous.subtype_mk hP
    let A : Set unitInterval := PT ⁻¹' ((Subtype.val : T → E) ⁻¹' openCell n e)
    have hAclopen : IsClopen A := hclopen.preimage hPT
    have h0 : (0 : unitInterval) ∈ A := by
      dsimp [A, PT]
      simpa [P.source] using hv
    have hAuniv : A = Set.univ := hAclopen.eq_univ ⟨0, h0⟩
    have h1 : (1 : unitInterval) ∈ A := by
      simp [hAuniv]
    dsimp [A, PT] at h1
    simpa [P.target] using h1
  have hcell : IsPathConnected (openCell n e) := isPathConnected_openCell e
  obtain ⟨p, hp⟩ := hcell.joinedIn v hv x hx
  exact ⟨p, fun t ↦ openCell_subset_openCellStratum e (hp t)⟩

theorem exists_openCell_zero_subset_of_isCircuit (hC : IsCircuit C)
    (h : C ⊆ skeleton K 1) : ∃ v : cell K 0, openCell 0 v ⊆ C := by
  by_contra! hv
  have hvert (v : cell K 0) (y : E) (hy : y ∈ C) : y ∉ openCell 0 v := by
    intro hmem
    rw [openCell_zero_eq_singleton, mem_singleton_iff] at hmem
    subst hmem
    have hsub : openCell 0 v ⊆ C := by
      rw [openCell_zero_eq_singleton]
      exact singleton_subset_iff.mpr hy
    exact hv v hsub
  have hr : C ⊆ openCellStratum K 1 := by
    intro y hy
    obtain ⟨m, hm, e, he⟩ := exists_mem_openCell_of_mem_skeleton.mp (h hy)
    simp only [Nat.cast_le_one] at hm
    obtain rfl | rfl : m = 0 ∨ m = 1 := by omega
    · exact (hvert e y hy he).elim
    exact openCell_subset_openCellStratum e he
  have hconn := hC.isPathConnected
  obtain ⟨f, hf, rfl⟩ := hC
  obtain ⟨n, hn, e, he⟩ := exists_mem_openCell_of_mem_skeleton.mp (h (mem_range_self 1))
  simp only [Nat.cast_le_one] at hn
  obtain rfl : n = 1 := by
    by_contra! hn1
    obtain rfl : n = 0 := by omega
    grind
  have := pathComponentIn_openCellStratum he ▸ hconn.subset_pathComponentIn ⟨1, rfl⟩ hr
  exact not_isCircuit_range_subset_openCell_one hf this

theorem subset_of_not_disjoint_of_path (P : Path (map 0 u 0) (map 0 v 0))
    (hP : Injective P) (h : range P ⊆ skeleton K 1) (hdisj : ¬ Disjoint (range P) (openCell 1 e)) :
    openCell 1 e ⊆ range P := by
  obtain ⟨x, hxP, hxe⟩ := not_disjoint_iff.mp hdisj; clear hdisj
  let A : Set (openCell 1 e) := {z | (z : E) ∈ range P}
  have hopen_preimage : IsOpen {s : unitInterval | P s ∈ openCell 1 e} := by
    let PS : unitInterval → (skeleton K 1 : Set E) := fun s ↦ ⟨P s, h (mem_range_self s)⟩
    change IsOpen (PS ⁻¹' (↑(skeleton K 1) ↓∩ openCell 1 e))
    exact (isOpen_openCell_skeleton e).preimage <| P.continuous.subtype_mk _
  have htarget_of_mem_openCell {y : E} (hy : y ∈ openCell 1 e) : y ∈ (map 1 e).target := by
    rwa [← (map 1 e).image_source_eq_target, source_eq]
  let coord : openCell 1 e → ℝ := fun z ↦ (map 1 e).symm (z : E) 0
  have hcoord_cont : Continuous coord :=
    (continuous_apply 0).comp <| (continuousOn_symm 1 e).comp_continuous continuous_subtype_val
      (fun z ↦ htarget_of_mem_openCell z.prop)
  have hA_open : IsOpen A := by
    refine isOpen_iff_forall_mem_open.mpr fun z ⟨t, ht⟩ ↦ ?_
    have ht_openCell : P t ∈ openCell 1 e := ht ▸ z.prop
    have ht0 : t ≠ 0 :=
      fun h ↦ map_zero_notMem_openCell_one u e (by simpa [Path.source, h] using ht_openCell)
    have ht1 : t ≠ 1 :=
      fun h ↦ map_zero_notMem_openCell_one v e (by simpa [Path.target, h] using ht_openCell)
    have h0t : (0 : unitInterval) < t := lt_of_le_of_ne bot_le ht0.symm
    have ht1' : t < (1 : unitInterval) := lt_of_le_of_ne le_top ht1
    obtain ⟨l, r, htlr, hlr_sub⟩ := (mem_nhds_iff_exists_Ioo_subset' ⟨0, h0t⟩ ⟨1, ht1'⟩).mp
      (hopen_preimage.mem_nhds ht_openCell)
    obtain ⟨a, hla, hat⟩ := exists_between htlr.1
    obtain ⟨b, htb, hbr⟩ := exists_between htlr.2
    clear h0t ht1' ht0 ht1 ht_openCell hopen_preimage hxe hxP h htlr
    have hIcc_openCell : Icc a b ⊆ {s : unitInterval | P s ∈ openCell 1 e} :=
      fun s hs ↦ hlr_sub ⟨hla.trans_le hs.1, hs.2.trans_lt hbr⟩
    have hg_cont : ContinuousOn ((mapOne e) ∘ P) (Icc a b) :=
      (continuous_apply 0).comp_continuousOn <| (continuousOn_symm 1 e).comp
        P.continuous.continuousOn (fun s hs ↦ htarget_of_mem_openCell (hIcc_openCell hs))
    have hg_inj : InjOn ((mapOne e) ∘ P) (Icc a b) := ((mapOne_source e ▸ (mapOne e).injOn).comp
      hP.injOn <| MapsTo.congr hlr_sub fun _ ↦ congrFun rfl) |>.mono (Icc_subset_Ioo hla hbr)
    obtain ⟨L, R, hL, hR, hLR_image⟩ :=
      exists_Ioo_subset_image_Ioo_of_continuousOn_injOn hat htb hg_cont hg_inj
    clear hg_cont hg_inj hat htb hla hbr hlr_sub
    let B : Set (openCell 1 e) := coord ⁻¹' Ioo L R
    refine ⟨B, fun y hyB ↦ ?_, isOpen_Ioo.preimage hcoord_cont, by
      simp only [comp_apply, mapOne_apply, Fin.isValue] at hL hR; grind⟩
    obtain ⟨s, hsIoo, hgs⟩ := hLR_image hyB
    refine ⟨s, ?_⟩
    rw [← (map 1 e).right_inv (htarget_of_mem_openCell (hIcc_openCell ⟨hsIoo.1.le, hsIoo.2.le⟩)),
      ← (map 1 e).right_inv (htarget_of_mem_openCell y.prop)]
    congr 1
    ext i
    fin_cases i
    exact hgs
  haveI : PreconnectedSpace (openCell 1 e) :=
    isPreconnected_iff_preconnectedSpace.mp (isPathConnected_openCell e).isConnected.isPreconnected
  have hA_univ : A = univ := IsClopen.eq_univ ⟨(isCompact_range P.continuous).isClosed.preimage
    continuous_subtype_val, hA_open⟩ ⟨⟨x, hxe⟩, hxP⟩
  exact fun y hy ↦ (show (⟨y, hy⟩ : openCell 1 e) ∈ A by simp [hA_univ])

theorem path_to_walk (P : Path (map 0 u 0) (map 0 v 0)) (h : range P ⊆ skeleton K 1) :
    ∃ W, (OneSkeletonGraph K).IsWalk W ∧ W.first = u ∧ W.last = v := by

  sorry

/- Cycle & Jordan curve correspondence

  Given a CW complex `K`, a subset of `K` is a jordan curve iff it is a cycle of its one skeleton.
-/
theorem cycle_iff_jordan_curve (hCK : C ⊆ skeleton K 1) :
    IsCircuit C ↔ ∃ C' : WList _ _, (OneSkeletonGraph K).IsCyclicWalk C' ∧
      ⋃ (e : E(OneSkeletonGraph K)), closedCell 1 e.val = C := by
  refine ⟨fun hC ↦ ?_, fun ⟨C', hC', hC''⟩ ↦ ?_⟩
  · obtain ⟨v, hv⟩ := exists_openCell_zero_subset_of_isCircuit hC hCK
    rw [openCell_zero_eq_singleton, singleton_subset_iff] at hv

    sorry
  subst C

  sorry


variable [CWComplex (univ : Set E)]
    (h_max_two : ∀ e : cell (univ : Set E) 1, ∀ x y z : cell (univ : Set E) 2,
      closedCell 1 e ⊆ cellFrontier 2 x ∩ cellFrontier 2 y ∩ cellFrontier 2 z → z = x ∨ z = y)
    (h_no_dangling : ∀ e : cell (univ : Set E) 1, ∃ x : cell (univ : Set E) 2,
      closedCell 1 e ⊆ cellFrontier 2 x)

def CWComplex.DualGraph : Graph (cell (univ : Set E) 2) (cell (univ : Set E) 1) where
  vertexSet := univ
  edgeSet := univ
  IsLink e x y := closedCell 1 e ⊆ cellFrontier 2 x ∩ cellFrontier 2 y
  isLink_symm e he x y h := by grind
  eq_or_eq_of_isLink_of_isLink e x y z w h1 h2 := by
    simp only [subset_inter_iff, and_imp] at h1 h2 h_max_two
    exact h_max_two e z w x h2.1 h2.2 h1.1
  left_mem_of_isLink e x y h := mem_univ _
  edge_mem_iff_exists_isLink e := by simp [h_no_dangling]
