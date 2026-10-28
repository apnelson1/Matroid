module

public import Matroid.ForMathlib.Topology.Crossing
public import Matroid.ForMathlib.Parity
public import Mathlib.Topology.Path
public import Mathlib.Data.Finset.Sort

/-!
# Boundary crossings of paths

A path with finite boundary contact and unique visits to crossing points has crossing parity
determined by its endpoint sides. Repeated tangencies are allowed. The carrier is Hausdorff;
the ambient space need not be.
-/

@[expose] public section

open Set Function TopologicalSpace Topology unitInterval Set.Notation Classical

variable {X : Type*} [TopologicalSpace X] {S U : Set X} {x y p : X}

section Cut

variable {P : Path x y} {T : Finset I} {n : ℕ} {g : Fin (n + 2) → I}

private lemma param_succ_mem_T {A : Type*} {T : Set A} {n : ℕ}
    {g : Fin (n + 2) → A} (hg : Injective g)
    (hcover : range g ⊆ T ∪ {g 0, g (Fin.last (n + 1))}) (i : Fin n) :
    g i.castSucc.succ ∈ T := by
  rcases hcover (mem_range_self (i.castSucc.succ)) with h | h
  · exact h
  rcases h with h | h
  · have he := congrArg Fin.val (hg h)
    simp at he
  · have he := congrArg Fin.val (hg h)
    simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_last] at he
    omega

private lemma param_succ_frontier (hgrange : range g = (T : Set I) ∪ {0, 1})
    (hg : StrictMono g) (hg0 : g 0 = 0) (hg1 : g (Fin.last (n + 1)) = 1)
    (hT : ∀ s : I, s ∈ T ↔ P s ∈ frontier U) (i : Fin n) :
    P (g i.castSucc.succ) ∈ frontier U := by
  apply (hT _).mp
  apply param_succ_mem_T hg.injective
  rw [hg0, hg1, hgrange]

private lemma piece_disjoint_frontier (hT : ∀ s : I, s ∈ T ↔ P s ∈ frontier U)
    (hg : StrictMono g) (hcover : (T : Set I) ⊆ range g) (k : Fin (n + 1)) :
    Disjoint (P '' Ioo (g k.castSucc) (g k.succ)) (frontier U) := by
  apply disjoint_left.mpr
  rintro _ ⟨s, ⟨hslo, hshi⟩, rfl⟩ hs
  obtain ⟨j, rfl⟩ := hcover ((hT s).mpr hs)
  exact (not_lt_of_ge (Fin.castSucc_lt_iff_succ_le.mp (hg.lt_iff_lt.mp hslo)))
    (hg.lt_iff_lt.mp hshi)

private lemma piece_subset_side (hT : ∀ s : I, s ∈ T ↔ P s ∈ frontier U)
    (hg : StrictMono g) (hgrange : range g = (T : Set I) ∪ {0, 1}) (k : Fin (n + 1)) :
    P '' Ioo (g k.castSucc) (g k.succ) ⊆ interior U ∨
      P '' Ioo (g k.castSucc) (g k.succ) ⊆ interior Uᶜ := by
  apply (isPreconnected_Ioo.image P P.continuous.continuousOn).disjoint_frontier_iff.mp
  exact piece_disjoint_frontier hT hg (by rw [hgrange]; exact subset_union_left) k

/-- The side of `interior U` on which the piece of the path between two consecutive cut points
lies. -/
private noncomputable def pieceIn (P : Path x y) (g : Fin (n + 2) → I) (k : Fin (n + 1)) :
    Bool :=
  if P '' Ioo (g k.castSucc) (g k.succ) ⊆ interior U then true else false

private lemma pieceIn_true_iff (k : Fin (n + 1)) :
    pieceIn (U := U) P g k = true ↔
      P '' Ioo (g k.castSucc) (g k.succ) ⊆ interior U := by
  unfold pieceIn
  by_cases h : P '' Ioo (g k.castSucc) (g k.succ) ⊆ interior U <;> simp [h]

private lemma pieceIn_false_iff (hT : ∀ s : I, s ∈ T ↔ P s ∈ frontier U)
    (hg : StrictMono g) (hgrange : range g = (T : Set I) ∪ {0, 1}) (k : Fin (n + 1)) :
    pieceIn (U := U) P g k = false ↔
      P '' Ioo (g k.castSucc) (g k.succ) ⊆ interior Uᶜ := by
  have hside := piece_subset_side (U := U) hT hg hgrange k
  constructor
  · intro h
    have hnot : ¬ (P '' Ioo (g k.castSucc) (g k.succ) ⊆ interior U) := by
      rw [← pieceIn_true_iff (P := P) (g := g) (k := k)]
      rw [h]
      simp
    exact hside.resolve_left hnot
  · intro h
    by_contra hc
    have htrue : pieceIn (U := U) P g k = true := by
      simpa using hc
    obtain ⟨s, hs⟩ := exists_between (hg (Fin.castSucc_lt_succ (i := k)))
    have hmem : P s ∈ P '' Ioo (g k.castSucc) (g k.succ) := ⟨s, hs, rfl⟩
    have hU : P s ∈ interior U := (pieceIn_true_iff (P := P) (g := g) (k := k)).mp htrue hmem
    exact (disjoint_compl_right.mono interior_subset interior_subset).notMem_of_mem_left hU (h hmem)

private lemma pieces_lt (hg : StrictMono g) (i : Fin n) :
    g (i.castSucc).castSucc < g (i.castSucc).succ ∧
      g (i.castSucc).succ < g (i.succ).succ := by
  constructor
  · exact hg Fin.castSucc_lt_succ
  · exact hg (by rw [Fin.lt_def]; simp only [Fin.val_castSucc, Fin.val_succ]; omega)

private lemma local_path_neighborhood {X : Type*} [TopologicalSpace X] {x y : X}
    {S : Set X} [T2Space ↥S] (P : Path x y) (hP : range P = S)
    {t : I} (ht : ∀ s, P s = P t → s = t) {W : Set I} (hW : W ∈ 𝓝 t) :
    ∃ V : Set X, IsOpen V ∧ P t ∈ V ∧ ∀ s : I, P s ∈ V → s ∈ W := by
  let Q : I → S := fun s ↦ ⟨P s, hP ▸ mem_range_self s⟩
  have hc : Continuous Q := P.continuous.subtype_mk _
  have he := hc.isClosedMap.eventually_nhds_fiber (Q t)
    (p := fun s ↦ s ∈ W) (by
      intro s hs
      have hst := ht s (congrArg Subtype.val hs)
      simpa [hst] using hW)
  obtain ⟨V, hVsub, hVopen, htV⟩ := mem_nhds_iff.mp he
  obtain ⟨O, hOopen, hOeq⟩ := IsInducing.subtypeVal.isOpen_iff.mp hVopen
  refine ⟨O, hOopen, ?_, ?_⟩
  · change Q t ∈ Subtype.val ⁻¹' O
    rwa [hOeq]
  · intro s hs
    have hsV : Q s ∈ V := by rwa [← hOeq]
    exact hVsub hsV s rfl

private lemma mem_closure_left_iff [T2Space ↥S] (hPrange : range P = S)
    (hPinj : InjOn P (P ⁻¹' frontier U))
    (hT : ∀ s : I, s ∈ T ↔ P s ∈ frontier U)
    (hg : StrictMono g) (hg0 : g 0 = 0) (hg1 : g (Fin.last (n + 1)) = 1)
    (hgrange : range g = (T : Set I) ∪ {0, 1}) (i : Fin n) :
    P (g (i.castSucc).succ) ∈ closure (S ∩ interior U) ↔
      pieceIn (U := U) P g i.castSucc = true ∨ pieceIn (U := U) P g i.succ = true := by
  obtain ⟨hga, hgb⟩ := pieces_lt (n := n) hg i
  have hmiddle := param_succ_frontier (U := U) hgrange hg hg0 hg1 hT i
  constructor
  · intro hc
    by_contra h
    simp only [not_or, Bool.not_eq_true] at h
    obtain ⟨hleft, hright⟩ := h
    obtain ⟨V, hVopen, hpV, hVsub⟩ := local_path_neighborhood P hPrange
      (fun s hs ↦ hPinj (by change P s ∈ frontier U; rw [hs]; exact hmiddle) hmiddle hs)
      (isOpen_Ioo.mem_nhds ⟨hga, hgb⟩)
    have hempty : ∀ x ∈ V, x ∈ S → x ∈ interior U → False := by
      intro x hxV hxS hxU
      rw [← hPrange] at hxS
      obtain ⟨s, rfl⟩ := hxS
      have hs := hVsub s hxV
      rcases lt_trichotomy s (g (i.castSucc).succ) with hlt | heq | hgt
      · have hmem : P s ∈ P '' Ioo (g (i.castSucc).castSucc) (g (i.castSucc).succ) :=
          ⟨s, mem_Ioo.mpr ⟨hs.1, hlt⟩, rfl⟩
        exact (disjoint_compl_right.mono interior_subset interior_subset).notMem_of_mem_left hxU
          ((pieceIn_false_iff (U := U) hT hg hgrange (i.castSucc)).mp hleft hmem)
      · subst heq
        exact disjoint_interior_frontier.notMem_of_mem_right hmiddle hxU
      · have hmem : P s ∈ P '' Ioo (g (i.succ).castSucc) (g (i.succ).succ) :=
          ⟨s, mem_Ioo.mpr ⟨hgt, hs.2⟩, rfl⟩
        exact (disjoint_compl_right.mono interior_subset interior_subset).notMem_of_mem_left hxU
          ((pieceIn_false_iff (U := U) hT hg hgrange (i.succ)).mp hright hmem)
    obtain ⟨x, hxV, hx⟩ := mem_closure_iff.mp hc V hVopen hpV
    exact hempty x hxV hx.1 hx.2
  · rintro (h | h)
    · have hp : P '' Ioo (g (i.castSucc).castSucc) (g (i.castSucc).succ) ⊆ interior U :=
        (pieceIn_true_iff (U := U) (P := P) (g := g) (k := i.castSucc)).mp h
      have hsub : P '' Ioo (g (i.castSucc).castSucc) (g (i.castSucc).succ) ⊆
          S ∩ interior U :=
        fun x hx => ⟨hPrange ▸ image_subset_range P _ hx, hp hx⟩
      have hb : P (g (i.castSucc).succ) ∈
          closure (P '' Ioo (g (i.castSucc).castSucc) (g (i.castSucc).succ)) := by
        have hmem : g (i.castSucc).succ ∈
            closure (Ioo (g (i.castSucc).castSucc) (g (i.castSucc).succ)) := by
          rw [closure_Ioo hga.ne]
          exact right_mem_Icc.mpr hga.le
        exact image_closure_subset_closure_image P.continuous ⟨_, hmem, rfl⟩
      exact closure_mono hsub hb
    · have hp : P '' Ioo (g (i.succ).castSucc) (g (i.succ).succ) ⊆ interior U :=
        (pieceIn_true_iff (U := U) (P := P) (g := g) (k := i.succ)).mp h
      have hsub : P '' Ioo (g (i.succ).castSucc) (g (i.succ).succ) ⊆ S ∩ interior U :=
        fun x hx => ⟨hPrange ▸ image_subset_range P _ hx, hp hx⟩
      have hb : P (g (i.castSucc).succ) ∈
          closure (P '' Ioo (g (i.succ).castSucc) (g (i.succ).succ)) := by
        have hmem : g (i.castSucc).succ ∈
            closure (Ioo (g (i.castSucc).succ) (g (i.succ).succ)) := by
          rw [closure_Ioo hgb.ne]
          exact left_mem_Icc.mpr hgb.le
        exact image_closure_subset_closure_image P.continuous ⟨_, hmem, rfl⟩
      exact closure_mono hsub hb

private lemma mem_closure_right_iff [T2Space ↥S] (hPrange : range P = S)
    (hPinj : InjOn P (P ⁻¹' frontier U))
    (hT : ∀ s : I, s ∈ T ↔ P s ∈ frontier U)
    (hg : StrictMono g) (hg0 : g 0 = 0) (hg1 : g (Fin.last (n + 1)) = 1)
    (hgrange : range g = (T : Set I) ∪ {0, 1}) (i : Fin n) :
    P (g (i.castSucc).succ) ∈ closure (S ∩ interior Uᶜ) ↔
      pieceIn (U := U) P g i.castSucc = false ∨ pieceIn (U := U) P g i.succ = false := by
  rw [mem_closure_left_iff (U := Uᶜ) hPrange (by simpa using hPinj) (by simpa using hT)
    hg hg0 hg1 hgrange i, pieceIn_true_iff, pieceIn_true_iff,
    ← pieceIn_false_iff (U := U) hT hg hgrange i.castSucc,
    ← pieceIn_false_iff (U := U) hT hg hgrange i.succ]

private lemma crossing_iff [T2Space ↥S] (hPrange : range P = S) (hPinj : InjOn P (P ⁻¹' frontier U))
    (hT : ∀ s : I, s ∈ T ↔ P s ∈ frontier U)
    (hg : StrictMono g) (hg0 : g 0 = 0) (hg1 : g (Fin.last (n + 1)) = 1)
    (hgrange : range g = (T : Set I) ∪ {0, 1}) (i : Fin n) :
    (P (g (i.castSucc).succ) ∈ closure (S ∩ interior U) ∧
        P (g (i.castSucc).succ) ∈ closure (S ∩ interior Uᶜ)) ↔
      pieceIn (U := U) P g i.castSucc ≠ pieceIn (U := U) P g i.succ := by
  rw [mem_closure_left_iff (U := U) hPrange hPinj hT hg hg0 hg1 hgrange i,
    mem_closure_right_iff (U := U) hPrange hPinj hT hg hg0 hg1 hgrange i]
  by_cases hl : pieceIn (U := U) P g i.castSucc <;>
    by_cases hr : pieceIn (U := U) P g i.succ <;> simp_all

private lemma pieceIn_eq_true_iff_endpoint_mem
    (hT : ∀ s : I, s ∈ T ↔ P s ∈ frontier U)
    (hg : StrictMono g) (hgrange : range g = (T : Set I) ∪ {0, 1})
    (k : Fin (n + 1)) {t : I}
    (ht : t ∈ closure (Ioo (g k.castSucc) (g k.succ)))
    (hf : P t ∉ frontier U) :
    pieceIn (U := U) P g k = true ↔ P t ∈ U := by
  rw [pieceIn_true_iff]
  exact (isPreconnected_Ioo.image P P.continuous.continuousOn).subset_interior_iff_of_mem_closure
    (piece_disjoint_frontier hT hg (by rw [hgrange]; exact subset_union_left) k)
    (image_closure_subset_closure_image P.continuous ⟨t, ht, rfl⟩) hf

end Cut

/-- A path with finite boundary intersection and unique visits to boundary points has crossing
parity equal to the discrepancy between its endpoint sides. -/
private theorem ncard_boundaryCrossings_mod_two_of_injOn_frontier [T2Space ↥S] (P : Path x y)
    (hPrange : range P = S) (hfin : (S ∩ frontier U).Finite)
    (hPinj : InjOn P (P ⁻¹' frontier U)) (hx : x ∉ frontier U) (hy : y ∉ frontier U) :
    (boundaryCrossings S U).ncard % 2 = if (x ∈ U ↔ y ∈ U) then 0 else 1 := by
  classical
  set T : Set I := {s | P s ∈ frontier U} with hTdef
  have hTmem : ∀ s : I, s ∈ T ↔ P s ∈ frontier U := fun s => Iff.rfl
  have hTsub : T ⊆ Ioo (0 : I) 1 := by
    intro s hs
    have hfr : P s ∈ frontier U := hs
    refine ⟨?_, ?_⟩
    · rcases eq_or_lt_of_le (show (0 : I) ≤ s from s.2.1) with h | h
      · have h0 : P (0 : I) ∈ frontier U := h ▸ hfr
        rw [P.source] at h0
        exact absurd h0 hx
      · exact h
    · rcases eq_or_lt_of_le (show s ≤ (1 : I) from s.2.2) with h | h
      · have h1 : P (1 : I) ∈ frontier U := h ▸ hfr
        rw [P.target] at h1
        exact absurd h1 hy
      · exact h
  have hTfin : T.Finite := by
    apply Set.Finite.of_finite_image
    · exact hfin.subset (by
        rintro _ ⟨s, hs, rfl⟩
        exact ⟨hPrange ▸ mem_range_self _, hs⟩)
    · exact hPinj
  set Tf : Finset I := hTfin.toFinset with hTfdef
  have hTfmem : ∀ s : I, s ∈ Tf ↔ P s ∈ frontier U := by
    intro s
    rw [hTfdef, hTfin.mem_toFinset]
    exact hTmem s
  set n : ℕ := hTfin.toFinset.card with hndef
  have h0not : (0 : I) ∉ hTfin.toFinset := fun h =>
    absurd (hTsub (hTfin.mem_toFinset.mp h)).1 (lt_irrefl 0)
  have h1not : (1 : I) ∉ hTfin.toFinset := fun h =>
    absurd (hTsub (hTfin.mem_toFinset.mp h)).2 (lt_irrefl 1)
  set G : Finset I := insert 0 (insert 1 hTfin.toFinset) with hGdef
  have h0not' : (0 : I) ∉ insert (1 : I) hTfin.toFinset := by simp [h0not]
  have hGcard : G.card = n + 2 := by
    rw [hGdef, Finset.card_insert_of_notMem h0not', Finset.card_insert_of_notMem h1not, hndef]
  set e : Fin (n + 2) ≃o ↥G := G.orderIsoOfFin hGcard with hedef
  set g : Fin (n + 2) → I := fun k => (e k : I) with hgdef
  have hgv : ∀ k, g k = ((e k : ↥G) : I) := fun k => rfl
  have hg : StrictMono g := fun a b h => e.strictMono h
  have hmem0 : (0 : I) ∈ G := by rw [hGdef]; exact Finset.mem_insert_self _ _
  have hmem1 : (1 : I) ∈ G := by
    rw [hGdef]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hg0 : g 0 = 0 := by
    have hmin : ∀ x : ↥G, e 0 ≤ x := by
      intro x
      obtain ⟨k, rfl⟩ := e.surjective x
      exact e.le_iff_le.mpr (Fin.zero_le k)
    have hle : g 0 ≤ (0 : I) := hmin ⟨0, hmem0⟩
    have hge : (0 : I) ≤ g 0 := (e 0).1.2.1
    exact le_antisymm hle hge
  have hg1 : g (Fin.last (n + 1)) = 1 := by
    have hmax : ∀ x : ↥G, x ≤ e (Fin.last (n + 1)) := by
      intro x
      obtain ⟨k, rfl⟩ := e.surjective x
      exact e.le_iff_le.mpr (Fin.le_last k)
    have hle : g (Fin.last (n + 1)) ≤ (1 : I) := (e (Fin.last (n + 1))).1.2.2
    have hge : (1 : I) ≤ g (Fin.last (n + 1)) := hmax ⟨1, hmem1⟩
    exact le_antisymm hle hge
  have hgrange : range g = (Tf : Set I) ∪ {0, 1} := by
    ext s
    constructor
    · rintro ⟨k, rfl⟩
      have hmem : ((e k : ↥G) : I) ∈ insert (0 : I) (insert 1 hTfin.toFinset) := (e k).2
      simp only [Finset.mem_insert] at hmem
      rcases hmem with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact Or.inl h
    · rintro (h | h | h)
      · have hmem : s ∈ insert (0 : I) (insert 1 hTfin.toFinset) :=
          Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h)
        refine ⟨e.symm ⟨s, hmem⟩, ?_⟩
        show ((e (e.symm ⟨s, hmem⟩) : ↥G) : I) = s
        simp
      · exact ⟨0, hg0.trans h.symm⟩
      · exact ⟨Fin.last (n + 1), hg1.trans h.symm⟩
  have h0T : (0 : I) ∉ (T : Set I) := fun h => absurd (hTsub h).1 (lt_irrefl 0)
  have h1T : (1 : I) ∉ (T : Set I) := fun h => absurd (hTsub h).2 (lt_irrefl 1)
  have hCross : boundaryCrossings S U =
      Set.range (fun i : {i : Fin n // pieceIn (U := U) P g i.castSucc ≠
          pieceIn (U := U) P g i.succ} => P (g (i.1.castSucc).succ)) := by
    ext p
    constructor
    · intro hp
      obtain ⟨hpS, hpfr⟩ := boundaryCrossings_subset S U hp
      have hpS' : p ∈ range P := hPrange.symm ▸ hpS
      obtain ⟨s, hs⟩ := hpS'
      have hsT : P s ∈ frontier U := by rw [hs]; exact hpfr
      have hsTf : s ∈ Tf := (hTfmem s).mpr hsT
      obtain ⟨j, hj⟩ : s ∈ range g := by
        rw [hgrange]
        exact Or.inl hsTf
      have hj0 : j ≠ 0 := by
        rintro rfl
        have hsz : s = 0 := by rw [← hj, hg0]
        exact h0T (hsz ▸ (hTmem s).mpr hsT)
      have hj1 : j ≠ Fin.last (n + 1) := by
        rintro rfl
        have hsz : s = 1 := by rw [← hj, hg1]
        exact h1T (hsz ▸ (hTmem s).mpr hsT)
      have hjval : 1 ≤ j.val := by
        rcases Nat.eq_zero_or_pos j.val with h | h
        · exact absurd (Fin.ext h) hj0
        · exact h
      have hjval' : j.val ≤ n := by
        rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp j.isLt) with h | h
        · omega
        · exact absurd (Fin.ext h) hj1
      have hje : (⟨j.val - 1, by omega⟩ : Fin n).castSucc.succ = j := by
        refine Fin.ext ?_
        simp only [Fin.val_succ, Fin.val_castSucc]
        omega
      have hpe : p = P (g ((⟨j.val - 1, by omega⟩ : Fin n).castSucc).succ) := by
        rw [← hs, ← hj, hje]
      rw [hpe] at hp
      exact ⟨⟨⟨j.val - 1, by omega⟩, (crossing_iff (U := U) hPrange hPinj hTfmem hg hg0
        hg1 hgrange ⟨j.val - 1, by omega⟩).mp ⟨hp.2.1, hp.2.2⟩⟩, hpe.symm⟩
    · rintro ⟨i, rfl⟩
      have hfront := param_succ_frontier (U := U) hgrange hg hg0 hg1 hTfmem i.1
      have hcr := (crossing_iff (U := U) hPrange hPinj hTfmem hg hg0 hg1 hgrange i.1).mpr
        i.2
      exact ⟨⟨hPrange ▸ mem_range_self _, hfront⟩, hcr.1, hcr.2⟩
  rw [hCross]
  have hinj : Function.Injective
      (fun i : {i : Fin n // pieceIn (U := U) P g i.castSucc ≠
        pieceIn (U := U) P g i.succ} => P (g (i.1.castSucc).succ)) := by
    intro a b hab
    have ha := param_succ_frontier (U := U) hgrange hg hg0 hg1 hTfmem a.1
    have hb := param_succ_frontier (U := U) hgrange hg hg0 hg1 hTfmem b.1
    have hkeq : a.1.castSucc.succ = b.1.castSucc.succ :=
      hg.injective (hPinj ha hb hab)
    refine Subtype.ext (Fin.ext ?_)
    have := congrArg (fun k : Fin (n + 2) => k.val) hkeq
    simp only [Fin.val_succ, Fin.val_castSucc] at this
    omega
  have hfirst : pieceIn (U := U) P g 0 = true ↔ x ∈ U := by
    suffices pieceIn (U := U) P g 0 = true ↔ P 0 ∈ U by simpa using this
    apply pieceIn_eq_true_iff_endpoint_mem hTfmem hg hgrange 0
    · rw [closure_Ioo (hg Fin.castSucc_lt_succ).ne]
      exact ⟨hg0.le, (hg Fin.castSucc_lt_succ).le.trans' hg0.ge⟩
    · rwa [P.source]
  have hlast : pieceIn (U := U) P g (Fin.last n) = true ↔ y ∈ U := by
    suffices pieceIn (U := U) P g (Fin.last n) = true ↔ P 1 ∈ U by simpa using this
    apply pieceIn_eq_true_iff_endpoint_mem hTfmem hg hgrange (Fin.last n)
    · rw [closure_Ioo (hg Fin.castSucc_lt_succ).ne]
      exact ⟨(hg Fin.castSucc_lt_succ).le.trans hg1.le, hg1.ge⟩
    · rwa [P.target]
  have hend : pieceIn (U := U) P g 0 = pieceIn (U := U) P g (Fin.last n) ↔
      (x ∈ U ↔ y ∈ U) := by
    rw [← hfirst, ← hlast]
    cases pieceIn (U := U) P g 0 <;> cases pieceIn (U := U) P g (Fin.last n) <;> simp
  rw [Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Bool.card_changes_mod_two]
  simp only [hend]

private theorem crossings_univ_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsOpen A) :
    boundaryCrossings univ (closure A) = frontier (closure A) := by
  have he : closure (interior (closure A)) = closure A :=
    isClosed_closure.closure_interior_subset.antisymm
      (closure_mono hA.subset_interior_closure)
  ext p
  simp only [boundaryCrossings, mem_ofPred_eq, univ_inter, he,
    isClosed_closure.isOpen_compl.interior_eq]
  constructor
  · exact fun h ↦ h.1
  · intro h
    refine ⟨h, ?_, ?_⟩
    · simpa only [closure_closure] using frontier_subset_closure h
    · exact (frontier_eq_closure_inter_closure (s := closure A) ▸ h).2

private theorem regularized_frontier {X : Type*} [TopologicalSpace X]
    {S U : Set X} [T1Space ↥S] (hf : (S ∩ frontier U).Finite) :
    frontier (closure ((Subtype.val : S → X) ⁻¹' interior U)) =
      Subtype.val ⁻¹' boundaryCrossings S U := by
  apply frontier_closure_preimage_interior_eq_boundaryCrossings
  have heq : (Subtype.val : S → X) ⁻¹' (S ∩ frontier U) =
      (Subtype.val : S → X) ⁻¹' frontier U := by
    ext q
    exact and_iff_right q.property
  have hfin : ((Subtype.val : S → X) ⁻¹' frontier U).Finite := by
    rw [← heq]
    exact hf.preimage Subtype.val_injective.injOn
  simpa only [Subtype.image_preimage_coe] using
    hfin.isDiscrete.image Topology.IsInducing.subtypeVal

/-- Finite boundary contact and unique visits to crossing points determine the parity of
crossings from the endpoint sides, allowing repeated tangencies. -/
theorem Path.ncard_boundaryCrossings_mod_two {X : Type*} [TopologicalSpace X]
    {S U : Set X} {x y : X} [T2Space ↥S] (P : Path x y)
    (hP : range P = S) (hf : (S ∩ frontier U).Finite)
    (hinj : InjOn P (P ⁻¹' boundaryCrossings S U))
    (hx : x ∉ frontier U) (hy : y ∉ frontier U) :
    (boundaryCrossings S U).ncard % 2 = if (x ∈ U ↔ y ∈ U) then 0 else 1 := by
  have hmem (t : I) : P t ∈ S := hP ▸ mem_range_self t
  have hxs : x ∈ S := P.source ▸ hmem 0
  have hys : y ∈ S := P.target ▸ hmem 1
  let Q : Path (⟨x, hxs⟩ : S) ⟨y, hys⟩ :=
    { toFun := fun t ↦ ⟨P t, hmem t⟩
      continuous_toFun := P.continuous.subtype_mk _
      source' := Subtype.ext P.source
      target' := Subtype.ext P.target }
  let V : Set S := closure (Subtype.val ⁻¹' interior U)
  have hfront : frontier V = Subtype.val ⁻¹' boundaryCrossings S U :=
    regularized_frontier hf
  have hcross : boundaryCrossings univ V = Subtype.val ⁻¹' boundaryCrossings S U :=
    (crossings_univ_closure (isOpen_interior.preimage continuous_subtype_val)).trans hfront
  have hQrange : range Q = univ := by
    apply eq_univ_of_forall
    intro q
    have hq : q.val ∈ range P := by rw [hP]; exact q.property
    obtain ⟨t, ht⟩ := hq
    exact ⟨t, Subtype.ext ht⟩
  have hQfin : (univ ∩ frontier V).Finite := by
    rw [univ_inter, hfront]
    exact (boundaryCrossings_finite hf).preimage Subtype.val_injective.injOn
  have hQinj : InjOn Q (Q ⁻¹' frontier V) := by
    intro s hs t ht he
    apply hinj
    · change Q s ∈ frontier V at hs
      rw [hfront] at hs
      exact hs
    · change Q t ∈ frontier V at ht
      rw [hfront] at ht
      exact ht
    · exact congrArg Subtype.val he
  have hQx : (⟨x, hxs⟩ : S) ∉ frontier V := by
    rw [hfront]
    exact fun h ↦ hx h.1.2
  have hQy : (⟨y, hys⟩ : S) ∉ frontier V := by
    rw [hfront]
    exact fun h ↦ hy h.1.2
  have hside {p : X} (hp : p ∈ S) (hpU : p ∉ frontier U) :
      (⟨p, hp⟩ : S) ∈ V ↔ p ∈ U := by
    have hv : V = Subtype.val ⁻¹' closure (S ∩ interior U) := by
      dsimp only [V]
      rw [IsInducing.subtypeVal.closure_eq_preimage_closure_image,
        image_preimage_eq_inter_range, Subtype.range_val, inter_comm]
    rw [hv]
    constructor
    · intro h
      have hc : p ∈ closure U := closure_mono (inter_subset_right.trans interior_subset) h
      exact interior_subset (closure_sdiff_frontier U ▸ ⟨hc, hpU⟩)
    · intro h
      have hi : p ∈ interior U :=
        closure_sdiff_frontier U ▸ ⟨subset_closure h, hpU⟩
      exact subset_closure ⟨hp, hi⟩
  have he := ncard_boundaryCrossings_mod_two_of_injOn_frontier Q hQrange hQfin hQinj hQx hQy
  rw [hcross, ncard_preimage_of_injective_subset_range Subtype.val_injective
    (by rw [Subtype.range_val]; exact (boundaryCrossings_subset S U).trans inter_subset_left),
    hside hxs hx, hside hys hy] at he
  exact he
