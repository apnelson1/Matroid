module

public import Matroid.ForMathlib.Geometry.PolygonalPath.Basic
public import Matroid.ForMathlib.Topology.Path

/-!
# Closed polygonal paths that are simple

`PolygonalPath.IsSimpleLoop` is the closed counterpart of `PolygonalPath.IsSimple`: the path
traverses each of its points once, apart from returning to its starting point at the end. It is the
parametrized notion `InjOn P.toPath (Ico 0 1)`. The polygon dictionary relates it to the
base-point-free notion `Polygon.IsSimple`.

## Main definitions

* `PolygonalPath.IsSimpleLoop`

## Main statements

* `PolygonalPath.isSimpleLoop_cons_iff`, `PolygonalPath.isSimpleLoop_append_iff` : the recursions
  for prepending and concatenating closed simple paths.
* `PolygonalPath.IsSimpleLoop.existsUnique_edge` : a non-vertex point of the image lies on a unique
  segment. The closed half of the hypothesis of `PolygonalPath.exists_nhds_inter_toSet_eq`.
-/

@[expose] public section

open Set Function unitInterval

namespace PolygonalPath

variable {α : Type*} [AddCommGroup α] [Module ℝ α] [TopologicalSpace α] [ContinuousSMul ℝ α]
  [ContinuousAdd α] {x y b : α}

omit [AddCommGroup α] [Module ℝ α] [TopologicalSpace α] [ContinuousSMul ℝ α]
  [ContinuousAdd α] in
lemma ext_vertices {P Q : PolygonalPath x y} (h : P.vertices = Q.vertices) : P = Q := by
  induction P with
  | nil x =>
    cases Q with
    | nil => rfl
    | cons a b Q => simp at h
  | @cons a b y P ih =>
    cases Q with
    | nil => simp at h
    | @cons _ c _ Q =>
      simp only [vertices_cons, List.cons.injEq] at h
      replace h := h.2
      have hbc : b = c := by
        have hh := congrArg List.head? h
        simpa using hh
      subst c
      congr
      exact ih h

/-- A closed polygonal path is *closed simple* if it traverses each of its points exactly once,
apart from returning to its starting point at the end. -/
def IsSimpleLoop (P : PolygonalPath x x) : Prop := P.toPath.IsSimpleLoop

@[simp] lemma isSimpleLoop_cast_self {x' : α} (P : PolygonalPath x x) (h : x = x') :
    (P.cast h h).IsSimpleLoop ↔ P.IsSimpleLoop := by
  subst x'
  rfl

lemma isSimpleLoop_iff_injOn (P : PolygonalPath x x) :
    P.IsSimpleLoop ↔ InjOn P.toPath (Ico 0 1) := Iff.rfl

@[simp] lemma not_isSimpleLoop_nil : ¬ (nil x).IsSimpleLoop := by
  simp [IsSimpleLoop]

@[simp] lemma not_isSimpleLoop_direct : ¬ (direct x x).IsSimpleLoop := by
  simp [IsSimpleLoop]

lemma IsSimpleLoop.length_pos {P : PolygonalPath x x} (h : P.IsSimpleLoop) : 0 < P.length := by
  cases P with
  | nil => simp at h
  | cons => simp

private lemma IsSimpleLoop.first_ne_second {P : PolygonalPath b x}
    (h : (cons x b P).IsSimpleLoop) : x ≠ b := by
  intro hxb
  subst b
  let q := squishLeft half
  have hq : q ∈ Ico (0 : I) 1 :=
    ⟨by simp [q], squishLeft_le_half half |>.trans_lt half_lt_one⟩
  have hval : (cons x x P).toPath 0 = (cons x x P).toPath q := by
    cases P with
    | nil => simp [q, squishLeft, toPath]
    | cons => rw [toPath_cons (by simp)]; simp [q, Path.trans_squishLeft]
  have heq := h (by simp) hq hval
  have hq0 : q ≠ 0 := by
    intro hq0
    apply half_ne_zero
    apply squishLeft_injective
    simpa [q] using hq0
  exact hq0 heq.symm

private lemma isSimpleLoop_cons_iff_aux {P : PolygonalPath b x} (hxb : x ≠ b) :
    (cons x b P).IsSimpleLoop ↔
      P.IsSimple ∧ Disjoint (segment ℝ x b \ {b}) (P.toSet \ {x}) := by
  have hpos : 0 < P.length := by
    cases P with
    | nil => simp_all
    | cons => simp
  rw [IsSimpleLoop, toPath_cons hpos]
  change InjOn ((Path.segment x b).trans P.toPath) (Ico 0 1) ↔ _
  rw [Path.trans_injOn_ico_iff, Path.range_segment, ← P.toSet_eq_range_toPath,
    Path.segment_injective, injective_toPath_iff]
  simp [hxb, hpos]

lemma IsSimpleLoop.not_isTrivial {P : PolygonalPath x x} (h : P.IsSimpleLoop) :
    ¬ P.IsTrivial := by
  intro htriv
  cases P with
  | nil => simp at h
  | @cons x b _ P =>
    exact h.first_ne_second (htriv b (by simp [P.first_mem_vertices])).symm

/-- Prepending a segment to a simple path closes it up into a simple closed path exactly when the
segment meets the path only at its two endpoints. This is `isSimple_cons_iff` with `{b}` replaced
by `{x, b}`, and is the case `A = direct x b` of `isSimpleLoop_append_iff`. -/
lemma isSimpleLoop_cons_iff {P : PolygonalPath b x} :
    (cons x b P).IsSimpleLoop ↔ x ≠ b ∧ P.IsSimple ∧ segment ℝ x b ∩ P.toSet ⊆ {x, b} := by
  constructor
  · intro h
    have hxb := h.first_ne_second
    obtain ⟨hP, hdj⟩ := (isSimpleLoop_cons_iff_aux hxb).mp h
    refine ⟨hxb, hP, ?_⟩
    rintro u ⟨huS, huP⟩
    by_cases hux : u = x
    · simp [hux]
    by_cases hub : u = b
    · simp [hub]
    exact (hdj.notMem_of_mem_left ⟨huS, hub⟩ ⟨huP, hux⟩).elim
  · rintro ⟨hxb, hP, hinter⟩
    apply (isSimpleLoop_cons_iff_aux hxb).mpr
    refine ⟨hP, ?_⟩
    rw [Set.disjoint_left]
    rintro u ⟨huS, hub⟩ ⟨huP, hux⟩
    have hu := hinter ⟨huS, huP⟩
    rcases hu with rfl | hu
    · exact hux rfl
    · subst u
      exact hub rfl

/-- A closed path is simple exactly when it is the union of two simple arcs meeting precisely at
their two shared endpoints. Note the right-hand side is symmetric in `A` and `B`, which is where
base-point independence comes from. -/
lemma isSimpleLoop_append_iff {A : PolygonalPath x y} {B : PolygonalPath y x} (hxy : x ≠ y) :
    (A.append B).IsSimpleLoop ↔ A.IsSimple ∧ B.IsSimple ∧ A.toSet ∩ B.toSet = {x, y} := by
  cases A with
  | nil => exact (hxy rfl).elim
  | @cons x b y A =>
    rw [cons_append, isSimpleLoop_cons_iff, isSimple_cons_iff, isSimple_append_iff,
      toSet_append, toSet_cons]
    constructor
    · rintro ⟨hxb, ⟨hA, hB, hAB⟩, hS⟩
      refine ⟨⟨hxb, hA, ?_⟩, hB, Set.Subset.antisymm ?_ ?_⟩
      · rintro u ⟨huS, huA⟩
        have hu := hS ⟨huS, Or.inl huA⟩
        rcases hu with hux | hub
        · exfalso
          apply hxy
          exact hux.symm.trans <| hAB ⟨huA, hux ▸
            B.mem_toSet_of_mem_vertices B.last_mem_vertices⟩
        · exact hub
      · rintro u ⟨huA, huB⟩
        rcases huA with huS | huA
        · have hu := hS ⟨huS, Or.inr huB⟩
          rcases hu with hux | hub
          · exact Or.inl hux
          · exact Or.inr <| hub.trans <| hAB
              ⟨A.mem_toSet_of_mem_vertices A.first_mem_vertices, hub ▸ huB⟩
        · have huy : u = y := hAB ⟨huA, huB⟩
          exact Or.inr huy
      · intro u hu
        rcases hu with hux | huy
        · subst u
          exact ⟨Or.inl (left_mem_segment ℝ x b),
            B.mem_toSet_of_mem_vertices B.last_mem_vertices⟩
        · subst u
          exact ⟨Or.inr (A.mem_toSet_of_mem_vertices A.last_mem_vertices),
            B.mem_toSet_of_mem_vertices B.first_mem_vertices⟩
    · rintro ⟨⟨hxb, hA, hSA⟩, hB, hEq⟩
      refine ⟨hxb, ⟨hA, hB, ?_⟩, ?_⟩
      · rintro u ⟨huA, huB⟩
        have hu : u ∈ ({x, y} : Set α) := hEq ▸ ⟨Or.inr huA, huB⟩
        rcases hu with hux | huy
        · have hub : u = b := hSA ⟨hux ▸ left_mem_segment ℝ x b, huA⟩
          exact (hxb (hux.symm.trans hub)).elim
        · exact huy
      · rintro u ⟨huS, huAB⟩
        rcases huAB with huA | huB
        · have hub : u = b := hSA ⟨huS, huA⟩
          simp [hub]
        · have hu : u ∈ ({x, y} : Set α) := hEq ▸ ⟨Or.inl huS, huB⟩
          rcases hu with hux | huy
          · exact Or.inl hux
          · exact Or.inr <| hSA ⟨huS, huy ▸
              A.mem_toSet_of_mem_vertices A.last_mem_vertices⟩

lemma isSimpleLoop_append_comm {A : PolygonalPath x y} {B : PolygonalPath y x} :
    (A.append B).IsSimpleLoop ↔ (B.append A).IsSimpleLoop := by
  by_cases hxy : x = y
  · subst y
    cases A with
    | nil => simp
    | @cons x a _ A =>
      cases B with
      | nil => simp
      | @cons _ b _ B =>
        have hnA : ¬(cons x a A).IsSimple := by
          intro hA
          exact hA.ne (by simp) rfl
        have hnB : ¬(cons x b B).IsSimple := by
          intro hB
          exact hB.ne (by simp) rfl
        constructor
        · intro h
          have hs := (isSimpleLoop_cons_iff.mp h).2.1
          exact (hnB (isSimple_append_iff.mp hs).2.1).elim
        · intro h
          have hs := (isSimpleLoop_cons_iff.mp h).2.1
          exact (hnA (isSimple_append_iff.mp hs).2.1).elim
  · rw [isSimpleLoop_append_iff hxy, isSimpleLoop_append_iff (Ne.symm hxy)]
    constructor
    · rintro ⟨hA, hB, hEq⟩
      exact ⟨hB, hA, by simpa [inter_comm, pair_comm] using hEq⟩
    · rintro ⟨hB, hA, hEq⟩
      exact ⟨hA, hB, by simpa [inter_comm, pair_comm] using hEq⟩

lemma IsSimpleLoop.isSimple_of_append_left {A : PolygonalPath x y} {B : PolygonalPath y x}
    (hxy : x ≠ y) (h : (A.append B).IsSimpleLoop) : A.IsSimple :=
  (isSimpleLoop_append_iff hxy).mp h |>.1

lemma IsSimpleLoop.vertices_dropLast_nodup {P : PolygonalPath x x} (h : P.IsSimpleLoop) :
    P.vertices.dropLast.Nodup := by
  cases P with
  | nil => simp
  | @cons x b _ P =>
    have hP := (isSimpleLoop_cons_iff.mp h).2.1.vertices_nodup
    rw [vertices_cons, List.dropLast_cons_of_ne_nil P.vertices_ne_nil]
    rw [P.vertices_eq_concat] at hP
    rw [List.nodup_cons]
    have hpa := List.nodup_append'.mp hP
    exact ⟨fun hx => hpa.2.2 hx (by simp), hpa.1⟩

/-- A simple closed polygonal path has at least three segments: `direct x x` is excluded by
`not_isSimpleLoop_direct`, and a digon by the fact that its two segments coincide. -/
lemma IsSimpleLoop.three_le_length {P : PolygonalPath x x} (h : P.IsSimpleLoop) :
    3 ≤ P.length := by
  cases P with
  | nil => simp at h
  | @cons x b _ P =>
    obtain ⟨hxb, hP, -⟩ := isSimpleLoop_cons_iff.mp h
    cases P with
    | nil => exact (hxb rfl).elim
    | @cons b c _ P =>
      cases P with
      | nil =>
        let ql := squishLeft half
        let qr := squishRight half
        have hql : ql ∈ Ico (0 : I) 1 :=
          ⟨by simp [ql], squishLeft_le_half half |>.trans_lt half_lt_one⟩
        have hqr : qr ∈ Ico (0 : I) 1 := ⟨by simp [qr], squishRight_lt_one half_lt_one⟩
        have hv : (cons x b (direct b x)).toPath ql =
            (cons x b (direct b x)).toPath qr := by
          rw [toPath_cons (by simp), Path.trans_squishLeft, Path.trans_squishRight]
          simp [Path.segment_apply, AffineMap.lineMap_apply_module, half]
          module
        have heq := h hql hqr hv
        have hvals := congrArg Subtype.val heq
        simp [ql, qr, squishLeft, squishRight, half] at hvals
      | cons => simp

@[simp] lemma isSimpleLoop_reverse {P : PolygonalPath x x} :
    P.reverse.IsSimpleLoop ↔ P.IsSimpleLoop := by
  cases P with
  | nil => simp
  | @cons x b _ P =>
    rw [reverse, isSimpleLoop_append_comm, direct_append, isSimpleLoop_cons_iff,
      isSimpleLoop_cons_iff, isSimple_reverse, toSet_reverse]
    simp only [ne_eq]
    constructor
    · rintro ⟨hbx, hP, hsub⟩
      refine ⟨Ne.symm hbx, hP, ?_⟩
      simpa [segment_symm, inter_comm, pair_comm] using hsub
    · rintro ⟨hxb, hP, hsub⟩
      refine ⟨Ne.symm hxb, hP, ?_⟩
      simpa [segment_symm, inter_comm, pair_comm] using hsub

@[simp] lemma isSimpleLoop_subdivide_iff {P : PolygonalPath x x} {a : α} (ha : a ∈ P.toSet) :
    (P.subdivide ha).IsSimpleLoop ↔ P.IsSimpleLoop := by
  match P with
  | .nil _ =>
    simp only [toSet_nil, mem_singleton_iff] at ha
    subst a
    simp [subdivide, breakAt]
  | .cons _ v P =>
    rw [subdivide, breakAt]
    split
    next hau =>
      subst a
      simp
    next hau =>
      split
      next hauv =>
        have hua : x ≠ a := fun h => hau h.symm
        have huv : x ≠ v := by
          intro h
          subst v
          rw [openSegment_same] at hauv
          exact hua (mem_singleton_iff.mp hauv).symm
        have hav : a ≠ v := by
          intro h
          subst a
          exact huv (right_mem_openSegment_iff.mp hauv)
        have hinter : segment ℝ x a ∩ segment ℝ a v = {a} :=
          segment_inter_subsegments_eq_singleton huv hauv
        have hsplit := segment_union_eq_segment (openSegment_subset_segment ℝ x v hauv)
        have hsub₁ : segment ℝ x a ⊆ segment ℝ x v := hsplit ▸ subset_union_left
        have hsub₂ : segment ℝ a v ⊆ segment ℝ x v := hsplit ▸ subset_union_right
        simp only [direct_append, isSimpleLoop_cons_iff, isSimple_cons_iff, toSet_cons]
        constructor
        · rintro ⟨_, ⟨_, hP, haP⟩, huaP⟩
          refine ⟨huv, hP, ?_⟩
          rintro w ⟨hwuv, hwP⟩
          rw [← hsplit] at hwuv
          rcases hwuv with hwu | hwv
          · have hw : w ∈ ({x, a} : Set α) := huaP ⟨hwu, Or.inr hwP⟩
            rcases hw with hwu' | hwa
            · exact Or.inl hwu'
            · have hw' : w = v := haP ⟨hwa ▸ left_mem_segment ℝ a v, hwP⟩
              exact Or.inr hw'
          · exact Or.inr <| haP ⟨hwv, hwP⟩
        · rintro ⟨_, hP, huvP⟩
          refine ⟨hua, ⟨hav, hP, ?_⟩, ?_⟩
          · rintro w ⟨hwav, hwP⟩
            have hw : w ∈ ({x, v} : Set α) := huvP ⟨hsub₂ hwav, hwP⟩
            rcases hw with hwu | hwv
            · have : x = a := by
                simpa using (Set.ext_iff.mp hinter x).mp
                  ⟨hwu ▸ left_mem_segment ℝ x a, hwu ▸ hwav⟩
              exact (hua this).elim
            · exact hwv
          · rintro w ⟨hwua, hwrest⟩
            rcases hwrest with hwav | hwP
            · exact Or.inr <| (Set.ext_iff.mp hinter w).mp ⟨hwua, hwav⟩
            · have hw : w ∈ ({x, v} : Set α) := huvP ⟨hsub₁ hwua, hwP⟩
              rcases hw with hwu | hwv
              · exact Or.inl hwu
              · have : v = a := by
                  simpa using (Set.ext_iff.mp hinter v).mp
                    ⟨hwv ▸ hwua, right_mem_segment ℝ a v⟩
                exact (hav this.symm).elim
      next hauv =>
        have ha' : a ∈ P.toSet :=
          ((mem_toSet_cons_iff.mp ha).resolve_left hau).resolve_left hauv
        change (cons x v (P.subdivide ha')).IsSimpleLoop ↔ (cons x v P).IsSimpleLoop
        rw [isSimpleLoop_cons_iff, isSimple_subdivide_iff ha', toSet_subdivide]
        exact (isSimpleLoop_cons_iff (x := x) (b := v) (P := P)).symm

/-- A point of a simple closed path which is not a vertex lies on a unique segment. -/
lemma IsSimpleLoop.existsUnique_edge {P : PolygonalPath x x} {a : α} (h : P.IsSimpleLoop)
    (ha : a ∈ P.toSet) (hav : a ∉ P.vertices) : ∃! s ∈ P.edges, a ∈ segment ℝ s.1 s.2 := by
  match P with
  | .nil _ => exact (hav (by simpa using ha)).elim
  | .cons _ b Q =>
    obtain ⟨-, hQ, hinter⟩ := isSimpleLoop_cons_iff.mp h
    have hxV : x ∈ (cons x b Q).vertices := (cons x b Q).first_mem_vertices
    have hbV : b ∈ (cons x b Q).vertices := by simp [Q.first_mem_vertices]
    have hax : a ≠ x := fun hax => hav (hax.symm ▸ hxV)
    have hab : a ≠ b := fun hab => hav (hab.symm ▸ hbV)
    rw [toSet_cons] at ha
    rcases ha with haS | haQ
    · refine ⟨(x, b), ⟨by simp, haS⟩, ?_⟩
      rintro s ⟨hs, has⟩
      simp only [edges_cons, List.mem_cons] at hs
      rcases hs with rfl | hs
      · rfl
      · have haQ' := Q.segment_subset_toSet hs has
        have haends := hinter ⟨haS, haQ'⟩
        exact haends.elim (fun e => (hax e).elim) (fun e => (hab e).elim)
    · have havQ : a ∉ Q.vertices := fun haV => hav (by simp [haV])
      obtain ⟨s, ⟨hs, has⟩, hsuniq⟩ := hQ.existsUnique_edge haQ havQ
      refine ⟨s, ⟨by simp [hs], has⟩, ?_⟩
      rintro t ⟨ht, hat⟩
      simp only [edges_cons, List.mem_cons] at ht
      rcases ht with rfl | ht
      · have haends := hinter ⟨hat, haQ⟩
        exact haends.elim (fun e => (hax e).elim) (fun e => (hab e).elim)
      · exact hsuniq t ⟨ht, hat⟩

/-! ### The two edges at the base point

At the base point of a simple loop, the first and last edges are the two incident edges. -/

/-- At the base point of a simple loop the first tip is not the base point. -/
lemma IsSimpleLoop.firstTip_ne {P : PolygonalPath x x} (h : P.IsSimpleLoop) : P.firstTip ≠ x := by
  cases P with
  | nil => exact (not_isSimpleLoop_nil h).elim
  | cons a b Q => exact fun hbx ↦ (isSimpleLoop_cons_iff.mp h).1 hbx.symm

/-- At the base point of a simple loop the last tip is not the base point. -/
lemma IsSimpleLoop.lastTip_ne {P : PolygonalPath x x} (h : P.IsSimpleLoop) : P.lastTip ≠ x :=
  (isSimpleLoop_reverse.mpr h).firstTip_ne

/-- **The two edges at the base point of a simple loop are distinct.** -/
lemma IsSimpleLoop.firstTip_ne_lastTip {P : PolygonalPath x x} (h : P.IsSimpleLoop) :
    P.firstTip ≠ P.lastTip := by
  cases P with
  | nil => exact (not_isSimpleLoop_nil h).elim
  | cons x b Q =>
    obtain ⟨-, hQ, -⟩ := isSimpleLoop_cons_iff.mp h
    have hQlen : 2 ≤ Q.length := by
      have := h.three_le_length
      simp at this
      omega
    intro heq
    cases Q with
    | nil => simp at hQlen
    | cons b c R =>
      have hRpos : 0 < R.length := by
        simp at hQlen
        omega
      have hlast : (cons x b (cons b c R)).lastTip = R.lastTip := by
        rw [lastTip_cons (by simp), lastTip_cons hRpos]
      have hbR : b ∈ R.vertices := by
        have : b = R.lastTip := heq.trans hlast
        exact this ▸ R.fst_mem_vertices (mem_edges_lastTip hRpos)
      exact (List.nodup_cons.mp hQ.vertices_nodup).1 hbR

/-- **At the base point of a simple loop, only the first and last edges contain it.** The loop
analogue of `eq_first_edge_of_mem_segment`; the disjunction is irreducible, because both edges
genuinely end at the base point. -/
lemma IsSimpleLoop.eq_first_or_last_edge_of_mem_segment {P : PolygonalPath x x}
    (h : P.IsSimpleLoop) {s : α × α} (hs : s ∈ P.edges) (hxs : x ∈ segment ℝ s.1 s.2) :
    s = (x, P.firstTip) ∨ s = (P.lastTip, x) := by
  cases P with
  | nil => exact (not_isSimpleLoop_nil h).elim
  | cons x b Q =>
    obtain ⟨-, hQ, -⟩ := isSimpleLoop_cons_iff.mp h
    have hQpos : 0 < Q.length := by
      have := h.three_le_length
      simp at this
      omega
    simp only [edges_cons, List.mem_cons] at hs
    rcases hs with rfl | hsQ
    · exact Or.inl rfl
    · have hs_eq : s = (Q.lastTip, x) :=
        eq_last_edge_of_mem_segment hQ (mem_edges_lastTip hQpos) hsQ hxs
      exact Or.inr (hs_eq.trans (by rw [lastTip_cons hQpos]))

/-- A simple loop has no degenerate edge. -/
@[grind →]
lemma IsSimpleLoop.hasNondegenerateEdges {x : α} {P : PolygonalPath x x}
    (h : P.IsSimpleLoop) : P.HasNondegenerateEdges := by
  cases P with
  | nil => exact (not_isSimpleLoop_nil h).elim
  | cons a b Q =>
    obtain ⟨hne, hQ, _⟩ := isSimpleLoop_cons_iff.mp h
    exact hasNondegenerateEdges_cons.mpr ⟨hne, hQ.hasNondegenerateEdges⟩

end PolygonalPath
