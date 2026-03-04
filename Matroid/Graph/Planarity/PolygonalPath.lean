import Mathlib.Analysis.InnerProductSpace.PiL2 -- inefficient import
import Mathlib.Topology.UniformSpace.Path
import Mathlib.Topology.Separation.Connected
import Mathlib.Geometry.Polygon.Basic -- inefficient import
import Matroid.ForMathlib.List
import Matroid.Graph.Planarity.Path

universe u
variable {α β : Type u} {a b c x y z w : α} {C L : List α} {X Y : Set α} {N : ℕ}

open Set Function TopologicalSpace Topology Metric Nat unitInterval

lemma segment_union_eq_segment {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E] {x y z : E}
    (hz : z ∈ segment 𝕜 x y) : segment 𝕜 x z ∪ segment 𝕜 z y = segment 𝕜 x y := by
  simp only [segment_eq_image, mem_image, mem_Icc] at hz ⊢
  obtain ⟨t, ht, rfl⟩ := hz
  let f := fun (θ : 𝕜) ↦ (1 - θ) • x + θ • y
  suffices (f ∘ (· * t)) '' Icc 0 1 ∪ (f ∘ (· + t) ∘ (· * (1 - t))) '' Icc 0 1 = f '' Icc 0 1 by
    convert this using 3
    · simp only [smul_add, smul_smul, ← add_assoc, ← add_smul, comp_apply, f]
      ring_nf
    · simp only [smul_add, smul_smul, add_assoc, ← add_smul, comp_apply, f]
      ring_nf
  simp_rw [image_comp]
  rw [image_mul_right_Icc (by positivity) ht.1, image_mul_right_Icc (by positivity) (by linarith)]
  simp only [zero_mul, one_mul, image_add_const_Icc, zero_add, sub_add_cancel, ← image_union]
  congr
  exact Icc_union_Icc_eq_Icc ht.1 ht.2

lemma segment_diff_endpoints {𝕜 : Type*} {E : Type*} [Ring 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E] {x y : E} [DenselyOrdered 𝕜]
    [Module.IsTorsionFree 𝕜 E] (hxy : x ≠ y) : segment 𝕜 x y \ {x, y} = openSegment 𝕜 x y := by
  ext z
  simp only [mem_diff, mem_insert_iff, mem_singleton_iff, not_or, ← ne_eq]
  refine ⟨fun ⟨h, hzx, hzy⟩ ↦ mem_openSegment_of_ne_left_right hzx.symm hzy.symm h, fun h ↦ ?_⟩
  use openSegment_subset_segment _ _ _ h, ?_, ?_ <;> rintro rfl <;> simp [hxy] at h

lemma frontier_connectedComponentIn {α : Type*} [TopologicalSpace α] [LocallyConnectedSpace α]
    {S : Set α} {a : α} (hS : IsClosed S) (ha : a ∉ S) :
    frontier (connectedComponentIn Sᶜ a) ⊆ S := by
  rintro z ⟨hzc, hzi⟩
  by_contra! hzS
  rw [hS.isOpen_compl.connectedComponentIn.interior_eq] at hzi
  refine (hzi <| (isPreconnected_connectedComponentIn.subset_closure
    ((connectedComponentIn Sᶜ a).subset_insert z) ?_).subset_connectedComponentIn
    (Or.inr <| mem_connectedComponentIn ha) ?_ (mem_insert z ..)).elim
  · simp only [insert_subset_iff, hzc, true_and]
    exact subset_closure
  simp only [insert_subset_iff, mem_compl_iff, hzS, not_false_eq_true, true_and]
  exact connectedComponentIn_subset Sᶜ a

inductive PolygonalPath : α → α → Type (u+1) where
| direct (x y : α) : PolygonalPath x y
| cons (a b : α) {c} (as : PolygonalPath b c) : PolygonalPath a c

namespace PolygonalPath

variable (P : PolygonalPath x y) (Q : PolygonalPath y z) (L : List α)
open List

def ofList (x : α) (L : List α) (y : α) : PolygonalPath x y :=
  match L with
  | [] => direct x y
  | a :: as => cons x a (ofList a as y)

-- Get all vertices including start and end
@[simp]
def vertices : ∀ {x y : α}, PolygonalPath x y → List α
  | a, b, direct _ _ => [a, b]
  | _, _, cons a _ as => a :: as.vertices

lemma two_le_vertices_length  : 2 ≤ P.vertices.length := by
  induction P with
  | direct _ _ => simp [vertices]
  | cons _ _ as ih =>
    simp only [vertices, length_cons, reduceLeDiff]
    omega

@[simp]
lemma vertices_ne_nil : P.vertices ≠ [] := by
  refine ne_nil_of_length_pos ?_
  have := P.two_le_vertices_length
  omega

@[simp]
lemma vertices_head? : P.vertices.head? = some x := by
  induction P with
  | direct a b => simp
  | cons a b as ih => simp

@[simp]
lemma vertices_getLast? : P.vertices.getLast? = some y := by
  induction P with
  | direct a b => simp
  | cons a b as ih => simp [List.getLast?_cons, ih]

@[simp]
lemma ofList_vertices (x : α) (L : List α) (y : α) : (ofList x L y).vertices = x :: L ++ [y] := by
  induction L generalizing x y with
  | nil => simp [ofList]
  | cons a as ih => simp [ofList, ih]

lemma first_mem_vertices : x ∈ P.vertices := by
  induction P with
  | direct x y => simp
  | cons a b as ih => simp

lemma vertices_eq_cons : P.vertices = x :: P.vertices.tail := by
  induction P with
  | direct x y => simp
  | cons a b as ih => simp

lemma last_mem_vertices : y ∈ P.vertices := by
  induction P with
  | direct x y => simp
  | cons a b as ih => simp [ih]

lemma vertices_eq_concat : P.vertices = P.vertices.dropLast ++ [y] := by
  induction P with
  | direct x y => simp
  | cons a b as ih =>
    rwa [vertices, List.dropLast_cons_of_ne_nil (by simp), List.cons_append, List.cons_inj_right]

def vPairs : ∀ {x y : α}, PolygonalPath x y → List (α × α)
  | _, _, direct a b => [(a, b)]
  | _, _, cons a b as => (a, b) :: as.vPairs

lemma vPairs_eq_zip : P.vPairs = P.vertices.zip P.vertices.tail := by
  induction P with
  | direct x y => simp [vPairs]
  | cons a b as ih =>
    simp only [vPairs, ih, vertices, tail_cons]
    nth_rw 4 [vertices_eq_cons]
    rw [zip_cons_cons]

-- Get the list of internal vertices (excluding start and end)
@[simp]
def internal : ∀ {x y : α}, PolygonalPath x y → List α
  | _, _, direct a b => []
  | _, _, cons _ b as => b :: as.internal

@[simp]
lemma cons_internal_concat : x :: (P.internal ++ [y]) = P.vertices := by
  induction P with
  | direct a b => simp
  | cons a b as ih => simpa

@[simp]
lemma cons_internal : x :: P.internal = P.vertices.dropLast := by
  induction P with
  | direct a b => simp
  | cons a b as ih => simp [ih, dropLast_cons_of_ne_nil]

@[simp]
lemma internal_concat : P.internal ++ [y] = P.vertices.tail := by
  induction P with
  | direct a b => simp
  | cons a b as ih => simp [dropLast_append_getLast?]

@[simp]
lemma ofList_internal (x : α) (L : List α) (y : α) :
    (ofList x L y).internal = L := by
  induction L generalizing x y with
  | nil => simp [ofList]
  | cons a as ih => simp [ofList, ih]

-- Append two polygonal paths
def append : ∀ {x y z : α}, PolygonalPath x y → PolygonalPath y z → PolygonalPath x z
  | _, _, _, direct x y, p => cons x y p
  | _, _, _, cons x w as, p => cons x w (as.append p)

@[simp]
lemma append_vertices : (P.append Q).vertices = P.vertices ++ Q.vertices.tail := by
  induction P with
  | direct x y =>
    rw [← cons_internal_concat]
    simp only [append, internal, cons_append, internal_concat, vertices, nil_append]
  | cons x w as ih => simp [append, ih]

@[simp]
lemma append_internal : (P.append Q).internal = P.internal ++ y :: Q.internal := by
  induction P with
  | direct x y => simp [append]
  | cons x w as ih => simp only [append, internal, cons_append, ih]

def trivial : Prop := ∀ z ∈ P.vertices, x = z

lemma trivial.first_eq_last (h : P.trivial) : x = y := h y P.last_mem_vertices

lemma trivial.of_cons (h : (cons a x P).trivial) : P.trivial := by
  intro z hz
  obtain rfl := h x (by simp [P.first_mem_vertices])
  exact h z (by simp [hz])

lemma trivial.vertices_eq_replicate (h : P.trivial) : ∃ n : ℕ, P.vertices = List.replicate n x := by
  induction P with
  | direct x y => use 2, by simp [h.first_eq_last]
  | cons a b as ih =>
    obtain ⟨n, hn⟩ := ih h.of_cons
    use n + 1
    obtain rfl := h b (by simp [as.first_mem_vertices])
    simp only [vertices, hn]
    rfl

section Path
variable [AddCommGroup α] [Module ℝ α] [TopologicalSpace α] [ContinuousAdd α] [ContinuousSMul ℝ α]

-- Convert to a Path
noncomputable def toPath : ∀ {x y : α}, PolygonalPath x y → Path x y
  | _, _, direct x y => Path.segment x y
  | _, _, cons x w as => (Path.segment x w).trans as.toPath

def toSet : Set α := Set.range (P.toPath)

lemma toSet_eq_biUnion : P.toSet = ⋃ s ∈ P.vPairs, segment ℝ s.1 s.2 := by
  unfold toSet
  induction P with
  | direct x y => simp [toPath, vPairs_eq_zip]
  | cons x w as ih =>
    simp only [toPath, Path.trans_range, Path.range_segment, ih, ← internal_concat, internal,
      cons_append, vPairs_eq_zip]
    simp

@[simp]
lemma toSet_direct : (direct x y).toSet = segment ℝ x y := by
  simp [toSet, toPath]

@[simp]
lemma toSet_cons : (cons a x P).toSet = segment ℝ a x ∪ P.toSet := by
  simp [toSet, toPath, Path.trans_range]

lemma toSet_compact [IsTopologicalAddGroup α] : IsCompact (P.toSet) := by
  simp only [toSet_eq_biUnion]
  induction P.vPairs with
  | nil => simp
  | cons head tail ih =>
    simp only [mem_cons, iUnion_iUnion_eq_or_left]
    apply IsCompact.union _ ih
    rw [← convexHull_pair]
    apply Set.Finite.isCompact_convexHull
    simp

lemma toSet_isClosed [IsTopologicalAddGroup α] [T2Space α] : IsClosed (P.toSet) :=
  P.toSet_compact.isClosed

lemma vertices_subset_toSet {x} (hx : x ∈ P.vertices) : x ∈ P.toSet := by
  induction P with
  | direct x y =>
    simp only [vertices, mem_cons, not_mem_nil, or_false] at hx
    obtain rfl | rfl := hx <;> rw [toSet_direct]
    · exact left_mem_segment ℝ x y
    · exact right_mem_segment ..
  | cons a b as ih =>
    simp only [vertices, mem_cons] at hx
    obtain rfl | hx := hx
    · simp [left_mem_segment]
    simp [ih hx]

lemma toSet_nonempty : P.toSet.Nonempty := ⟨x, P.vertices_subset_toSet P.first_mem_vertices⟩

lemma toSet_isConnected : IsConnected (P.toSet) := by
  refine ⟨P.toSet_nonempty, ?_⟩
  rw [toSet, ← image_univ]
  exact isPreconnected_univ.image P.toPath P.toPath.continuous.continuousOn

lemma toSet_infinite_of_nontrivial [T1Space α] (h : P.toSet.Nontrivial) : P.toSet.Infinite :=
  (P.toSet_isConnected).isPreconnected.infinite_of_nontrivial h

noncomputable def breakAt {x y : α} (P : PolygonalPath x y) {a} (ha : a ∈ P.toSet) :
    PolygonalPath x a × PolygonalPath a y :=
  match P with
  | .direct x y => (direct x a, direct a y)
  | .cons u v vs => by
    classical
    if hauv : a ∈ segment ℝ u v then exact (direct u a, cons a v vs) else
    simp only [toSet_cons, mem_union, hauv, false_or] at ha
    let P' := vs.breakAt ha
    exact (cons u v P'.1, P'.2)

lemma break_toSet (P : PolygonalPath x y) {a} (ha : a ∈ P.toSet) :
    let P' := P.breakAt ha; P'.1.toSet ∪ P'.2.toSet = P.toSet := by
  induction P with
  | direct _ _ =>
    simp only [toSet_eq_biUnion, vertices, tail_cons, zip_cons_cons, zip_nil_right, mem_cons,
      not_mem_nil, or_false, iUnion_iUnion_eq_left, breakAt, vPairs_eq_zip] at ha ⊢
    exact segment_union_eq_segment ha
  | cons x v vs ih =>
    simp only [toSet_cons, mem_union] at ha
    by_cases hauv : a ∈ segment ℝ x v
    · simp [breakAt, hauv, ↓reduceDIte, toSet_direct, toSet_cons]
      rw [← union_assoc, segment_union_eq_segment hauv]
    replace ih := by simpa using ih (ha.resolve_left hauv)
    simp [breakAt, hauv, union_assoc, ih]

/-- `simple` is a predicate on `PolygonalPath` that asserts the associated path is injective;
that is, the path does not pass through the same point more than once.
Further, it disallows the degenerate case of a path having same vertex more than once.
For example, the path `[x, x]` is not simple, although it is not self-intersecting. -/
def simple : Prop := Injective P.toPath

@[simp] lemma direct_simple : (direct x y).simple ↔ x ≠ y := by
  simp [simple, toPath]

lemma simple.cons_iff : (cons a x P).simple ↔ a ≠ x ∧ P.simple ∧
    Disjoint (segment ℝ a x \ {x}) P.toSet := by
  simp [simple, toPath, Path.trans_injective_iff, Path.range_segment, toSet]

lemma simple.of_cons (h : (cons a x P).simple) : P.simple := by
  rw [simple.cons_iff] at h
  tauto

lemma simple.ne (h : P.simple) : x ≠ y := by
  simpa using mt <| h (a₁ := 0) (a₂ := 1)

lemma simple.ne' (h : P.simple) : y ≠ x := by
  simpa using mt <| h (a₁ := 1) (a₂ := 0)

variable {P : PolygonalPath x y}

lemma simple.vertex_nodup (h : P.simple) : P.vertices.Nodup := by
  induction P with
  | direct x y => simp_all
  | cons a b as ih =>
    obtain ⟨hab, hP, hdj⟩ := (simple.cons_iff _).mp h
    have := hdj.notMem_of_mem_left (a := a) (by simp [hab, left_mem_segment ℝ a b])
    simp only [vertices, nodup_cons, ih hP, and_true]
    contrapose! this
    exact as.vertices_subset_toSet this

lemma simple.unique_segment (h : P.simple) (ha : a ∈ P.toSet) (hav : a ∉ P.vertices) :
    ∃! s ∈ P.vPairs, a ∈ segment ℝ s.1 s.2 := by
  induction P with
  | direct x y =>
    simp only [toSet_direct, vPairs_eq_zip, vertices, tail_cons, zip_cons_cons, zip_nil_right,
      mem_cons, not_mem_nil, or_false] at ha ⊢
    use (x, y)
    simpa
  | cons u v vs ih =>
    simp only [toSet_cons, mem_union, vertices, mem_cons, not_or, ← ne_eq, cons_iff, vPairs_eq_zip,
      tail_cons] at ha hav h ⊢
    obtain ⟨huvne, hvssimple, hdj⟩ := h
    obtain ⟨haune, havsv⟩ := hav
    replace ih := (ih hvssimple · havsv)
    simp_rw [← vs.cons_internal_concat]
    simp only [internal_concat, zip_cons_cons, mem_cons]
    rw [← vs.vertices_eq_cons, ← vs.vPairs_eq_zip]
    by_cases havs : a ∈ vs.toSet
    · obtain ⟨h1, ⟨h21, h22⟩, h3⟩ := ih havs
      refine ⟨h1, ⟨Or.inr h21, h22⟩, ?_⟩
      rintro ⟨b, c⟩ ⟨(⟨rfl, rfl⟩ | hbc), habc⟩
      · simp only at h22 habc
        obtain rfl := by simpa [habc] using hdj.notMem_of_mem_right havs
        exact (havsv vs.first_mem_vertices).elim
      exact h3 _ ⟨hbc, habc⟩
    replace ha := ha.resolve_right havs
    use (u, v)
    simp only [true_or, ha, and_self, and_imp, forall_eq_or_imp, imp_self, Prod.forall,
      Prod.mk.injEq, true_and]
    rintro b c hbc habc
    absurd havs
    simp only [toSet_eq_biUnion, mem_iUnion, exists_prop, Prod.exists]
    use b, c

section ClosedSimple
variable {P : PolygonalPath x x}

def closedSimple (P : PolygonalPath x x) : Prop := InjOn P.toPath (Ico 0 1)

@[simp]
lemma closedSimple.not_direct : ¬ (direct x x).closedSimple := by
  intro h
  simpa [Subtype.ext_iff, toPath] using h (x₁ := 0) (x₂ := ⟨1/2, by constructor <;> linarith⟩)
    (by simp) (by simp [← coe_lt_one]; norm_num)

@[simp]
lemma closedSimple.not_trivial (h : P.closedSimple) : ¬ P.trivial := by
  match P with
  | .direct x _ => simp at h
  | .cons a b as =>
    let half : I := ⟨1/2, by constructor <;> linarith⟩
    have := by simpa [Subtype.ext_iff, half] using (h (x₁ := 0) (x₂ := half) (by simp)
      (by simp [← coe_lt_one]; norm_num))
    simp only [trivial, vertices, mem_cons, forall_eq_or_imp, true_and, not_forall]
    use b, as.first_mem_vertices
    simpa [toPath, Path.trans_apply] using this

lemma closedSimple.of_cons_simple {P : PolygonalPath x y} (h : P.simple)
    (hdj : Disjoint (openSegment ℝ y x) P.toSet) : (cons y x P).closedSimple := by
  intro s hs t ht hst
  simp only [toPath, Path.trans_apply, one_div, Path.segment_apply] at hst
  have H : ∀ (s t : ℝ) (hsle : s ≤ 2⁻¹) (htle : ¬ t ≤ 2⁻¹) (hsIco : s ∈ Ico 0 1)
    (htIco : t ∈ Ico 0 1), (AffineMap.lineMap y x) (2 * s) = P.toPath ⟨2 * t - 1, by
    rw [two_mul_sub_one_mem_iff]; simp [htIco.2.le]; linarith [htIco.1]⟩ → s = t := by
    intro s t hsle htle hsIco htIco hst
    generalize_proofs _ htI at hst
    have := hdj.notMem_of_mem_right (by use ⟨2 * t - 1, htI⟩)
    rw [← hst, openSegment_eq_image_lineMap] at this
    simp only [mem_image, mem_Ioo, AffineMap.lineMap_eq_lineMap_iff, h.ne.symm, false_or,
      exists_eq_right, ofNat_pos, mul_pos_iff_of_pos_left, not_and_or, not_lt] at this
    obtain hs1 | hs1 := this
    · obtain rfl := hs1.antisymm hsIco.1
      simp only [mul_zero, AffineMap.lineMap_apply_zero, ← P.toPath.target] at hst
      have := by simpa [Subtype.ext_iff] using h hst
      linarith [htIco.2]
    obtain rfl : s = 2⁻¹ := by linarith
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_inv_cancel₀,
      AffineMap.lineMap_apply_one, ← P.toPath.source] at hst
    have := by simpa [Subtype.ext_iff] using h hst
    linarith
  rw [Subtype.ext_iff]
  split_ifs at hst with hs2 ht2 ht2
  · simpa [h.ne.symm] using hst
  · exact H s.val t.val hs2 ht2 hs ht hst
  · exact H t.val s.val ht2 hs2 ht hs hst.symm |>.symm
  simpa using h hst

lemma closedSimple.cons_simple (h : P.closedSimple) :
    ∃ b P', P = cons x b P' ∧ P'.simple ∧ Disjoint (openSegment ℝ x b) P'.toSet := by
  match P with
  | .direct x _ => simp at h
  | .cons a b as =>
  have has : as.simple := by
    rw [closedSimple, toPath, Path.injOn_ico_iff_injOn_ioc] at h
    refine (Path.segment a b).injective_right_iff_trans_injOn as.toPath |>.mp ?_
    exact h.mono <| (Icc_subset_Ioc_iff le_one').mpr ⟨zero_lt_half, le_one'⟩
  refine ⟨b, as, rfl, has, ?_⟩
  rw [closedSimple, toPath, Path.trans_injOn_ico_iff] at h
  obtain ⟨hP, hQ, hdj⟩ := h
  simp only [Path.range_segment] at hdj
  rwa [← disjoint_sdiff_comm, diff_diff, union_singleton, segment_diff_endpoints has.ne.symm] at hdj

lemma closedSimple_iff_cons_simple (P : PolygonalPath x x) : P.closedSimple ↔ ∃ b P',
    P = cons x b P' ∧ P'.simple ∧ Disjoint (openSegment ℝ x b) P'.toSet ∧
    (cons x b P').closedSimple := by
  refine ⟨fun h ↦ ?_, fun ⟨_, _, heq, _, _, hP'c⟩ ↦ heq ▸ hP'c⟩
  obtain ⟨b, P', rfl, hP', hdj⟩ := h.cons_simple
  exact ⟨b, P', rfl, hP', hdj, h⟩

lemma closedSimple.unique_segment (h : P.closedSimple) (ha : a ∈ P.toSet) (hav : a ∉ P.vertices) :
    ∃! s ∈ P.vPairs, a ∈ segment ℝ s.1 s.2 := by
  obtain ⟨b, P', rfl, hP', hdj⟩ := h.cons_simple
  obtain ⟨hax, haP'⟩ := by simpa [← ne_eq] using hav
  obtain ⟨hab, -⟩ := by
    rw [P'.vertices_eq_cons] at haP'
    simpa [← ne_eq] using haP'
  obtain ha | ha := by simpa using ha
  · refine ⟨(x, b), ⟨by simp [vPairs], ha⟩, fun s' ⟨hs', hs'h⟩ ↦ ?_⟩
    simp only [vPairs, mem_cons] at hs'
    refine hs'.resolve_right fun hs' ↦ hdj.notMem_of_mem_left (mem_openSegment_of_ne_left_right
      hax.symm hab.symm ha) ?_
    simp only [mem_iUnion, toSet_eq_biUnion]
    use s'
  obtain ⟨c, ⟨hcP, hac⟩, hc⟩ := hP'.unique_segment ha haP'
  refine ⟨c, ⟨by simp [vPairs, hcP], hac⟩, fun y ⟨hy, hay⟩ ↦ ?_⟩
  obtain rfl | hyP' := by simpa only [vPairs, mem_cons] using hy
  · exact hdj.notMem_of_mem_left (mem_openSegment_of_ne_left_right hax.symm hab.symm hay) ha |>.elim
  · exact hc y ⟨hyP', hay⟩

lemma closedSimple.two_segments (h : P.closedSimple) (hb : b ∈ P.vertices) : ∃ a c,
    (a, b) ∈ P.vertices.zip P.vertices.tail ∧ (b, c) ∈ P.vertices.zip P.vertices.tail ∧
    b ∉ ⋃ s ∈ {s | s ∈ P.vertices.zip P.vertices.tail} \ {(a, b), (b, c)}, segment ℝ s.1 s.2 := by
  sorry

end ClosedSimple

def region (P : PolygonalPath x y) (a : α) : Set α :=
  connectedComponentIn P.toSetᶜ a

lemma region_subset (P : PolygonalPath x y) (a : α) : P.region a ⊆ P.toSetᶜ :=
  connectedComponentIn_subset P.toSetᶜ a

lemma mem_region (ha : a ∉ P.toSet) : a ∈ P.region a :=
  mem_connectedComponentIn ha

lemma region_nonempty_iff (P : PolygonalPath x y) (a : α) : (P.region a).Nonempty ↔ a ∉ P.toSet :=
  connectedComponentIn_nonempty_iff

lemma region_empty_iff (P : PolygonalPath x y) (a : α) : P.region a = ∅ ↔ a ∈ P.toSet := by
  rw [← not_nonempty_iff_eq_empty, not_iff_comm]
  exact (region_nonempty_iff P a).symm

lemma region_isOpen [LocallyConnectedSpace α] [IsTopologicalAddGroup α] [T2Space α]
    (P : PolygonalPath x y) (a : α) : IsOpen (P.region a) :=
  P.toSet_isClosed.isOpen_compl.connectedComponentIn

lemma region_frontier_subset [LocallyConnectedSpace α] [IsTopologicalAddGroup α] [T2Space α]
    (P : PolygonalPath x y) (a : α) : frontier (P.region a) ⊆ P.toSet := by
  by_cases ha : a ∈ P.toSet
  · simp [(P.region_empty_iff a).mpr ha]
  exact frontier_connectedComponentIn P.toSet_isClosed ha

lemma exists_mem_frontier_connectedComponentIn [LocallyConnectedSpace α] [IsTopologicalAddGroup α]
    [T2Space α] (P : PolygonalPath x y) (ha : a ∉ P.toSet) :
    ∃ x ∈ P.toSet, x ∈ frontier (P.region a) := by
  let s : Set I := (Path.segment a x) ⁻¹' P.region a
  let b := Path.segment a x (sSup s)
  suffices hbf : b ∈ frontier (P.region a) by exact ⟨b, P.region_frontier_subset a hbf, hbf⟩
  refine ⟨image_closure_subset_closure_image (Path.segment a x |>.continuous) (s := s).trans
      (closure_mono (image_preimage_subset ..)) ?_, ?_⟩
  · use sSup s, sSup_mem_closure (by use 0; simp [s, P.mem_region ha])
  rw [P.region_isOpen a |>.interior_eq]
  exact (Path.segment a x).sSup_notMem (P.region_isOpen a) fun hr ↦
    P.region_subset a hr <| P.vertices_subset_toSet P.first_mem_vertices

end Path

end PolygonalPath

section Uniform
open PolygonalPath

/--
Returns a list of uniformly spaced `N + 1` points in the closed unit interval `[0, 1]`,
subdividing the interval into `N` equal parts.

Specifically, for a positive natural number `N`, `List.uniform hN` produces
the list `[0, 1/N, 2/N, ..., 1]` (as elements of `unitInterval`), so the list has
length `N + 1`. The points are suitable for parametrizing polygonal subdivisions
or sampling a path at `N` evenly distributed intervals.
-/
noncomputable def List.uniform (hN : 0 < N) : List unitInterval :=
  List.finRange (N + 1) |>.map (fun (i : Fin (N + 1)) ↦ ⟨(i : ℝ) / N,
    div_nonneg (cast_nonneg _) (cast_nonneg _), by
    rw [div_le_one (cast_pos.mpr hN)]
    exact cast_le.mpr (le_of_lt_succ i.is_lt)⟩)

@[simp]
lemma List.uniform_head? (hN : 0 < N) : (List.uniform hN).head? = some 0 := by
  simp [uniform, finRange]

@[simp]
lemma List.uniform_getLast? (hN : 0 < N) : (List.uniform hN).getLast? = some 1 := by
  rw [uniform, finRange_succ_last]
  simp [hN.ne']

lemma List.uniform_isChain (hN : 0 < N) : (List.uniform hN).IsChain (dist · · = 1 / N) := by
  simp only [Subtype.dist_eq, dist_eq_norm, Real.norm_eq_abs, one_div, uniform,
    finRange_eq_pmap_range, isChain_map, isChain_pmap, Order.lt_add_one_iff, exists_prop,
    isChain_and_iff, isChain_range, add_tsub_cancel_right, succ_eq_add_one, Order.add_one_le_iff,
    imp_self, implies_true, cast_add, cast_one, true_and]
  simp +contextual only [le_of_lt, implies_true, true_and]
  intro m hmN
  simp [div_sub_div_same, abs_div]

@[simp]
lemma List.uniform_length (hN : 0 < N) : (List.uniform hN).length = N + 1 := by
  simp [uniform]

@[simp]
lemma List.uniform_get (hN : 0 < N) (i : Fin (N + 1)) :
    (List.uniform hN).get (i.cast (by simp)) = (i : ℝ) / N := by
  simp [uniform]

lemma List.uniform_eq_cons_concat (hN : 0 < N) :
    List.uniform hN = 0 :: (List.uniform hN).tail.dropLast ++ [1] := by
  simp only [cons_append]
  rw [dropLast_append_getLast?, cons_head?_tail (by simp)]
  rw [getLast?_tail]
  simp [hN.ne']

variable [SeminormedAddCommGroup α] [NormedSpace ℝ α]

lemma Path.exists_polygonalPath_of_thickening (P : Path x y) {δ : ℝ} (hδ : 0 < δ) :
    ∃ L : PolygonalPath x y, L.toSet ⊆ Metric.thickening δ (range P) := by
  obtain ⟨ε, hεpos, hε⟩ := Metric.uniformContinuous_iff.mp P.uniformContinuous δ hδ
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  have hNpos' : 0 < (N : ℝ) := lt_trans (by simpa) hN
  have hNpos : 0 < N := by norm_cast at hNpos'
  have hN' : 1 / ↑N < ε := (one_div_lt hεpos hNpos').mp hN
  set L : List α := (List.uniform hNpos) |>.map P with hL
  use ofList x L.tail.dropLast y
  have hxLy : L = x :: L.tail.dropLast ++ [y] := by
    rw [hL, List.uniform_eq_cons_concat hNpos]
    simp
  have hLtail : L.tail = L.tail.dropLast ++ [y] := by
    rw [hxLy]
    simp
  simp only [toSet_eq_biUnion, vPairs_eq_zip, ofList_vertices, ← hxLy, iUnion_subset_iff,
    Prod.forall]
  refine fun a b hab x hx ↦ mem_thickening_iff.mpr ⟨b, ?_, ?_⟩
  · simp only [Set.mem_range, Subtype.exists, mem_Icc]
    obtain ⟨i, hi, -, hhi⟩ := by simpa [L] using List.mem_of_mem_tail (List.of_mem_zip hab |>.2)
    use i, hi, hhi
  have hchain : L.IsChain (dist · · < δ) := by
    unfold L
    rw [List.isChain_map]
    apply List.uniform_isChain hNpos |>.imp fun a b hab ↦ hε (hab ▸ hN')
  rw [List.isChain_iff_all_zip_tail] at hchain
  have hdist := by simpa using hchain _ hab
  have hseg : segment ℝ a b ⊆ ball b δ := (convex_ball b δ).segment_subset (by simpa) (by simpa)
  simpa using hseg hx

lemma JoinedIn.exists_polygonalPath_of_open (hX : IsOpen X) (h : JoinedIn X x y) :
    ∃ P : PolygonalPath x y, range P.toPath ⊆ X := by
  obtain ⟨P, hP⟩ := h
  have hPc : IsCompact (range P) := isCompact_range P.continuous
  have hPr : range ⇑P ⊆ X := by
    intro i hi
    simp only [Set.mem_range, Subtype.exists, mem_Icc] at hi
    obtain ⟨t, ht, rfl⟩ := hi
    exact hP ⟨t, ht⟩
  obtain ⟨δ, hδpos, hδ⟩ := hPc.exists_thickening_subset_open hX hPr
  obtain ⟨L, hL⟩ := P.exists_polygonalPath_of_thickening hδpos
  use L, hL.trans hδ

end Uniform

section Even

lemma even_of_involutive (f : α → α) (hf : Involutive f) (hfix : ∀ x, f x ≠ x) :
    Even (Nat.card α) := by
  classical
  obtain (_ | _) := finite_or_infinite α |>.symm
  · simp [Nat.card_eq_zero_of_infinite]
  letI : Fintype α := Fintype.ofFinite α
  letI s : Setoid α := {
    r := fun x y => y = x ∨ y = f x
    iseqv := by
      refine ⟨fun x ↦ Or.inl rfl, ?_, ?_⟩
      · rintro x y (rfl | rfl) <;> simp [hf.eq_iff.symm]
      · rintro x y z (rfl | rfl) (rfl | rfl) <;> simp [hf.eq_iff]}
  suffices e : α ≃ (Quotient s × Bool) by simp [Fintype.card_congr e]
  let toFun : α → (Quotient s × Bool) := fun x =>
    let q : Quotient s := ⟦x⟧
    (q, decide (x = q.out))
  let invFun : (Quotient s × Bool) → α := fun qb =>
    let r := qb.1.out
    bif qb.2 then r else f r
  refine ⟨toFun, invFun, fun x ↦ ?_, fun ⟨q, b⟩ ↦ ?_⟩
  · let r : α := (⟦x⟧ : Quotient s).out
    have hx : x = r ∨ x = f r := Quotient.exact (by simp [r] : (⟦r⟧ : Quotient s) = ⟦x⟧)
    by_cases hxr : x = r <;> grind
  · let r : α := q.out
    cases b
    · have hmk : (⟦f r⟧ : Quotient s) = q := by
        have : (⟦r⟧ : Quotient s) = ⟦f r⟧ := Quotient.sound (s := s) (Or.inr rfl)
        exact this.symm.trans (by simp [r])
      simp [toFun, invFun, r, hmk, hfix r]
    · have hmk : (⟦r⟧ : Quotient s) = q := by simp [r]
      simp [toFun, invFun, r, hmk]

end Even

/-# Crossings -/

section Crossings

variable [TopologicalSpace α] [TopologicalSpace β] {a b c : α} {x y z : β}

-- lemma exists_component_linking_closures {α : Type*} [TopologicalSpace α] [T2Space α]
--     [CompactSpace α] [PreconnectedSpace α] {U V : Set α} (hU : IsOpen U) (hV : IsOpen V)
--     (hUne : U.Nonempty) (hVne : V.Nonempty) (hUV : Disjoint U V) :
--     ∃ x ∈ (U ∪ V)ᶜ, (closure U ∩ connectedComponentIn (U ∪ V)ᶜ x).Nonempty ∧
--     (closure V ∩ connectedComponentIn (U ∪ V)ᶜ x).Nonempty := by
--   by_contra hx
--   simp_rw [not_exists, not_and (a := _ ∈ (U ∪ V)ᶜ)] at hx
--   simp only [compl_union, mem_inter_iff, mem_compl_iff, not_and_or, not_nonempty_iff_eq_empty,
--     ← disjoint_iff_inter_eq_empty, and_imp] at hx

--   sorry

-- namespace ContinuousMap

-- def crossing (U : Set β) (f : C(α, β)) : Set β :=
--     closure (range f ∩ (interior U)) ∩ closure (range f ∩ (closure U)ᶜ)

-- lemma crossing_subset_range (U : Set β) (f : C(α, β)) (hf : IsClosed (range f)) :
--     crossing U f ⊆ range f := by
--   simp only [crossing]
--   exact inter_subset_left.trans <| closure_mono inter_subset_left
--   |>.trans hf.closure_subset

-- lemma crossing_subset_frontier (U : Set β) (f : C(α, β)) :
--     crossing U f ⊆ frontier U := by
--   refine fun x hx ↦ ⟨?_, ?_⟩
--   · exact closure_mono inter_subset_right |>.trans (closure_mono interior_subset) hx.1
--   · have := by simpa using closure_mono inter_subset_right hx.2
--     contrapose! this
--     exact interior_mono (subset_closure) this

-- lemma mem_crossing_of_mem_notMem (U : Set β) (f : C(α, β)) (ha : a ∈ closure (⇑f ⁻¹' interior U))
--     (hb : b ∉ interior (⇑f ⁻¹' closure U)) (hab : f a = f b) : f a ∈ crossing U f := by
--   refine ⟨?_, hab ▸ ?_⟩ <;>
--   · rw [← mem_preimage]
--     apply f.continuous.closure_preimage_subset
--     simpa

-- lemma exists_crossing [PreconnectedSpace α] (U : Set β) (f : C(α, β))
--     (hfin : (range f ∩ frontier U).Finite) (ha : f a ∈ interior U) (hb : f b ∉ closure U) :
--     (crossing U f).Nonempty := by
--   let V  := f ⁻¹' (interior U)
--   let W := f ⁻¹' (closure U)ᶜ
--   have hV_open : IsOpen V := isOpen_interior.preimage f.continuous
--   have hW_open : IsOpen W := (isClosed_closure.preimage f.continuous).isOpen_compl
--   have haV : a ∈ V := by simp [V, ha]
--   have hbW : b ∈ W := by simp [W, hb]
--   have hVW_disjoint : Disjoint V W := by
--     rw [Set.disjoint_iff]
--     intro t ⟨htV, htW⟩
--     exact htW (interior_subset_closure htV)
--   -- have hV'W_disjoint : Disjoint (closure V) W := hVW_disjoint.closure_left hW_open
--   obtain ⟨c, hccV, hcV⟩ : (frontier V).Nonempty := by
--     rw [nonempty_frontier_iff, ne_univ_iff_exists_notMem]
--     exact ⟨(by use a), (by use b, hVW_disjoint.notMem_of_mem_right hbW)⟩
--   let S := connectedComponentIn (V ∪ W)ᶜ c

--   have hS : (f '' S).Subsingleton := by
--     sorry
--   refine ⟨f c, mem_crossing_of_mem_notMem U f hccV ?_ ?_⟩
--   suffices c ∈ closure W by simpa [W] using this


variable {x y z : α}

/--
`crossings U P` is the set of points in the path `P` s.t. every neighborhood of the
point inside `P` has nonempty intersection with both `interior U` and `(closure U)ᶜ`.
That is, the point is in between a part of `P` inside `U` and a part of `P` outside `U`. -/
def crossings (U : Set α) (P : Path x y) : Set α :=
    closure (range P ∩ (interior U)) ∩ closure (range P ∩ (closure U)ᶜ)

variable (U : Set α) (P : Path x y)

lemma crossings_subset_path [T2Space α] : crossings U P ⊆ range P := by
  simp only [crossings]
  exact inter_subset_left.trans <| closure_mono inter_subset_left
  |>.trans (isCompact_range P.continuous).isClosed.closure_subset

lemma crossings_subset_frontier : crossings U P ⊆ frontier U := by
  refine fun x hx ↦ ⟨?_, ?_⟩
  · exact closure_mono inter_subset_right |>.trans (closure_mono interior_subset) hx.1
  · have := by simpa using closure_mono inter_subset_right hx.2
    contrapose! this
    exact interior_mono (subset_closure) this

lemma Path.exists_mem_frontier (P : Path x y) (U : Set α) (hx : x ∈ U) (hy : y ∉ U) :
    (range P ∩ frontier U).Nonempty := by
  let V : Set unitInterval := P ⁻¹' U
  have hVnonempty : V.Nonempty := ⟨0, by simpa [V, Path.source] using hx⟩
  have hVneuniv : V ≠ univ := by
    intro hV
    have : (1 : unitInterval) ∈ V := by simp [hV]
    exact hy (by simpa [V, Path.target] using this)
  rcases (nonempty_frontier_iff (s := V)).mpr ⟨hVnonempty, hVneuniv⟩ with ⟨t, ht⟩
  exact ⟨P t, ⟨t, rfl⟩, by simpa using P.continuous.frontier_preimage_subset U ht⟩

lemma exists_crossings [T1Space α] (hfin : (range P ∩ frontier U).Finite) (hx : x ∈ interior U)
    (hy : y ∉ closure U) : (crossings U P).Nonempty := by
  let V : Set unitInterval := P ⁻¹' (interior U)
  let W : Set unitInterval := P ⁻¹' (closure U)ᶜ
  have hV_open : IsOpen V := isOpen_interior.preimage P.continuous
  have hW_open : IsOpen W := (isClosed_closure.preimage P.continuous).isOpen_compl
  have h0inV : 0 ∈ V := by simp [V, hx]
  have h1inW : 1 ∈ W := by simp [W, hy]
  have hVW_disjoint : Disjoint V W := by
    rw [Set.disjoint_iff]
    intro t ⟨htV, htW⟩
    exact htW (interior_subset_closure htV)
  have hV'W_disjoint : Disjoint (closure V) W := hVW_disjoint.closure_left hW_open

  let tz := sSup V
  let z := P tz
  have htz_mem_closure_V : tz ∈ closure V :=
    csSup_mem_closure (nonempty_of_mem h0inV) ⟨1, fun x hx ↦ x.2.2⟩
  have htz_notMem_W : tz ∉ W :=
    hV'W_disjoint.notMem_of_mem_left htz_mem_closure_V
  have htz_lt_one : tz < 1 := by
    by_contra! h
    exact hV'W_disjoint.ne_of_mem htz_mem_closure_V h1inW <| (one_le _).mp h
  have htz_notMem_V : tz ∉ V := hV_open.sSup_notMem ⟨1, htz_lt_one⟩
  refine ⟨z, ?_, ?_⟩
  · rw [mem_closure_iff_nhds]
    intro U_z hU_z
    have ⟨t, htP, htV⟩ : (P ⁻¹' U_z ∩ V).Nonempty := mem_closure_iff_nhds.mp htz_mem_closure_V
      (P ⁻¹' U_z) (P.continuous.continuousAt hU_z)
    exact ⟨P t, htP, (by use t), htV⟩
  rw [inter_comm, ← image_preimage_eq_inter_range]
  change z ∈ closure (P '' W)
  refine image_closure_subset_closure_image P.continuous ?_

  let tz' : unitInterval := sInf (Ioi tz ∩ W)
  have hbdd : BddBelow (Ioi tz ∩ W) := ⟨tz, fun _ h ↦ h.1.le⟩
  have htlet : tz ≤ tz' := le_sInf fun _ h ↦ h.1.le
  have hinter_open : IsOpen (Ioi tz ∩ W) := isOpen_Ioi (a := tz).inter hW_open
  have h_zero_lt_tz' : 0 < tz' := by
    by_contra! h
    replace h := h.antisymm bot_le
    apply hVW_disjoint.mono_right (inter_subset_right (s := Ioi tz))
    |>.closure_right hV_open |>.notMem_of_mem_left h0inV
    exact h ▸ csInf_mem_closure ⟨1, by simpa [h1inW]⟩ hbdd
  have htz'_notMem_W : tz' ∉ W := by
    rintro htz'W
    have : tz' ∉ _ := ((isOpen_Ioi (a := tz)).inter hW_open).sInf_notMem ⟨0, h_zero_lt_tz'⟩
    simp only [mem_inter_iff, mem_Ioi, htz'W, and_true, not_lt] at this
    replace this := this.antisymm htlet
    exact htz_notMem_W (this ▸ htz'W)

  refine ⟨tz', ?_, ?_⟩
  · apply csInf_mem_closure (by use 1; simp [h1inW, htz_lt_one]) hbdd
    simp only [mem_setOf_eq, isClosed_closure, true_and]
    exact inter_subset_right.trans subset_closure
  suffices (P '' (Icc tz tz')).Subsingleton by
    exact this (by use tz', by simpa) (by use tz, by simpa)

  have hItfrontierU : P '' (Icc tz tz') ⊆ frontier U := by
    rw [image_subset_iff]
    intro t ⟨htl, htr⟩
    have htV : t ∉ V := by
      intro htv
      exact ((htl.antisymm <| le_sSup htv) ▸ htz_notMem_V) htv
    have htW : t ∉ W := by
      intro htw
      have hne : tz ≠ t := fun heq ↦ htz_notMem_W (heq ▸ htw)
      replace htl := lt_of_le_of_ne htl hne
      exact ((htr.antisymm <| sInf_le ⟨htl, htw⟩) ▸ htz'_notMem_W) htw
    simp only [preimage_compl, mem_compl_iff, mem_preimage, not_not, W] at htW
    exact ⟨htW, htV⟩

  rw [← Set.not_nontrivial_iff]
  exact mt (isPreconnected_Icc.image P P.continuous.continuousOn |>.infinite_of_nontrivial)
  <| not_infinite.mpr <| hfin.subset <| by simp [hItfrontierU]

lemma crossings_encard_even (hfin : (range P ∩ frontier U).Finite) :
    Even (crossings U P).encard := by

  -- let f : crossings U P → crossings U P := fun x
  sorry

end Crossings



-- lemma foo {x y : EuclideanSpace ℝ (Fin 2)} (P : PolygonalPath x y) :
--     ∃ (ε : ℝ) (R₀ R₁ : Set (EuclideanSpace ℝ (Fin 2))),
--     0 < ε ∧ Metric.thickening ε (range P.toPath) = R₀ ∪ R₁ ∧
--     IsPathConnected R₀ ∧ IsPathConnected R₁ :=
--   sorry
