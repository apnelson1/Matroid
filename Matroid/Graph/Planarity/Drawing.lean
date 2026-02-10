import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.UniformSpace.Path
import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
import Mathlib.Geometry.Polygon.Basic
import Matroid.Graph.Finite

variable {α β : Type*} {x y : EuclideanSpace ℝ (Fin 2)} {C L : List (EuclideanSpace ℝ (Fin 2))}
  {X Y : Set (EuclideanSpace ℝ (Fin 2))}

open Set Function TopologicalSpace Topology

def List.drawing (L : List (EuclideanSpace ℝ (Fin 2))) : Set (EuclideanSpace ℝ (Fin 2)) :=
  ⋃ x ∈ L.dropLast.zip L.tail, segment ℝ x.1 x.2

def List.cdrawing (C : List (EuclideanSpace ℝ (Fin 2))) : Set (EuclideanSpace ℝ (Fin 2)) :=
  ⋃ x ∈ C.zip (C.rotate 1), segment ℝ x.1 x.2
  -- C.zip (C.rotate 1) |>.map (fun (x, y) ↦ segment ℝ x y) |>.foldl (· ∪ ·) ∅

def List.toPath (L : List (EuclideanSpace ℝ (Fin 2))) : Path x y := by
  sorry

lemma List.drawing_compact (L : List (EuclideanSpace ℝ (Fin 2))) : IsCompact (drawing L) := by
  simp only [drawing]
  induction L.dropLast.zip L.tail with
  | nil => simp
  | cons a as ih =>
    simp only [List.mem_cons, iUnion_iUnion_eq_or_left]
    apply IsCompact.union _ ih
    rw [← convexHull_pair]
    apply Set.Finite.isCompact_convexHull
    simp

lemma List.cdrawing_compact (C : List (EuclideanSpace ℝ (Fin 2))) : IsCompact (cdrawing C) := by
  simp only [cdrawing]
  induction C.zip (C.rotate 1) with
  | nil => simp
  | cons a as ih =>
    simp only [List.mem_cons, iUnion_iUnion_eq_or_left]
    apply IsCompact.union _ ih
    rw [← convexHull_pair]
    apply Set.Finite.isCompact_convexHull
    simp

noncomputable def t {N : ℕ} (hN : 0 < N) (i : Fin (N + 1)) : unitInterval :=
  ⟨(i : ℝ) / N, by
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · rw [div_le_one (Nat.cast_pos.mpr hN)]
      exact Nat.cast_le.mpr (Nat.le_of_lt_succ i.is_lt)⟩

lemma Path.exists_drawing_of_thickening (P : Path x y) {δ : ℝ} (hδ : 0 < δ) : ∃ L : List _,
    L.drawing ⊆ Metric.thickening δ (range P) ∧ L.head? = some x ∧ L.getLast? = some y := by
  obtain ⟨ε, hεpos, hε⟩ := Metric.uniformContinuous_iff.mp P.uniformContinuous δ hδ
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  have hNpos : 0 < (N : ℝ) := lt_trans (by simpa) hN
  have hN' : 1 / ↑N < ε := (one_div_lt hεpos hNpos).mp hN
  let L : List (EuclideanSpace ℝ (Fin 2)) := List.ofFn (P ∘ (t <| by norm_cast at hNpos))
  use L, ?_, by simp [L, t], ?_
  · unfold List.drawing
    simp only [iUnion_subset_iff, Prod.forall]
    intro x y hxy
    have hdxy : dist x y < δ :=
      sorry
    have hx : x ∈ range P := by
      have hxL : x ∈ L := by
        sorry
      rw [List.mem_ofFn] at hxL
      obtain ⟨i, rfl⟩ := hxL
      simp
    refine subset_trans ?_ <| Metric.ball_subset_thickening hx _
    exact (convex_ball x δ).segment_subset (Metric.mem_ball_self hδ) (by simp [dist_comm, hdxy])
  unfold L
  rw [List.ofFn_succ_last]
  simp [t, div_self hNpos.ne']

lemma JoinedIn.exists_drawing (hX : IsOpen X) (h : JoinedIn X x y) :
    ∃ L : List _, L.drawing ⊆ X ∧ L.head? = some x ∧ L.getLast? = some y := by
  obtain ⟨P, hP⟩ := h
  have hPc : IsCompact (range P) := isCompact_range P.continuous
  have hPr : range ⇑P ⊆ X := by
    intro i hi
    simp only [mem_range, Subtype.exists] at hi
    obtain ⟨t, ht, rfl⟩ := hi
    exact hP ⟨t, ht⟩
  obtain ⟨δ, hδpos, hδ⟩ := hPc.exists_thickening_subset_open hX hPr
  obtain ⟨L, hL, hLh, hLl⟩ := P.exists_drawing_of_thickening hδpos
  use L, hL.trans hδ, hLh, hLl

lemma exists_angle_fst_ne (S : Set (EuclideanSpace ℝ (Fin 2))) (hS : S.Finite) :
    let A := EuclideanSpace.instFactEqNatFinrankFin 2
    let B := A.out ▸ (stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin 2))).toBasis.orientation
    ∃ θ : Real.Angle, S.InjOn (B.rotation θ · 0) := by
  intro A B
  -- 1. Define the set of bad angles for a pair (u, v)
  let bad_angles (u v : EuclideanSpace ℝ (Fin 2)) : Set Real.Angle :=
    { θ | (B.rotation θ u) 0 = (B.rotation θ v) 0 }

  -- 2. Show bad_angles is finite for distinct u, v
  have h_finite_pair (u v : EuclideanSpace ℝ (Fin 2)) (h : u ≠ v) : (bad_angles u v).Finite := by
    -- Use orthogonality arguments in 2D Euclidean space
    sorry

  -- 3. Define the set of all bad angles
  let all_bad_angles := ⋃ (u ∈ S) (v ∈ S) (_ : u ≠ v), bad_angles u v

  -- 4. Show the union is finite
  have h_finite_all : all_bad_angles.Finite := by
    apply Set.Finite.biUnion hS
    intro u _
    apply Set.Finite.biUnion hS
    intro v _
    simp only [finite_iUnion_of_subsingleton]
    intro h_ne
    exact h_finite_pair u v h_ne

  -- 5. Conclude existence
  have h_infinite : (Set.univ : Set Real.Angle).Infinite := by
    have : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
    rw [infinite_univ_iff, Real.Angle, (AddCircle.equivIco _ 0).infinite_iff]
    apply Set.Ico.infinite
    positivity
  obtain ⟨θ, hθ⟩ := (h_infinite.diff h_finite_all).nonempty
  use θ
  intro x hxS y hyS hxy
  by_contra! hne
  have hθ1 : θ ∈ bad_angles x y := hxy
  have hθ2 : θ ∈ all_bad_angles := by
    simp [all_bad_angles]
    use x, hxS, y
  exact hθ.2 hθ2

-- Define a vertical ray starting at (c, y0) and going upwards.
-- It is the set of points where x = c and y ≥ y0.
def VerticalRay (c y0 : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {p | p 0 = c ∧ y0 ≤ p 1}

lemma vertical_ray_segment_inter_subsingleton (c y0 : ℝ) (a b : EuclideanSpace ℝ (Fin 2))
    (h_non_vert : a 0 ≠ b 0) : (VerticalRay c y0 ∩ segment ℝ a b).Subsingleton := by
  rintro p ⟨⟨rfl, hpy⟩, hp'⟩ q ⟨⟨hx, hqy⟩, hq'⟩
  -- Since p and q are on the segment, they can be written as a + t • (b - a)
  rw [segment_eq_image'] at hp' hq'
  obtain ⟨tp, _, rfl⟩ := hp'
  obtain ⟨tq, _, rfl⟩ := hq'
  simp_all [sub_ne_zero.mpr (Ne.symm h_non_vert)]

lemma vertical_ray_drawing_inter_finite (c y0 : ℝ) (L : List (EuclideanSpace ℝ (Fin 2)))
    (hL : L.Pairwise ((· ≠ ·) on (· 0))) :
    (VerticalRay c y0 ∩ L.drawing).Finite := by
  simp only [List.drawing, inter_iUnion]
  refine Finite.biUnion' (List.finite_toSet _) fun x hx ↦ ?_
  refine (vertical_ray_segment_inter_subsingleton c y0 x.1 x.2 ?_).finite
  apply hL.forall (Symmetric.comap (fun a b ↦ Ne.symm) _)
  sorry
  sorry
  sorry

/-- Vertices of the polygonal curve that previous and next edges are both left or right side of
  the vertex. -/
def List.turn (L : List (EuclideanSpace ℝ (Fin 2))) : Set (EuclideanSpace ℝ (Fin 2)) := by
  sorry

noncomputable def m (L : List (EuclideanSpace ℝ (Fin 2))) (x : EuclideanSpace ℝ (Fin 2)) : Prop :=
  Even (VerticalRay (x 0) (x 1) ∩ (L.drawing \ L.turn)).ncard

lemma forall_nhdsWithin_m_const (L : List (EuclideanSpace ℝ (Fin 2)))
    (hL : L.Pairwise ((· ≠ ·) on (· 0))) :
    ∀ x ∈ L.drawingᶜ, ∀ᶠ y in 𝓝[L.drawingᶜ] x, m L x ↔ m L y := by
  intro x hxs
  have ho : IsOpen L.drawingᶜ := L.drawing_compact.isClosed.isOpen_compl
  rw [ho.nhdsWithin_eq hxs, Metric.eventually_nhds_iff_ball]
  obtain ⟨ε, hεpos, hε⟩ := Metric.isOpen_iff.mp ho x hxs
  use ε, by positivity
  intro y hy
  have hyε := hε hy
  let z : EuclideanSpace ℝ (Fin 2) := !₂[x 0, y 1]
  have hz : m L x ↔ m L z := by
    clear hε ho
    simp only [m, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      z]
    suffices VerticalRay (x.ofLp 0) (x.ofLp 1) ∩ (L.drawing \ L.turn) =
      VerticalRay (x.ofLp 0) (y.ofLp 1) ∩ (L.drawing \ L.turn) by
      rw [this]
    rw [inter_eq_inter_iff_right]
    -- Moving vertically does not change the number of points in the intersection.
    sorry
  simp only [hz]
  simp only [m, Fin.isValue, z, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  -- Moving horizontally does not change the parity of the number of points in the intersection.
  sorry

lemma not_isPreconnected (L : List (EuclideanSpace ℝ (Fin 2))) (hL : L.Pairwise ((· ≠ ·) on (· 0))):
    ¬ IsPreconnected (L.drawingᶜ) := by
  intro hconn
  obtain ⟨x, hx, hmx⟩ : ∃ x ∈ L.drawingᶜ, m L x := sorry
  obtain ⟨y, hy, hmy⟩ : ∃ y ∈ L.drawingᶜ, ¬ m L y := sorry
  exact hmy <| hconn.induction₂ (m L · ↔ m L ·) (forall_nhdsWithin_m_const L hL) (by grind)
    (by grind) hx hy |>.mp hmx

open Graph

structure Graph.orientation (G : Graph α β) where
  dInc : E(G) → V(G) × V(G)
  isLink_of_dInc : ∀ e, G.IsLink e.val (dInc e).1 (dInc e).2

@[simps (attr := grind =)]
def Graph.orientation.anti {G H : Graph α β} (hH : H ≤ G) (D : Graph.orientation G) :
    Graph.orientation H := by
  refine ⟨fun e ↦ ?_, fun e ↦ ?_⟩ <;> let e' : E(G) := ⟨e, edgeSet_mono hH e.prop⟩ <;>
    have := D.isLink_of_dInc e' |>.of_le_of_mem hH e.prop
  · exact (⟨_, this.left_mem⟩, ⟨_, this.right_mem⟩)
  exact this

structure Graph.Drawing (G : Graph α β) extends orientation G where
  vertex : V(G) → EuclideanSpace ℝ (Fin 2)
  vertex_inj : Function.Injective vertex
  edge : ∀ e : E(G), Path (vertex (dInc e).1) (vertex (dInc e).2)
  edge_vert_inter : ∀ e, range (edge e) ∩ range vertex ⊆ {vertex (dInc e).1, vertex (dInc e).2}
  edge_inter : ∀ e₁ e₂, e₁ ≠ e₂ → range (edge e₁) ∩ range (edge e₂) ⊆
    {vertex (dInc e₁).1, vertex (dInc e₁).2} ∩ {vertex (dInc e₂).1, vertex (dInc e₂).2}

@[simps! (attr := grind =)]
def Graph.Drawing.anti {G H : Graph α β} (hH : H ≤ G) (D : Graph.Drawing G) : Graph.Drawing H where
  toorientation := D.toorientation.anti hH
  vertex := fun v ↦ D.vertex ⟨v, vertexSet_mono hH v.prop⟩
  vertex_inj _ _ hab := by simpa [Subtype.ext_iff] using D.vertex_inj hab
  edge e := D.edge ⟨e, edgeSet_mono hH e.prop⟩
  edge_vert_inter e := subset_trans (by grind) (D.edge_vert_inter ⟨e, edgeSet_mono hH e.prop⟩)
  edge_inter e₁ e₂ hne := subset_trans (by grind) (D.edge_inter ⟨e₁, edgeSet_mono hH e₁.prop⟩
    ⟨e₂, edgeSet_mono hH e₂.prop⟩ (by simpa [Subtype.ext_iff] using hne))

def Graph.bot_Drawing : Graph.Drawing (⊥ : Graph α β) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩ <;> try rintro ⟨i, hi⟩ ; simp at hi

def Graph.IsPlanar (G : Graph α β) : Prop := Nonempty (Drawing G)

lemma Graph.IsPlanar.anti {G H : Graph α β} (hG : G.IsPlanar) (hH : H ≤ G) : H.IsPlanar :=
  ⟨hG.some.anti hH⟩

lemma Graph.bot_isPlanar : (⊥ : Graph α β).IsPlanar := ⟨Graph.bot_Drawing⟩

lemma Graph.IsPlanar.exists_polygonal_drawing {G : Graph α β} [G.Finite] (hG : G.IsPlanar) :
    ∃ (D : G.Drawing) (L : E(G) → List (EuclideanSpace ℝ (Fin 2))),
    ∀ e, D.edge e = (L e).toPath := by
  obtain ⟨DG⟩ := hG
  refine G.of_not_exists_minimal (P := fun G ↦ ∃ (D : G.Drawing) (L : E(G) → List _),
    ∀ e, D.edge e = (L e).toPath) (fun H hle _ hMin ↦ ?_)
  obtain ⟨e, he⟩ : E(H).Nonempty := by
    by_contra! hE
    refine hMin.prop ⟨DG.anti hle, ?_, ?_⟩ <;> rintro ⟨e, he⟩ <;> simp [hE] at he
  have hlt : H ＼ {e} < H := by
    apply lt_of_le_of_ne edgeDelete_le
    rintro heq
    simpa [he] using congrArg Graph.edgeSet heq
  obtain ⟨D, L, h⟩ := not_not.mp <| hMin.not_prop_of_lt hlt
  sorry
