module

public import Matroid.Graph.Planarity.Drawing
public import Matroid.Graph.Subdivision

@[expose] public section

/-!
# Drawings of topological minors and subdivisions

This file connects the combinatorial route witnesses in `Graph.TopologicalMinor` with graph
realizations and drawings. A topological minor gives a continuous injection of its realization
into the host realization. A subdivision is exhaustive, so that injection is a homeomorphism.
Consequently drawings restrict to topological minors, while subdivisions transport drawings in
both directions without changing their image.

The combinatorial definitions stay in `Matroid.Graph.TopologicalMinor`; generic drawing unions are
independent and live in `Matroid.Graph.Planarity.Drawing.Union`.
-/

open Function Set Topology Path WList unitInterval
open scoped unitInterval

namespace Graph

noncomputable section

variable {α β γ δ X : Type*} {G : Graph α β} {H : Graph γ δ} [TopologicalSpace X]

/-- Vertices with equal labels give the same point of the realization. -/
lemma vertexMk_congr {u v : V(G)} (h : (u : α) = v) : vertexMk u = vertexMk v :=
  congrArg vertexMk (Subtype.ext h)

open Classical

/-- The unit-interval path along an incidence, reversed when the walk uses the edge backwards. -/
noncomputable def pathOfIsLink {e : β} {x y : α} (h : G.IsLink e x y) :
    Path (vertexMk ⟨x, h.left_mem⟩) (vertexMk ⟨y, h.right_mem⟩) :=
  if hdir : x = G.source e h.edge_mem ∧ y = G.target e h.edge_mem then
    (edgePath ⟨e, h.edge_mem⟩).cast (vertexMk_congr hdir.1) (vertexMk_congr hdir.2)
  else
    have hswap := (h.eq_and_eq_or_eq_and_eq (G.isLink_source_target h.edge_mem)).resolve_left hdir
    (edgePath ⟨e, h.edge_mem⟩).symm.cast (vertexMk_congr hswap.1) (vertexMk_congr hswap.2)

/-- Concatenate `pathOfIsLink` along a nonempty walk, keeping the last edge on a full `[0,1]`
so the parametrization is not eventually constant. -/
noncomputable def pathOfIsWalk {w : WList α β} (hw : G.IsWalk w) (hne : w.Nonempty) :
    Path (vertexMk ⟨w.first, hw.first_mem⟩) (vertexMk ⟨w.last, hw.last_mem⟩) :=
  match w, hne with
  | .cons _x _e (.nil _y), _ =>
    (pathOfIsLink (cons_isWalk_iff.mp hw).1).cast (vertexMk_congr rfl) (vertexMk_congr rfl)
  | .cons _x _e (.cons y f w), _ =>
    have h := cons_isWalk_iff.mp hw
    ((pathOfIsLink h.1).trans
      ((pathOfIsWalk h.2 (cons_nonempty y f w)).cast (vertexMk_congr rfl)
        (vertexMk_congr rfl))).cast (vertexMk_congr rfl) (vertexMk_congr rfl)

lemma path_trans_interior {X : Type*} [TopologicalSpace X] {x y z : X}
    {P : Path x y} {Q : Path y z} :
    (P.trans Q).Interior = P.Interior ∪ {y} ∪ Q.Interior := by
  apply subset_antisymm
  · rintro p ⟨t, ht, rfl⟩
    rw [trans_apply_ite_lt]
    split_ifs with hlt
    · have ht0 : (0 : ℝ) < t := ht.1
      have h2t : 2 * (t : ℝ) < 1 := by linarith
      refine .inl <| .inl ⟨⟨2 * (t : ℝ), (mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, hlt.le⟩⟩,
        ⟨mul_pos two_pos ht0, h2t⟩, rfl⟩
    · have hle : (1 / 2 : ℝ) ≤ t := le_of_not_gt hlt
      by_cases heq : (t : ℝ) = 1 / 2
      · refine .inl <| .inr ?_
        simp [heq, Path.source]
      · have ht1 : (t : ℝ) < 1 := ht.2
        have hpos : (0 : ℝ) < 2 * t - 1 := by linarith [lt_of_le_of_ne hle (Ne.symm heq)]
        have hlt1 : 2 * (t : ℝ) - 1 < 1 := by linarith
        refine .inr ⟨⟨2 * (t : ℝ) - 1, two_mul_sub_one_mem_iff.2 ⟨hle, t.2.2⟩⟩, ?_, rfl⟩
        rw [mem_Ioo, ← coe_pos, ← coe_lt_one]
        exact ⟨hpos, hlt1⟩
  · intro p hp
    rcases hp with h | ⟨s, hs, rfl⟩
    · rcases h with ⟨s, hs, rfl⟩ | rfl
      · have hs0 : (0 : ℝ) < s := hs.1
        refine ⟨squishLeft s, ?_, trans_squishLeft s⟩
        constructor
        · rw [← coe_pos]; change (0 : ℝ) < (s : ℝ) / 2; linarith
        · rw [← coe_lt_one]; change (s : ℝ) / 2 < 1; linarith [s.2.2]
      · exact ⟨half, ⟨zero_lt_half, half_lt_one⟩, by simp [trans_apply, half, Path.target]⟩
    · have hs0 : (0 : ℝ) < s := hs.1
      have hs1 : (s : ℝ) < 1 := hs.2
      refine ⟨squishRight s, ?_, trans_squishRight s⟩
      constructor
      · rw [← coe_pos]; change (0 : ℝ) < ((s : ℝ) + 1) / 2; linarith
      · rw [← coe_lt_one]; change ((s : ℝ) + 1) / 2 < 1; linarith

lemma pathOfIsLink_interior {e : β} {x y : α} (h : G.IsLink e x y) :
    (pathOfIsLink h).Interior = edgePath ⟨e, h.edge_mem⟩ '' Ioo (0 : I) 1 := by
  have hσ {t : I} (ht : t ∈ Ioo (0 : I) 1) : σ t ∈ Ioo (0 : I) 1 := by
    have h0 : (0 : ℝ) < t := ht.1
    have h1 : (t : ℝ) < 1 := ht.2
    rw [mem_Ioo, ← coe_pos, ← coe_lt_one, coe_symm_eq]
    constructor <;> linarith
  unfold pathOfIsLink
  split_ifs with hdir
  · simp [Path.Interior, Path.cast_coe]
  · ext z
    simp only [Path.Interior, Path.cast_coe, mem_image, Path.symm_apply]
    exact ⟨fun ⟨t, ht, ht'⟩ ↦ ⟨σ t, hσ ht, ht'⟩,
      fun ⟨t, ht, ht'⟩ ↦ ⟨σ t, hσ ht, by simpa [symm_symm] using ht'⟩⟩

lemma pathOfIsLink_injOn_Ioo {e : β} {x y : α} (h : G.IsLink e x y) :
    InjOn (pathOfIsLink h) (Ioo (0 : I) 1) := by
  intro s hs t ht heq
  unfold pathOfIsLink at heq
  split_ifs at heq
  · exact edgePath_inj_of_mem_Ioo (mod_cast hs) (by simpa [Path.cast_coe] using heq)
  · have hst : edgePath ⟨e, h.edge_mem⟩ (σ s) = edgePath ⟨e, h.edge_mem⟩ (σ t) := by
      simpa [Path.cast_coe] using heq
    have hs0 : (0 : ℝ) < s := hs.1
    have hs1 : (s : ℝ) < 1 := hs.2
    have hsσ : (σ s : ℝ) ∈ Ioo 0 1 := by
      rw [coe_symm_eq, mem_Ioo]; constructor <;> linarith
    simpa [symm_symm] using congrArg σ (edgePath_inj_of_mem_Ioo hsσ hst)

lemma mem_of_mem_internalVertexSet {w : WList α β} {x : α} (hx : x ∈ w.internalVertexSet) :
    x ∈ w :=
  mem_iff_eq_first_or_mem_internalVertexSet_or_eq_last.mpr (Or.inr (Or.inl hx))

lemma path_cast_interior {X : Type*} [TopologicalSpace X] {x y x' y' : X}
    {P : Path x y} (h1 : x' = x) (h2 : y' = y) :
    (P.cast h1 h2).Interior = P.Interior := by
  simp [Path.Interior, Path.cast_coe]

lemma internalVertexSet_cons_nil (x : α) (e : β) (y : α) :
    (cons x e (nil y)).internalVertexSet = ∅ := by
  simp [internalVertexSet]

lemma internalVertexSet_cons_cons (x : α) (e : β) (y : α) (f : β) (w : WList α β) :
    (cons x e (cons y f w)).internalVertexSet =
      insert y (cons y f w).internalVertexSet := by
  simp [internalVertexSet, cons_vertex_dropLast]
  ext z
  simp [mem_insert_iff]

lemma internalVertexSet_reverse (w : WList α β) :
    w.reverse.internalVertexSet = w.internalVertexSet := by
  simp only [internalVertexSet, reverse_vertex]
  ext x
  cases w with
  | nil => simp
  | cons a e w =>
    cases w with
    | nil => simp
    | cons b f w => simp [List.mem_reverse, or_comm]

lemma pathOfIsWalk_cons_nil {x : α} {e : β} {y : α} (hw : G.IsWalk (cons x e (nil y)))
    (hne : (cons x e (nil y)).Nonempty) :
    pathOfIsWalk hw hne =
      (pathOfIsLink (cons_isWalk_iff.mp hw).1).cast (vertexMk_congr rfl) (vertexMk_congr rfl) :=
  rfl

lemma pathOfIsWalk_cons_cons {x : α} {e : β} {y : α} {f : β} {w : WList α β}
    (hw : G.IsWalk (cons x e (cons y f w))) (hne : (cons x e (cons y f w)).Nonempty) :
    pathOfIsWalk hw hne =
      ((pathOfIsLink (cons_isWalk_iff.mp hw).1).trans
        ((pathOfIsWalk (cons_isWalk_iff.mp hw).2 (cons_nonempty y f w)).cast
          (vertexMk_congr rfl) (vertexMk_congr rfl))).cast
        (vertexMk_congr rfl) (vertexMk_congr rfl) :=
  rfl

lemma pathOfIsWalk_apply_cons_nil {x : α} {e : β} {y : α} (hw : G.IsWalk (cons x e (nil y)))
    (hne : (cons x e (nil y)).Nonempty) (t : I) :
    pathOfIsWalk hw hne t = pathOfIsLink (cons_isWalk_iff.mp hw).1 t := by
  rw [pathOfIsWalk_cons_nil]
  rfl

lemma pathOfIsWalk_apply_cons_cons {x : α} {e : β} {y : α} {f : β} {w : WList α β}
    (hw : G.IsWalk (cons x e (cons y f w))) (hne : (cons x e (cons y f w)).Nonempty) (t : I) :
    pathOfIsWalk hw hne t =
      ((pathOfIsLink (cons_isWalk_iff.mp hw).1).trans
        ((pathOfIsWalk (cons_isWalk_iff.mp hw).2 (cons_nonempty y f w)).cast
          (vertexMk_congr rfl) (vertexMk_congr rfl))) t := by
  rw [pathOfIsWalk_cons_cons]
  rfl

lemma edgePath_congr_mem {e : β} {he he' : e ∈ E(G)} (t : I) :
    edgePath ⟨e, he⟩ t = edgePath ⟨e, he'⟩ t := by
  have h : (⟨e, he⟩ : E(G)) = ⟨e, he'⟩ := Subtype.ext rfl
  rw [h]

-- lemma continuous_squishLeft : Continuous squishLeft :=
--   Continuous.subtype_mk (continuous_subtype_val.div_const 2) _

-- lemma continuous_squishRight : Continuous squishRight :=
--   Continuous.subtype_mk ((continuous_subtype_val.add continuous_const).div_const 2) _

-- lemma continuous_symm_I : Continuous (σ : I → I) :=
--   Continuous.subtype_mk (by simpa [coe_symm_eq] using continuous_const.sub continuous_subtype_val) _

-- lemma range_path_symm {X : Type*} [TopologicalSpace X] {x y : X} (P : Path x y) :
--     range P.symm = range P := by
--   ext z
--   simp only [mem_range, Path.symm_apply]
--   exact ⟨fun ⟨t, ht⟩ ↦ ⟨σ t, ht⟩, fun ⟨t, ht⟩ ↦ ⟨σ t, by simpa [symm_symm] using ht⟩⟩

-- lemma range_path_trans {X : Type*} [TopologicalSpace X] {x y z : X} (P : Path x y) (Q : Path y z) :
--     range (P.trans Q) = range P ∪ range Q := by
--   ext p
--   constructor
--   · rintro ⟨t, rfl⟩
--     rw [trans_apply_ite_lt]
--     split_ifs <;> simp [mem_union, mem_range]
--   · rintro (⟨t, rfl⟩ | ⟨t, rfl⟩)
--     · exact ⟨squishLeft t, trans_squishLeft t⟩
--     · exact ⟨squishRight t, trans_squishRight t⟩

-- lemma range_pathOfIsLink {e : β} {x y : α} (h : G.IsLink e x y) :
--     range (pathOfIsLink h) = range (edgePath ⟨e, h.edge_mem⟩) := by
--   unfold pathOfIsLink
--   split_ifs <;> simp [Path.cast_coe, range_path_symm]

-- /-- Reparametrize so a walk path traces a given walk-edge as a full `[0,1]` cell. -/
-- lemma exists_reparam_pathOfIsLink {e : β} {x y : α} (h : G.IsLink e x y) :
--     ∃ φ : C(I, I), ∀ t, pathOfIsLink h (φ t) = edgePath ⟨e, h.edge_mem⟩ t := by
--   unfold pathOfIsLink
--   split_ifs
--   · exact ⟨ContinuousMap.id _, fun t ↦ by simp [Path.cast_coe]⟩
--   · exact ⟨⟨σ, continuous_symm_I⟩, fun t ↦ by simp [Path.cast_coe, Path.symm_apply, symm_symm]⟩

-- lemma exists_reparam_pathOfIsWalk {w : WList α β} (hw : G.IsWalk w) (hne : w.Nonempty) {f : β}
--     (hf : f ∈ w.edge) :
--     ∃ φ : C(I, I), ∀ t,
--       pathOfIsWalk hw hne (φ t) = edgePath ⟨f, hw.edge_mem_of_mem hf⟩ t := by
--   match w, hne with
--   | .cons _x e (.nil _y), hne =>
--     have rfl : f = e := by simpa using hf
--     subst f
--     obtain ⟨φ, hφ⟩ := exists_reparam_pathOfIsLink (cons_isWalk_iff.mp hw).1
--     refine ⟨φ, fun t ↦ ?_⟩
--     rw [pathOfIsWalk_apply_cons_nil, hφ t]
--     exact edgePath_congr_mem t
--   | .cons _x e (.cons y g rest), hne =>
--     have hwalk := cons_isWalk_iff.mp hw
--     have hf' : f = e ∨ f ∈ (cons y g rest).edge := by simpa using hf
--     rcases hf' with rfl | hfrest
--     · obtain ⟨φ, hφ⟩ := exists_reparam_pathOfIsLink hwalk.1
--       refine ⟨⟨squishLeft, continuous_squishLeft⟩.comp φ, fun t ↦ ?_⟩
--       rw [pathOfIsWalk_apply_cons_cons, ContinuousMap.comp_apply, trans_squishLeft, hφ t]
--       exact edgePath_congr_mem t
--     · obtain ⟨φ, hφ⟩ := exists_reparam_pathOfIsWalk hwalk.2 (cons_nonempty y g rest) hfrest
--       refine ⟨⟨squishRight, continuous_squishRight⟩.comp φ, fun t ↦ ?_⟩
--       rw [pathOfIsWalk_apply_cons_cons, ContinuousMap.comp_apply, trans_squishRight, Path.cast_coe,
--         hφ t]
--       exact edgePath_congr_mem t

-- lemma range_pathOfIsWalk {w : WList α β} (hw : G.IsWalk w) (hne : w.Nonempty) :
--     range (pathOfIsWalk hw hne) =
--       ⋃ (e : β) (he : e ∈ w.edge), range (edgePath ⟨e, hw.edge_mem_of_mem he⟩) := by
--   refine subset_antisymm ?_ ?_
--   · intro z hz
--     obtain ⟨t, rfl⟩ := hz
--     match w, hne with
--     | .cons _x e (.nil _y), hne =>
--       simp only [mem_iUnion]
--       refine ⟨e, by simp, ?_⟩
--       have : pathOfIsWalk hw hne t ∈ range (pathOfIsLink (cons_isWalk_iff.mp hw).1) :=
--         ⟨t, (pathOfIsWalk_apply_cons_nil hw hne t).symm⟩
--       rw [range_pathOfIsLink] at this
--       obtain ⟨s, hs⟩ := this
--       exact ⟨s, hs.trans (edgePath_congr_mem s)⟩
--     | .cons _x e (.cons y g rest), hne =>
--       have hwalk := cons_isWalk_iff.mp hw
--       have hz : pathOfIsWalk hw hne t ∈
--           range (pathOfIsLink hwalk.1) ∪
--             range (pathOfIsWalk hwalk.2 (cons_nonempty y g rest)) := by
--         have : pathOfIsWalk hw hne t ∈ range
--             ((pathOfIsLink hwalk.1).trans
--               ((pathOfIsWalk hwalk.2 (cons_nonempty y g rest)).cast
--                 (vertexMk_congr rfl) (vertexMk_congr rfl))) :=
--           ⟨t, (pathOfIsWalk_apply_cons_cons hw hne t).symm⟩
--         simpa [range_path_trans, Path.cast_coe] using this
--       simp only [mem_iUnion]
--       rcases hz with hzP | hzQ
--       · rw [range_pathOfIsLink] at hzP
--         obtain ⟨s, hs⟩ := hzP
--         exact ⟨e, by simp, s, hs.trans (edgePath_congr_mem s)⟩
--       · rw [range_pathOfIsWalk hwalk.2 (cons_nonempty y g rest)] at hzQ
--         simp only [mem_iUnion] at hzQ
--         obtain ⟨f, hf, hzQ⟩ := hzQ
--         obtain ⟨s, hs⟩ := hzQ
--         exact ⟨f, List.mem_cons_of_mem _ hf, s, hs.trans (edgePath_congr_mem s)⟩
--   · intro z hz
--     simp only [mem_iUnion] at hz
--     obtain ⟨e, he, t, rfl⟩ := hz
--     obtain ⟨φ, hφ⟩ := exists_reparam_pathOfIsWalk hw hne he
--     exact ⟨φ t, hφ t⟩

-- lemma vertexMk_mem_range_pathOfIsWalk {w : WList α β} (hw : G.IsWalk w) (hne : w.Nonempty)
--     {x : α} (hx : x ∈ w) :
--     vertexMk ⟨x, hw.vertex_mem_of_mem hx⟩ ∈ range (pathOfIsWalk hw hne) := by
--   obtain ⟨y, e, hlink⟩ := hne.mem_iff_exists_isLink.mp hx
--   have he : e ∈ w.edge := hlink.edge_mem
--   have hG := hw.isLink_mono hlink
--   rw [range_pathOfIsWalk]
--   refine ⟨e, he, ?_⟩
--   obtain ⟨hxsrc, _⟩ | ⟨hxtgt, _⟩ :=
--     hG.eq_and_eq_or_eq_and_eq (G.isLink_source_target hG.edge_mem)
--   · exact ⟨0, (Path.source _).trans (vertexMk_congr hxsrc.symm)⟩
--   · exact ⟨1, (Path.target _).trans (vertexMk_congr hxtgt.symm)⟩

-- lemma range_RealizationEmbedding {H G : Graph α β} (h : H ≤ G) :
--     range h.RealizationEmbedding =
--       range (fun v : V(H) ↦ vertexMk ⟨v.val, h.vertexSet_mono v.prop⟩) ∪
--       ⋃ e : E(H), range (G.edgePath ⟨e.val, edgeSet_mono h e.prop⟩) := by
--   ext z
--   simp only [mem_range, mem_union, mem_iUnion]
--   constructor
--   · rintro ⟨x, rfl⟩
--     induction x using Realization.ind with | h a =>
--     match a with
--     | .inl v => exact Or.inl ⟨v, h.RealizationEmbedding_vertexMk v⟩
--     | .inr ⟨e, t⟩ => exact Or.inr ⟨e, t, h.RealizationEmbedding_edgePath e t⟩
--   · rintro (⟨v, rfl⟩ | ⟨e, t, rfl⟩)
--     · exact ⟨vertexMk v, h.RealizationEmbedding_vertexMk v⟩
--     · exact ⟨edgePath e t, h.RealizationEmbedding_edgePath e t⟩

/-- Interior points of a concatenated walk path are internal vertices or open edge cells.
The `Path.cast` endpoints are not definitionally the walk's `first`/`last` subtypes, so
membership has to be transported along `⇑` rather than by rewriting the `Path` term. -/
lemma pathOfIsWalk_interior_subset {w : WList α β} (hw : G.IsWalk w) (hne : w.Nonempty) :
    (pathOfIsWalk hw hne).Interior ⊆
      {z | ∃ x, ∃ hx : x ∈ w.internalVertexSet,
          z = vertexMk ⟨x, hw.vertex_mem_of_mem (mem_of_mem_internalVertexSet hx)⟩} ∪
      {z | ∃ e, ∃ he : e ∈ w.edge, ∃ t, t ∈ Ioo (0 : I) 1 ∧
          z = edgePath ⟨e, hw.edge_mem_of_mem he⟩ t} := by
  match w, hne with
  | .cons x e (.nil y), hne =>
    intro z hz
    obtain ⟨t, ht, htzeq⟩ := hz
    have hfun : pathOfIsWalk hw hne t = pathOfIsLink (cons_isWalk_iff.mp hw).1 t :=
      pathOfIsWalk_apply_cons_nil hw hne t
    have hzI : z ∈ (pathOfIsLink (cons_isWalk_iff.mp hw).1).Interior :=
      ⟨t, ht, hfun.symm.trans htzeq⟩
    rw [pathOfIsLink_interior] at hzI
    obtain ⟨s, hs, hs'⟩ := hzI
    exact .inr ⟨e, by simp, s, hs, hs'.symm.trans (edgePath_congr_mem s)⟩
  | .cons x e (.cons y f rest), hne =>
    intro z hz
    obtain ⟨t, ht, htzeq⟩ := hz
    have hfun : pathOfIsWalk hw hne t =
        ((pathOfIsLink (cons_isWalk_iff.mp hw).1).trans
          ((pathOfIsWalk (cons_isWalk_iff.mp hw).2 (cons_nonempty y f rest)).cast
            (vertexMk_congr rfl) (vertexMk_congr rfl))) t :=
      pathOfIsWalk_apply_cons_cons hw hne t
    have hzT : z ∈ ((pathOfIsLink (cons_isWalk_iff.mp hw).1).trans
        ((pathOfIsWalk (cons_isWalk_iff.mp hw).2 (cons_nonempty y f rest)).cast
          (vertexMk_congr rfl) (vertexMk_congr rfl))).Interior :=
      ⟨t, ht, hfun.symm.trans htzeq⟩
    rw [path_trans_interior] at hzT
    rcases hzT with hz | hzQ
    · rcases hz with hzP | hzmid
      · rw [pathOfIsLink_interior] at hzP
        obtain ⟨s, hs, hs'⟩ := hzP
        exact .inr ⟨e, by simp, s, hs, hs'.symm.trans (edgePath_congr_mem s)⟩
      · rw [mem_singleton_iff] at hzmid
        refine .inl ⟨y, ?_, hzmid.trans (vertexMk_congr rfl)⟩
        · rw [internalVertexSet_cons_cons]
          exact mem_insert _ _
    · rw [path_cast_interior] at hzQ
      obtain hzI | hzE := pathOfIsWalk_interior_subset _ _ hzQ
      · obtain ⟨u, hu, hu'⟩ := hzI
        refine .inl ⟨u, ?_, hu'.trans (vertexMk_congr rfl)⟩
        · rw [internalVertexSet_cons_cons]
          exact mem_insert_of_mem _ hu
      · obtain ⟨ee, hee, s, hs, hs'⟩ := hzE
        exact .inr ⟨ee, List.mem_cons_of_mem _ hee, s, hs, hs'.trans (edgePath_congr_mem s)⟩

lemma pathOfIsWalk_injOn_Ioo_of_simple {w : WList α β} (hw : G.IsWalk w) (hne : w.Nonempty)
    (hsimple : G.IsPath w ∨ G.IsCyclicWalk w) :
    InjOn (pathOfIsWalk hw hne) (Ioo (0 : I) 1) := by
  sorry

/-- Two graphs are topologically equivalent when their realizations are homeomorphic. For finite
graphs, the intended combinatorial source of such a homeomorphism is an isomorphism followed by
edge subdivisions. -/
def TopologicallyEquivalent (G : Graph α β) (H : Graph γ δ) : Prop :=
  Nonempty (Realization G ≃ₜ Realization H)

namespace IsoTopologicalMinor

variable (M : H.IsoTopologicalMinor G)

open Classical

lemma route_isWalk (e : E(H)) : G.IsWalk (M.route e) :=
  (M.route_isSimple e).elim (·.isWalk) (fun h ↦ h.isTrail.isWalk)

lemma route_ends_source_target (e : E(H)) :
    s(M.branchVertex (edgeSource e), M.branchVertex (edgeTarget e)) =
      s((M.route e).first, (M.route e).last) := by
  have hends : H.ends e = s(edgeSource e, edgeTarget e) :=
    (isLink_edgeSource_edgeTarget e).ends_eq
  rw [← M.route_ends e, hends, Sym2.map_mk]

/-- Reverse the model route when it runs from target to source. -/
noncomputable def orientedRoute (e : E(H)) : WList α β :=
  if (M.route e).first = M.branchVertex (edgeSource e) then M.route e
  else (M.route e).reverse

lemma orientedRoute_eq_or_reverse (e : E(H)) :
    M.orientedRoute e = M.route e ∨ M.orientedRoute e = (M.route e).reverse := by
  unfold orientedRoute
  split_ifs <;> simp

lemma orientedRoute_isWalk (e : E(H)) : G.IsWalk (M.orientedRoute e) := by
  unfold orientedRoute
  split_ifs
  · exact M.route_isWalk e
  · exact (M.route_isWalk e).reverse

lemma orientedRoute_nonempty (e : E(H)) : (M.orientedRoute e).Nonempty := by
  unfold orientedRoute
  split_ifs
  · exact M.route_nonempty e
  · exact (M.route_nonempty e).reverse

lemma orientedRoute_isSimple (e : E(H)) :
    G.IsPath (M.orientedRoute e) ∨ G.IsCyclicWalk (M.orientedRoute e) := by
  unfold orientedRoute
  split_ifs
  · exact M.route_isSimple e
  · exact (M.route_isSimple e).imp (·.reverse) (·.reverse)

lemma orientedRoute_first (e : E(H)) :
    (M.orientedRoute e).first = M.branchVertex (edgeSource e) := by
  unfold orientedRoute
  split_ifs with h
  · exact h
  · obtain ⟨h1, _⟩ | ⟨h1, _⟩ := Sym2.eq_iff.mp (M.route_ends_source_target e)
    · exact (h h1.symm).elim
    · simpa [reverse_first] using h1.symm

lemma orientedRoute_last (e : E(H)) :
    (M.orientedRoute e).last = M.branchVertex (edgeTarget e) := by
  unfold orientedRoute
  split_ifs with hf
  · obtain ⟨_, h2⟩ | ⟨h1, h2⟩ := Sym2.eq_iff.mp (M.route_ends_source_target e)
    · exact h2.symm
    · exact h1.symm.trans (hf.symm.trans h2.symm)
  · obtain ⟨h1, _⟩ | ⟨_, h2⟩ := Sym2.eq_iff.mp (M.route_ends_source_target e)
    · exact (hf h1.symm).elim
    · simpa [reverse_last] using h2.symm

/-- The path in the host realization obtained by concatenating the closed cells along one model
route, reoriented to the preferred source and target of the pattern edge. -/
noncomputable def routePath (e : E(H)) :
    Path (vertexMk ⟨M.branchVertex (edgeSource e), M.branchVertex_mem (edgeSource e)⟩)
      (vertexMk ⟨M.branchVertex (edgeTarget e), M.branchVertex_mem (edgeTarget e)⟩) :=
  (pathOfIsWalk (M.orientedRoute_isWalk e) (M.orientedRoute_nonempty e)).cast
    (vertexMk_congr (M.orientedRoute_first e).symm)
    (vertexMk_congr (M.orientedRoute_last e).symm)

/-- A route path is injective on the open interval; loops are allowed, so no endpoint inequality
is asserted. -/
theorem routePath_injOn (e : E(H)) :
    InjOn (M.routePath e) (Ioo (0 : unitInterval) 1) := by
  intro s hs t ht heq
  exact pathOfIsWalk_injOn_Ioo_of_simple (M.orientedRoute_isWalk e) (M.orientedRoute_nonempty e)
    (M.orientedRoute_isSimple e) hs ht (by simpa [routePath, Path.cast_coe] using heq)

theorem routePath_interior_disjoint_branchVertices (e : E(H)) :
    Disjoint (M.routePath e).Interior
      (range fun v : V(H) ↦ vertexMk ⟨M.branchVertex v, M.branchVertex_mem v⟩) := by
  refine disjoint_left.mpr ?_
  intro z hz hzV
  have hz' : z ∈ (pathOfIsWalk (M.orientedRoute_isWalk e)
      (M.orientedRoute_nonempty e)).Interior := by
    simpa [routePath, path_cast_interior] using hz
  obtain hzI | hzE := pathOfIsWalk_interior_subset _ _ hz'
  · obtain ⟨x, hx, rfl⟩ := hzI
    obtain ⟨v, hv⟩ := hzV
    have hx' : x ∈ (M.route e).internalVertexSet := by
      simpa [orientedRoute, apply_ite (fun w : WList α β ↦ w.internalVertexSet),
        internalVertexSet_reverse] using hx
    exact (M.route_internal_disjoint_branchVertices e).notMem_of_mem_left hx' ⟨v, by
      simpa [vertexMk_inj, Subtype.ext_iff] using hv⟩
  · obtain ⟨_, _, t, ht, rfl⟩ := hzE
    obtain ⟨v, hv⟩ := hzV
    exact vertexMk_not_mem_edgePath_Ioo _ _ ⟨t, ht, hv.symm⟩

theorem routePath_interior_disjoint {e f : E(H)} (hef : e ≠ f) :
    Disjoint (M.routePath e).Interior (M.routePath f).Interior := by
  refine disjoint_left.mpr ?_
  intro z hze hzf
  have hze' : z ∈ (pathOfIsWalk (M.orientedRoute_isWalk e)
      (M.orientedRoute_nonempty e)).Interior := by
    simpa [routePath, path_cast_interior] using hze
  have hzf' : z ∈ (pathOfIsWalk (M.orientedRoute_isWalk f)
      (M.orientedRoute_nonempty f)).Interior := by
    simpa [routePath, path_cast_interior] using hzf
  obtain hzeI | hzeE := pathOfIsWalk_interior_subset _ _ hze'
  · obtain ⟨x, hxe, rfl⟩ := hzeI
    obtain hzfI | hzfE := pathOfIsWalk_interior_subset _ _ hzf'
    · obtain ⟨y, hyf, hy⟩ := hzfI
      have hxe' : x ∈ (M.route e).internalVertexSet := by
        simpa [orientedRoute, apply_ite (fun w : WList α β ↦ w.internalVertexSet),
          internalVertexSet_reverse] using hxe
      have hyf' : y ∈ (M.route f).internalVertexSet := by
        simpa [orientedRoute, apply_ite (fun w : WList α β ↦ w.internalVertexSet),
          internalVertexSet_reverse] using hyf
      have hxy : x = y := by
        simpa [vertexMk_inj, Subtype.ext_iff] using hy
      exact (M.route_internal_disjoint e f hef).notMem_of_mem_left hxe' (hxy ▸ hyf')
    · obtain ⟨_, _, t, ht, ht'⟩ := hzfE
      exact vertexMk_not_mem_edgePath_Ioo _ _ ⟨t, ht, ht'.symm⟩
  · obtain ⟨ee, hee, t, ht, rfl⟩ := hzeE
    obtain hzfI | hzfE := pathOfIsWalk_interior_subset _ _ hzf'
    · obtain ⟨y, _, hy⟩ := hzfI
      exact vertexMk_not_mem_edgePath_Ioo _ _ ⟨t, ht, hy⟩
    · obtain ⟨ef, hefE, s, hs, hseq⟩ := hzfE
      have hee' : ee ∈ E(M.route e) := by
        unfold orientedRoute at hee
        split_ifs at hee
        · exact hee
        · simpa [reverse_edgeSet] using hee
      have hef' : ef ∈ E(M.route f) := by
        unfold orientedRoute at hefE
        split_ifs at hefE
        · exact hefE
        · simpa [reverse_edgeSet] using hefE
      have hne : (⟨ee, (M.route_isWalk e).edge_mem_of_mem (mem_edgeSet_iff.mp hee')⟩ : E(G)) ≠
          ⟨ef, (M.route_isWalk f).edge_mem_of_mem (mem_edgeSet_iff.mp hef')⟩ := by
        intro h
        have heq : ee = ef := congrArg Subtype.val h
        subst heq
        exact (M.route_edge_disjoint e f hef).notMem_of_mem_left hee' hef'
      exact ((disjoint_edgePath_Ioo_iff _ _).mpr hne).notMem_of_mem_left
        ⟨t, ht, rfl⟩ ⟨s, hs, hseq.symm⟩

/-- The drawing of the pattern into the host realization along a topological-minor witness. -/
noncomputable def realizationDrawing (M : H.IsoTopologicalMinor G) :
    Drawing H (Realization G) :=
  Drawing.ofVertexAndEdgePaths
    (fun v ↦ vertexMk ⟨M.branchVertex v, M.branchVertex_mem v⟩)
    (vertexMk_injective.comp fun _ _ h ↦ M.branchVertex.injective (congrArg Subtype.val h))
    M.routePath M.routePath_injOn
    M.routePath_interior_disjoint_branchVertices
    fun _ _ hef ↦ M.routePath_interior_disjoint hef

/-- The continuous map of realizations that sends branch vertices to branch vertices and each
pattern edge along its route in the host. -/
noncomputable def realizationMap (M : H.IsoTopologicalMinor G) :
    C(Realization H, Realization G) :=
  M.realizationDrawing.toContinuousMap

/-- The realization map sends a vertex to its branch vertex. -/
@[simp]
theorem realizationMap_vertex (v : V(H)) :
    M.realizationMap (vertexMk v) =
      vertexMk ⟨M.branchVertex v, M.branchVertex_mem v⟩ :=
  Drawing.ofVertexAndEdgePaths_vertex v

/-- On a closed pattern edge, the realization map is the corresponding concatenated route path. -/
theorem realizationMap_edgePath (e : E(H)) (t : unitInterval) :
    M.realizationMap (H.edgePath e t) = M.routePath e t := by
  rw [realizationMap, Drawing.coe_toContinuousMap, ← Drawing.edgePath_apply]
  exact Drawing.ofVertexAndEdgePaths_edgePath_apply e t

/-- The realization map of a topological-minor witness is injective. -/
theorem realizationMap_injective : Injective M.realizationMap :=
  M.realizationDrawing.injective

/-- The image of the realization map is the realization of the used subgraph, included in the
host realization. -/
theorem range_realizationMap :
    range (IsoTopologicalMinor.realizationMap M) =
      range (M.usedSubgraph_le.realizationContinuousMap) := by
  sorry

end IsoTopologicalMinor

namespace IsoSubdivision

variable (S : H.IsoSubdivision G)

/-- Exhaustiveness of a subdivision makes the realization map onto the refined realization. -/
theorem realizationMap_surjective : Surjective (S.realizationMap) := by
  sorry

/-- The inverse point map sends each refined cell to the appropriate subinterval of its coarse
edge. -/
noncomputable def inverseRealizationMap (S : H.IsoSubdivision G) :
    Realization G → Realization H := by
  sorry

theorem inverseRealizationMap_leftInverse :
    LeftInverse S.inverseRealizationMap (S.realizationMap) := by
  sorry

theorem inverseRealizationMap_rightInverse :
    RightInverse S.inverseRealizationMap (S.realizationMap) := by
  sorry

/-- Continuity of the inverse is checked one refined closed cell at a time. -/
theorem continuous_inverseRealizationMap : Continuous S.inverseRealizationMap := by
  sorry

/-- The homeomorphism from the realization of a subdivision to the realization of the graph it
subdivides. Its inverse cuts every coarse edge into the cells of its subdivision route. -/
noncomputable def realizationHomeomorph (S : H.IsoSubdivision G) :
    Realization G ≃ₜ Realization H := by
  sorry

/-- The subdivision homeomorphism sends every branch vertex to its corresponding coarse vertex. -/
@[simp]
theorem realizationHomeomorph_branchVertex (v : V(H)) :
    S.realizationHomeomorph (vertexMk ⟨S.branchVertex v, S.branchVertex_mem v⟩) = vertexMk v := by
  sorry

/-- A subdivision exhibits the two graphs as topologically equivalent. -/
theorem topologicallyEquivalent (S : H.IsoSubdivision G) : G.TopologicallyEquivalent H :=
  ⟨IsoSubdivision.realizationHomeomorph S⟩

end IsoSubdivision

namespace Drawing

variable {D : Drawing G X}

/-- Pull a drawing back along a homeomorphism of graph realizations. -/
noncomputable def ofHomeomorph (D : Drawing G X) (h : Realization H ≃ₜ Realization G) :
    Drawing H X where
  toContinuousMap := ⟨D ∘ h, D.continuous.comp h.continuous⟩
  inj' := D.injective.comp h.injective

@[simp]
theorem ofHomeomorph_apply (D : Drawing G X) (h : Realization H ≃ₜ Realization G)
    (x : Realization H) : D.ofHomeomorph h x = D (h x) :=
  rfl

/-- Pulling a drawing back along a homeomorphism does not change its image. -/
@[simp]
theorem support_ofHomeomorph (D : Drawing G X) (h : Realization H ≃ₜ Realization G) :
    (D.ofHomeomorph h).support = D.support := by
  ext x
  simp only [support, mem_range, ofHomeomorph_apply]
  exact ⟨fun ⟨y, hy⟩ ↦ ⟨h y, hy⟩, fun ⟨z, hz⟩ ↦ ⟨h.symm z, by simp [hz]⟩⟩

/-- Restrict a drawing to the subdivision model of a topological minor. -/
noncomputable def ofIsoTopologicalMinor (D : Drawing G X) (M : H.IsoTopologicalMinor G) :
    Drawing H X where
  toContinuousMap := ⟨D ∘ IsoTopologicalMinor.realizationMap M,
    D.continuous.comp (IsoTopologicalMinor.realizationMap M).continuous⟩
  inj' := D.injective.comp (IsoTopologicalMinor.realizationMap_injective M)

/-- A drawing of a topological minor uses no points outside the host drawing. -/
theorem support_ofIsoTopologicalMinor_subset (D : Drawing G X) (M : H.IsoTopologicalMinor G) :
    (D.ofIsoTopologicalMinor M).support ⊆ D.support := by
  rintro _ ⟨x, rfl⟩
  exact ⟨IsoTopologicalMinor.realizationMap M x, rfl⟩

/-- Subdivide the cells of a drawing. The resulting drawing has the refined graph as its domain. -/
noncomputable def subdivide (D : Drawing H X) (S : H.IsoSubdivision G) : Drawing G X :=
  D.ofHomeomorph (IsoSubdivision.realizationHomeomorph S)

/-- Suppress the subdivision vertices of a drawing. -/
noncomputable def suppress (D : Drawing G X) (S : H.IsoSubdivision G) : Drawing H X :=
  D.ofHomeomorph (IsoSubdivision.realizationHomeomorph S).symm

/-- Subdividing a drawing preserves its image exactly. -/
@[simp]
theorem support_subdivide (D : Drawing H X) (S : H.IsoSubdivision G) :
    (D.subdivide S).support = D.support :=
  D.support_ofHomeomorph _

/-- Suppressing subdivision vertices preserves the image exactly. -/
@[simp]
theorem support_suppress (D : Drawing G X) (S : H.IsoSubdivision G) :
    (D.suppress S).support = D.support :=
  D.support_ofHomeomorph _

/-- Transport a drawing across a topological equivalence without changing its image. -/
noncomputable def ofTopologicallyEquivalent (D : Drawing G X) (h : H.TopologicallyEquivalent G) :
    Drawing H X :=
  D.ofHomeomorph h.some

@[simp]
theorem support_ofTopologicallyEquivalent (D : Drawing G X) (h : H.TopologicallyEquivalent G) :
    (D.ofTopologicallyEquivalent h).support = D.support :=
  D.support_ofHomeomorph _

end Drawing

namespace IsDrawable

/-- Drawability is inherited by up-to-isomorphism topological minors. -/
theorem isoTopologicalMinor (hG : G.IsDrawable X) (M : H.IsoTopologicalMinor G) : H.IsDrawable X :=
  ⟨hG.some.ofIsoTopologicalMinor M⟩

/-- Subdivision does not change drawability in a fixed topological space. -/
theorem isoSubdivision_iff (S : H.IsoSubdivision G) : H.IsDrawable X ↔ G.IsDrawable X :=
  ⟨fun h ↦ ⟨h.some.subdivide S⟩, fun h ↦ ⟨h.some.suppress S⟩⟩

end IsDrawable

namespace Planar

/-- Planarity is inherited by up-to-isomorphism topological minors. -/
theorem isoTopologicalMinor (hG : G.Planar) (M : H.IsoTopologicalMinor G) : H.Planar :=
  IsDrawable.isoTopologicalMinor hG M

/-- Subdivision does not change planarity. -/
theorem isoSubdivision_iff (S : H.IsoSubdivision G) : H.Planar ↔ G.Planar :=
  IsDrawable.isoSubdivision_iff S

end Planar

end


end Graph
