/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Matroid.Graph.Transport
public import Matroid.Graph.Minor.Walk

/-!
# Walks under graph isomorphism

Canonical transport of supported walks and bundled paths. IRw registrations are attached directly
to the project-owned equivalences and naturality theorems that they describe.
-/

@[expose] public section

open Set

namespace Graph

universe uV uE uV' uE'

variable {V : Type uV} {E : Type uE} {V' : Type uV'} {E' : Type uE'}
  {G : Graph V E} {H : Graph V' E'}

/-! ## Supported walks -/

/-- Transport a walk whose vertices and edges are certified to belong to the source graph.

The first-vertex equation is carried alongside the transported walk so that the recursive `cons`
case can transport its linking edge without choosing ambient default vertices. -/
def Iso.walkMapAux (i : Iso G H) :
    (W : WList V E) → (hW : G.IsWalk W) →
      {W' : WList V' E' //
        H.IsWalk W' ∧
          W'.first = (i.vertexEquiv ⟨W.first, hW.first_mem⟩).1}
  | .nil x, hW =>
      ⟨.nil (i.vertexEquiv ⟨x, hW.first_mem⟩).1,
        IsWalk.nil (i.vertexEquiv ⟨x, hW.first_mem⟩).2, rfl⟩
  | .cons x e W, hW => by
      have hW' := hW.of_cons
      have he := (cons_isWalk_iff.mp hW).1
      let W' := walkMapAux i W hW'
      let hx : V(G) := ⟨x, he.left_mem⟩
      let hf : E(G) := ⟨e, he.edge_mem⟩
      let hy : V(G) := ⟨W.first, hW'.first_mem⟩
      have he' := (i.isLink_edgeEquiv_vertexEquiv hf hx hy).mp he
      refine ⟨.cons (i.vertexEquiv hx).1 (i.edgeEquiv hf).1 W'.1,
        W'.2.1.cons ?_, ?_⟩
      · rwa [W'.2.2]
      · change (i.vertexEquiv hx).1 =
          (i.vertexEquiv ⟨x, hW.first_mem⟩).1
        congr 2

/-- The underlying raw `WList` obtained by transporting a supported walk. -/
def Iso.walkMap (i : Iso G H) (W : {W : WList V E // G.IsWalk W}) :
    {W' : WList V' E' // H.IsWalk W'} :=
  ⟨(walkMapAux i W.1 W.2).1, (walkMapAux i W.1 W.2).2.1⟩

/-- Applying the supported walk transport and then its symmetric transport recovers the raw walk. -/
theorem Iso.walkMap_symm_apply_val (i : Iso G H) {W : WList V E}
    (hW : G.IsWalk W) :
    (walkMap i.symm (walkMap i ⟨W, hW⟩)).1 = W := by
  induction W with
  | nil x =>
      simp only [Iso.walkMap, Iso.walkMapAux, WList.nil_inj_iff]
      exact congrArg Subtype.val (i.vertexEquiv.symm_apply_apply ⟨x, hW.first_mem⟩)
  | cons x e W ih =>
      simp only [Iso.walkMap, Iso.walkMapAux]
      rw [WList.cons_inj_iff]
      refine ⟨?_, ?_, ?_⟩
      · exact congrArg Subtype.val
          (i.vertexEquiv.symm_apply_apply ⟨x, (cons_isWalk_iff.mp hW).1.left_mem⟩)
      · exact congrArg Subtype.val
          (i.edgeEquiv.symm_apply_apply ⟨e, (cons_isWalk_iff.mp hW).1.edge_mem⟩)
      · exact ih hW.of_cons

/-- Applying the supported walk transport and then its symmetric transport is the identity. -/
theorem Iso.walkMap_symm_apply (i : Iso G H)
    (W : {W : WList V E // G.IsWalk W}) :
    walkMap i.symm (walkMap i W) = W := by
  exact Subtype.ext (walkMap_symm_apply_val i W.2)

/-- Edge membership is preserved by supported walk transport. -/
theorem Iso.walkMap_edge_mem_iff (i : Iso G H) {W : WList V E}
    (hW : G.IsWalk W) (f : E(G)) :
    (i.edgeEquiv f).1 ∈ (i.walkMap ⟨W, hW⟩).1.edge ↔ f.1 ∈ W.edge := by
  induction W with
  | nil x => simp [Iso.walkMap, Iso.walkMapAux]
  | cons x e W ih =>
      simp only [Iso.walkMap, Iso.walkMapAux, WList.cons_edge, List.mem_cons]
      constructor
      · rintro (hef | hfW)
        · left
          have hsub : i.edgeEquiv f =
              i.edgeEquiv ⟨e, (cons_isWalk_iff.mp hW).1.edge_mem⟩ := Subtype.ext hef
          exact congrArg Subtype.val (i.edgeEquiv.injective hsub)
        · right
          exact (ih hW.of_cons).mp hfW
      · rintro (hef | hfW)
        · left
          subst e
          rfl
        · right
          exact (ih hW.of_cons).mpr hfW

/-- Vertex membership is preserved by supported walk transport. -/
theorem Iso.walkMap_vertex_mem_iff (i : Iso G H) {W : WList V E}
    (hW : G.IsWalk W) (x : V(G)) :
    (i.vertexEquiv x).1 ∈ (i.walkMap ⟨W, hW⟩).1 ↔ x.1 ∈ W := by
  induction W with
  | nil y =>
      simp only [Iso.walkMap, Iso.walkMapAux, WList.mem_nil_iff]
      constructor
      · intro hxy
        have hsub : i.vertexEquiv x = i.vertexEquiv ⟨y, hW.first_mem⟩ :=
          Subtype.ext hxy
        exact congrArg Subtype.val (i.vertexEquiv.injective hsub)
      · rintro rfl
        rfl
  | cons y e W ih =>
      simp only [Iso.walkMap, Iso.walkMapAux, WList.mem_cons_iff]
      constructor
      · rintro (hxy | hxW)
        · left
          have hsub : i.vertexEquiv x =
              i.vertexEquiv ⟨y, (cons_isWalk_iff.mp hW).1.left_mem⟩ := Subtype.ext hxy
          exact congrArg Subtype.val (i.vertexEquiv.injective hsub)
        · right
          exact (ih hW.of_cons).mp hxW
      · rintro (hxy | hxW)
        · left
          subst y
          rfl
        · right
          exact (ih hW.of_cons).mpr hxW

/-- The first vertex of a transported walk is the transported first vertex. -/
theorem Iso.walkMap_first (i : Iso G H) {W : WList V E} (hW : G.IsWalk W) :
    (i.walkMap ⟨W, hW⟩).1.first =
      (i.vertexEquiv ⟨W.first, hW.first_mem⟩).1 :=
  (i.walkMapAux W hW).2.2

/-- The last vertex of a transported walk is the transported last vertex. -/
theorem Iso.walkMap_last (i : Iso G H) {W : WList V E} (hW : G.IsWalk W) :
    (i.walkMap ⟨W, hW⟩).1.last =
      (i.vertexEquiv ⟨W.last, hW.last_mem⟩).1 := by
  induction W with
  | nil x => rfl
  | cons x e W ih =>
      simpa only [Iso.walkMap, Iso.walkMapAux, WList.last_cons] using ih hW.of_cons

/-- Supported walk transport commutes with appending a linked edge and endpoint. -/
theorem Iso.walkMap_concat (i : Iso G H) {W : WList V E} {e : E} {x : V}
    (hW : G.IsWalk W)
    (he : G.IsLink e W.last x) :
    (i.walkMap ⟨W.concat e x, hW.concat he⟩).1 =
      (i.walkMap ⟨W, hW⟩).1.concat
        (i.edgeEquiv ⟨e, he.edge_mem⟩).1
        (i.vertexEquiv ⟨x, he.right_mem⟩).1 := by
  induction W with
  | nil y => rfl
  | cons y f W ih =>
      simp only [WList.cons_concat, Iso.walkMap, Iso.walkMapAux, WList.cons_inj_iff]
      exact ⟨True.intro, True.intro, ih hW.of_cons he⟩

/-- Supported walk transport commutes with reversing the walk. -/
theorem Iso.walkMap_reverse (i : Iso G H) {W : WList V E} (hW : G.IsWalk W) :
    (i.walkMap ⟨W.reverse, hW.reverse⟩).1 =
      (i.walkMap ⟨W, hW⟩).1.reverse := by
  induction W with
  | nil x => rfl
  | cons x e W ih =>
      have htail := hW.of_cons
      have hlink := (cons_isWalk_iff.mp hW).1
      have hrevlink : G.IsLink e W.reverse.last x := by simpa using hlink.symm
      change (i.walkMap ⟨W.reverse.concat e x, htail.reverse.concat hrevlink⟩).1 =
        (WList.cons (i.vertexEquiv ⟨x, hlink.left_mem⟩).1
          (i.edgeEquiv ⟨e, hlink.edge_mem⟩).1
          (i.walkMap ⟨W, htail⟩).1).reverse
      rw [i.walkMap_concat htail.reverse hrevlink]
      simp only [WList.reverse_cons]
      rw [ih htail]

/-- Supported walk transport preserves trails. -/
theorem Iso.isTrail_walkMap (i : Iso G H) {W : WList V E} (hW : G.IsTrail W) :
    H.IsTrail (i.walkMap ⟨W, hW.isWalk⟩).1 := by
  induction W with
  | nil x =>
      exact nil_isTrail (i.walkMap ⟨.nil x, hW.isWalk⟩).2.first_mem
  | cons x e W ih =>
      rw [cons_isTrail_iff] at hW
      simp only [Iso.walkMap, Iso.walkMapAux, cons_isTrail_iff]
      refine ⟨ih hW.1, ?_, ?_⟩
      · rw [(i.walkMapAux W hW.1.isWalk).2.2]
        exact (i.isLink_edgeEquiv_vertexEquiv ⟨e, hW.2.1.edge_mem⟩ ⟨x, hW.2.1.left_mem⟩
          ⟨W.first, hW.1.isWalk.first_mem⟩).mp hW.2.1
      · intro heW
        exact hW.2.2 <| (i.walkMap_edge_mem_iff hW.1.isWalk
          ⟨e, hW.2.1.edge_mem⟩).mp heW

/-- Supported walk transport preserves paths. -/
theorem Iso.isPath_walkMap (i : Iso G H) {W : WList V E} (hW : G.IsPath W) :
    H.IsPath (i.walkMap ⟨W, hW.isWalk⟩).1 := by
  induction W with
  | nil x =>
      exact nil_isPath (i.walkMap ⟨.nil x, hW.isWalk⟩).2.first_mem
  | cons x e W ih =>
      rw [cons_isPath_iff] at hW
      simp only [Iso.walkMap, Iso.walkMapAux, cons_isPath_iff]
      refine ⟨?_, ih hW.2.1, ?_⟩
      · rw [(i.walkMapAux W hW.2.1.isWalk).2.2]
        exact (i.isLink_edgeEquiv_vertexEquiv ⟨e, hW.1.edge_mem⟩ ⟨x, hW.1.left_mem⟩
          ⟨W.first, hW.2.1.isWalk.first_mem⟩).mp hW.1
      · intro hxW
        exact hW.2.2 <| (i.walkMap_vertex_mem_iff hW.2.1.isWalk
          ⟨x, hW.1.left_mem⟩).mp hxW

/-- Supported walk transport preserves tours. -/
theorem Iso.isTour_walkMap (i : Iso G H) {W : WList V E} (hW : G.IsTour W) :
    H.IsTour (i.walkMap ⟨W, hW.isTrail.isWalk⟩).1 where
  toIsTrail := i.isTrail_walkMap hW.isTrail
  nonempty := by
    have hne := hW.nonempty
    cases W with
    | nil x => simp at hne
    | cons x e W => simp [Iso.walkMap, Iso.walkMapAux]
  isClosed := by
    change (i.walkMap ⟨W, hW.isTrail.isWalk⟩).1.first =
      (i.walkMap ⟨W, hW.isTrail.isWalk⟩).1.last
    rw [i.walkMap_first, i.walkMap_last]
    have hsub : (⟨W.first, hW.isTrail.isWalk.first_mem⟩ : V(G)) =
        ⟨W.last, hW.isTrail.isWalk.last_mem⟩ := Subtype.ext hW.isClosed
    exact congrArg Subtype.val (congrArg i.vertexEquiv hsub)

/-- Supported walk transport preserves cyclic walks. -/
theorem Iso.isCyclicWalk_walkMap (i : Iso G H) {W : WList V E} (hW : G.IsCyclicWalk W) :
    H.IsCyclicWalk (i.walkMap ⟨W, hW.isTour.isTrail.isWalk⟩).1 where
  toIsTour := i.isTour_walkMap hW.isTour
  nodup := by
    have hne := hW.nonempty
    cases W with
    | nil x => simp at hne
    | cons x e W =>
      simpa only [Iso.walkMap, Iso.walkMapAux, WList.tail_cons] using
        (i.isPath_walkMap
          (⟨hW.isTour.isTrail.isWalk.tail, hW.nodup⟩ : G.IsPath W)).nodup

/-- The canonical equivalence between raw walk lists supported by isomorphic graphs. -/
@[irw_equiv]
def Iso.walkEquiv (i : Iso G H) :
    {W : WList V E // G.IsWalk W} ≃ {W' : WList V' E' // H.IsWalk W'} where
  toFun := walkMap i
  invFun := walkMap i.symm
  left_inv := walkMap_symm_apply i
  right_inv := walkMap_symm_apply i.symm

/-- Supported walk transport commutes with taking the first vertex. -/
@[irw_naturality]
theorem Iso.walkEquiv_first (i : Iso G H) (W : {W : WList V E // G.IsWalk W}) :
    i.vertexEquiv ⟨W.1.first, W.2.first_mem⟩ =
      ⟨(i.walkEquiv W).1.first,
        (i.walkEquiv W).2.first_mem⟩ := by
  exact Subtype.ext (i.walkMap_first W.2).symm

/-- Supported walk transport commutes with taking the last vertex. -/
@[irw_naturality]
theorem Iso.walkEquiv_last (i : Iso G H) (W : {W : WList V E // G.IsWalk W}) :
    i.vertexEquiv ⟨W.1.last, W.2.last_mem⟩ =
      ⟨(i.walkEquiv W).1.last,
        (i.walkEquiv W).2.last_mem⟩ := by
  exact Subtype.ext (i.walkMap_last W.2).symm

/-- The canonical equivalence between bundled paths of isomorphic graphs. -/
@[irw_equiv]
def Iso.pathEquiv (i : Iso G H) : G.Path ≃ H.Path where
  toFun P := ⟨(i.walkMap ⟨P.1, P.2.isWalk⟩).1, i.isPath_walkMap P.2⟩
  invFun Q := ⟨(i.symm.walkMap ⟨Q.1, Q.2.isWalk⟩).1, i.symm.isPath_walkMap Q.2⟩
  left_inv P := Subtype.ext (i.walkMap_symm_apply_val P.2.isWalk)
  right_inv Q := Subtype.ext (i.symm.walkMap_symm_apply_val Q.2.isWalk)

/-! ## Primitive bundled-path naturality -/

/-- Path transport commutes with taking the first vertex. -/
@[irw_naturality]
theorem Iso.pathEquiv_first (i : Iso G H) (P : G.Path) :
    i.vertexEquiv P.first = (i.pathEquiv P).first := by
  apply Subtype.ext
  exact (i.walkMap_first P.2.isWalk).symm

/-- Path transport commutes with taking the last vertex. -/
@[irw_naturality]
theorem Iso.pathEquiv_last (i : Iso G H) (P : G.Path) :
    i.vertexEquiv P.last = (i.pathEquiv P).last := by
  apply Subtype.ext
  exact (i.walkMap_last P.2.isWalk).symm

/-- Path transport commutes with reversal. -/
@[irw_naturality]
theorem Iso.pathEquiv_reverse (i : Iso G H) (P : G.Path) :
    i.pathEquiv P.reverse = (i.pathEquiv P).reverse := by
  apply Subtype.ext
  exact i.walkMap_reverse P.2.isWalk

/-- Path transport commutes with taking the intrinsic vertex set. -/
@[irw_naturality]
theorem Iso.pathEquiv_vertexSet (i : Iso G H) (P : G.Path) :
    i.vertexEquiv '' P.vertexSet = (i.pathEquiv P).vertexSet := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (i.walkMap_vertex_mem_iff P.2.isWalk x).mpr hx
  · intro hy
    let x := i.vertexEquiv.symm y
    refine ⟨x, ?_, by simp [x]⟩
    change y.1 ∈ (i.walkMap ⟨P.1, P.2.isWalk⟩).1 at hy
    exact (i.walkMap_vertex_mem_iff P.2.isWalk x).mp (by simpa [x] using hy)

/-- Path transport commutes with taking the intrinsic edge set. -/
@[irw_naturality]
theorem Iso.pathEquiv_edgeSet (i : Iso G H) (P : G.Path) :
    i.edgeEquiv '' P.edgeSet = (i.pathEquiv P).edgeSet := by
  ext f
  constructor
  · rintro ⟨e, he, rfl⟩
    exact (i.walkMap_edge_mem_iff P.2.isWalk e).mpr he
  · intro hf
    let e := i.edgeEquiv.symm f
    refine ⟨e, ?_, by simp [e]⟩
    change f.1 ∈ (i.walkMap ⟨P.1, P.2.isWalk⟩).1.edge at hf
    exact (i.walkMap_edge_mem_iff P.2.isWalk e).mp (by simpa [e] using hf)

/-- Primitive supported action on ambient raw walk lists. -/
@[irw_domain]
def Iso.walkDomain (i : Iso G H) : IRw.SupportedDomain (WList V E) (WList V' E') where
  sourceSupport := G.IsWalk
  targetSupport := H.IsWalk
  equiv := i.walkEquiv

@[irw_naturality]
theorem Iso.walkEquiv_isWalk (i : Iso G H) (W : {W : WList V E // G.IsWalk W}) :
    G.IsWalk W.1 ↔ H.IsWalk (i.walkEquiv W).1 :=
  ⟨fun _ ↦ (i.walkEquiv W).2, fun _ ↦ W.2⟩

@[irw_naturality]
theorem Iso.walkEquiv_isTrail (i : Iso G H) (W : {W : WList V E // G.IsWalk W}) :
    G.IsTrail W.1 ↔ H.IsTrail (i.walkEquiv W).1 := by
  constructor
  · exact i.isTrail_walkMap
  · intro hW
    change H.IsTrail (i.walkMap W).1 at hW
    have hback := i.symm.isTrail_walkMap hW
    rw [i.walkMap_symm_apply_val W.2] at hback
    exact hback

@[irw_naturality]
theorem Iso.walkEquiv_isPath (i : Iso G H) (W : {W : WList V E // G.IsWalk W}) :
    G.IsPath W.1 ↔ H.IsPath (i.walkEquiv W).1 := by
  constructor
  · exact i.isPath_walkMap
  · intro hW
    change H.IsPath (i.walkMap W).1 at hW
    have hback := i.symm.isPath_walkMap hW
    rw [i.walkMap_symm_apply_val W.2] at hback
    exact hback

@[irw_naturality]
theorem Iso.walkEquiv_isTour (i : Iso G H) (W : {W : WList V E // G.IsWalk W}) :
    G.IsTour W.1 ↔ H.IsTour (i.walkEquiv W).1 := by
  constructor
  · exact i.isTour_walkMap
  · intro hW
    change H.IsTour (i.walkMap W).1 at hW
    have hback := i.symm.isTour_walkMap hW
    rw [i.walkMap_symm_apply_val W.2] at hback
    exact hback

@[irw_naturality]
theorem Iso.walkEquiv_isCyclicWalk (i : Iso G H) (W : {W : WList V E // G.IsWalk W}) :
    G.IsCyclicWalk W.1 ↔ H.IsCyclicWalk (i.walkEquiv W).1 := by
  constructor
  · exact i.isCyclicWalk_walkMap
  · intro hW
    change H.IsCyclicWalk (i.walkMap W).1 at hW
    have hback := i.symm.isCyclicWalk_walkMap hW
    rw [i.walkMap_symm_apply_val W.2] at hback
    exact hback

/-! ## Support evidence

These rules are visible only to `irw`'s restricted certificate solver. -/

/-- A tour is, in particular, a walk; exposed directly to keep support search one-step. -/
theorem IsTour.irw_support_isWalk {W : WList V E} (hW : G.IsTour W) : G.IsWalk W :=
  hW.isTrail.isWalk

/-- A cyclic walk is, in particular, a walk; exposed directly to keep support search one-step. -/
theorem IsCyclicWalk.irw_support_isWalk {W : WList V E} (hW : G.IsCyclicWalk W) : G.IsWalk W :=
  hW.isTour.isTrail.isWalk

attribute [irw_support →]
  IsLink.edge_mem IsLink.left_mem IsLink.right_mem
  Inc.edge_mem Inc.vertex_mem
  Adj.left_mem Adj.right_mem
  IsWalk.first_mem IsWalk.last_mem
  IsTrail.isWalk IsPath.isWalk IsTour.irw_support_isWalk IsCyclicWalk.irw_support_isWalk


end Graph
