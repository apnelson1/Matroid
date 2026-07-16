import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.OrderOfElement
import Matroid.Graph.Minor.Defs
import Matroid.ForMathlib.Data.PFun
import Matroid.ForMathlib.Topology.ENat

open Set PFun Part Equiv

variable {V E D : Type*} {G H : Graph V E} {e : E} {d d' : D}

namespace Graph

structure DartStructure (G : Graph V E) (D : Type*) where
  fₑ : D →. E
  ran_fₑ : fₑ.ran = E(G)
  preimage_encard ⦃e : E⦄ : e ∈ E(G) → (fₑ.preimage {e}).encard = 2
  fᵥ : D →. V
  dom_fᵥ : fᵥ.Dom = fₑ.Dom
  ran_fᵥ : fᵥ.ran ⊆ V(G)
  inc_iff_exists_dart : ∀ e v, G.Inc e v ↔ ∃ d, e ∈ fₑ d ∧ v ∈ fᵥ d

initialize_simps_projections DartStructure (as_prefix fₑ, as_prefix ran_fₑ, as_prefix fᵥ,
  as_prefix dom_fᵥ, as_prefix ran_fᵥ)

namespace DartStructure

variable (M : DartStructure G D)

attribute [simp, grind =] ran_fₑ preimage_encard dom_fᵥ
attribute [simp, grind .] ran_fᵥ

private lemma mem_edgeSet_of_mem_fₑ (hd : e ∈ M.fₑ d) : e ∈ E(G) := by
  rw [← M.ran_fₑ]
  exact ⟨d, hd⟩

private lemma exists_singleton_preimage_diff (h : d ∈ M.fₑ.Dom) :
    ∃ x, M.fₑ.preimage {((M.fₑ d).get h)} \ {d} = {x} := by
  have hmem := mem_preimage_self h
  have heG : (M.fₑ d).get h ∈ E(G) := by
    rw [← M.ran_fₑ]
    exact ⟨d, get_mem h⟩
  have := (M.preimage_encard heG).symm ▸ encard_diff_singleton_of_mem hmem
  rw [show (2 : ℕ∞) - 1 = 1 by enat_to_nat] at this
  exact encard_eq_one.mp this

noncomputable def otherDart (d : D) : D := by
  classical
  exact if h : d ∈ M.fₑ.Dom then (M.exists_singleton_preimage_diff h).choose else d

private lemma otherDart_eq_choose (h : d ∈ M.fₑ.Dom) :
    M.otherDart d = (M.exists_singleton_preimage_diff h).choose := by
  simp [h, otherDart]

lemma preimage_diff_eq_other (h : d ∈ M.fₑ.Dom) :
    M.fₑ.preimage {((M.fₑ d).get h)} \ {d} = {M.otherDart d} := by
  simpa [M.otherDart_eq_choose h] using (M.exists_singleton_preimage_diff h).choose_spec

private lemma mem_preimage_other (h : d ∈ M.fₑ.Dom) :
    M.otherDart d ∈ M.fₑ.preimage {((M.fₑ d).get h)} :=
  mem_of_mem_diff ((M.preimage_diff_eq_other h).symm.subset (mem_singleton _))

@[simp]
lemma otherDart_of_notMem_dom (h : d ∉ M.fₑ.Dom) : M.otherDart d = d := by
  simp [h, otherDart]

@[grind →]
lemma otherDart_ne (h : d ∈ M.fₑ.Dom) : M.otherDart d ≠ d := by
  grind [(M.preimage_diff_eq_other h).symm.subset (mem_singleton _)]

@[grind →]
lemma preimage_singleton_pair (hd : e ∈ M.fₑ d) (hd' : e ∈ M.fₑ d') (hne : d ≠ d') :
    M.fₑ.preimage {e} = {d, d'} := by
  obtain ⟨x, y, hxy, hpair⟩ := encard_eq_two.mp <| M.preimage_encard (M.mem_edgeSet_of_mem_fₑ hd)
  replace hd : d ∈ M.fₑ.preimage {e} := by simpa
  replace hd' : d' ∈ M.fₑ.preimage {e} := by simpa
  grind

@[simp, grind =]
lemma fₑ_otherDart (d : D) : M.fₑ (M.otherDart d) = M.fₑ d := by
  obtain hndom | h := em' (d ∈ M.fₑ.Dom)
  · simp [hndom]
  have : (M.fₑ d).get h ∈ M.fₑ (M.otherDart d) := by simpa using M.mem_preimage_other h
  exact (eq_of_mem h this).symm

lemma otherDart_invol (d : D) : M.otherDart (M.otherDart d) = d := by
  obtain h | h := em' (d ∈ M.fₑ.Dom)
  · simp [h, otherDart]
  set e := (M.fₑ d).get h
  have hpair := M.preimage_singleton_pair (by simpa only [PFun.mem_preimage,
    mem_singleton_iff, exists_eq_left] using mem_preimage_self h)
    (by simpa only [fₑ_otherDart, PFun.mem_preimage, mem_singleton_iff, exists_eq_left] using
      M.mem_preimage_other h) (M.otherDart_ne h).symm
  have hdom' := M.fₑ.preimage_subset_dom _ (hpair ▸ mem_insert_of_mem _ (mem_singleton _))
  have he' : (M.fₑ (M.otherDart d)).get hdom' = e := by
    refine Part.get_eq_of_mem ?_ _
    have := (M.preimage_diff_eq_other h).symm.subset (Set.mem_singleton (M.otherDart d))
    simp [e]
  have hdom₀ := M.otherDart_eq_choose h ▸ hdom'
  have hspec := (M.exists_singleton_preimage_diff hdom₀).choose_spec
  rw [congr_arg M.otherDart (M.otherDart_eq_choose h), M.otherDart_eq_choose hdom₀]
  have hmem : (M.exists_singleton_preimage_diff hdom₀).choose ∈
      M.fₑ.preimage {e} \ {M.otherDart d} := by
    simpa [(M.otherDart_eq_choose h).symm, he'] using hspec.symm.subset (Set.mem_singleton _)
  exact mem_singleton_iff.mp <|
    (by grind [M.otherDart_ne] : M.fₑ.preimage {e} \ {M.otherDart d} ⊆ {d}) hmem

noncomputable def α : Equiv.Perm D where
  toFun := M.otherDart
  invFun := M.otherDart
  left_inv := M.otherDart_invol
  right_inv := M.otherDart_invol

@[simp] lemma α_apply (d : D) : M.α d = M.otherDart d := rfl

@[simp] lemma α_inv_apply (d : D) : M.α.invFun d = M.otherDart d := rfl

noncomputable def swap (e : E) : Equiv.Perm D where
  toFun d := by
    classical
    exact if e ∈ M.fₑ d then M.otherDart d else d
  invFun d := by
    classical
    exact if e ∈ M.fₑ d then M.otherDart d else d
  left_inv d := by grind [M.otherDart_invol]
  right_inv d := by grind [M.otherDart_invol]

lemma swap_eq_α (hd : e ∈ M.fₑ d) : M.swap e d = M.α d := by
  simp [hd, swap]

lemma α_apply_ne_eq_dom_fₑ : {d | M.α d ≠ d} = M.fₑ.Dom := by
  ext d
  simp only [Set.mem_setOf_eq, DartStructure.α_apply]
  exact ⟨fun h ↦ by_contra fun hd ↦ h (M.otherDart_of_notMem_dom hd), M.otherDart_ne⟩

lemma α_apply_ne_iff_mem_dom_fₑ : M.α d ≠ d ↔ d ∈ M.fₑ.Dom := by
  simp [← α_apply_ne_eq_dom_fₑ]

@[simps]
def copy (M : DartStructure G D) (h : G = H) : DartStructure H D where
  fₑ := M.fₑ
  ran_fₑ := by simp [h]
  preimage_encard e he := M.preimage_encard (h ▸ he)
  fᵥ := M.fᵥ
  dom_fᵥ := M.dom_fᵥ
  ran_fᵥ := h ▸ M.ran_fᵥ
  inc_iff_exists_dart := h ▸ M.inc_iff_exists_dart

def dartFiber (v : V) (e : E) : Set D := M.fₑ.preimage {e} ∩ M.fᵥ.preimage {v}

lemma fᵥ_preimage_eq_iUnion_dartFiber (v : V) :
    M.fᵥ.preimage {v} = ⋃ e ∈ E(G, v), M.dartFiber v e := by
  ext d
  refine ⟨fun hdv ↦ ?_, fun hd ↦ ?_⟩
  · have hdom := M.dom_fᵥ ▸ M.fᵥ.preimage_subset_dom {v} hdv
    exact mem_iUnion.2 ⟨(M.fₑ d).get hdom, mem_iUnion.2
      ⟨(M.inc_iff_exists_dart _ _).2 ⟨d, Part.get_mem hdom, by simpa [PFun.mem_preimage] using hdv⟩,
      ⟨by simp, hdv⟩⟩⟩
  simp only [mem_iUnion] at hd
  exact hd.choose_spec.2.2

lemma dartFiber_pairwiseDisjoint (v : V) : (E(G, v)).PairwiseDisjoint (M.dartFiber v) := by
  refine fun e he f hf hne ↦ disjoint_left.2 fun d hd hfd ↦ ?_
  have hed : e ∈ M.fₑ d := by simpa [dartFiber, PFun.mem_preimage] using hd.1
  have hfd' : f ∈ M.fₑ d := by simpa [dartFiber, PFun.mem_preimage] using hfd.1
  exact hne <| Part.mem_unique hed hfd'

lemma _root_.Graph.IsLoopAt.dartFiber_eq_preimage {v} (h : G.IsLoopAt e v) :
    M.dartFiber v e = M.fₑ.preimage {e} := by
  ext d
  refine ⟨fun hd ↦ hd.1, fun hd ↦ ?_⟩
  have hdom := M.fₑ.preimage_subset_dom {e} hd
  have hdomv : d ∈ M.fᵥ.Dom := by rwa [M.dom_fᵥ]
  have hx := h.eq_of_inc ((M.inc_iff_exists_dart _ _).2 ⟨d, by simpa [PFun.mem_preimage] using hd,
    Part.get_mem hdomv⟩)
  exact ⟨hd, by simp [hx]⟩

lemma dartFiber_encard_isLoopAt {v e} (h : G.IsLoopAt e v) :
    (M.dartFiber v e).encard = 2 := by
  rw [h.dartFiber_eq_preimage, M.preimage_encard h.edge_mem]

lemma _root_.Graph.IsNonloopAt.dartFiber_eq_singleton {v e} (h : G.IsNonloopAt e v) :
    ∃ d, M.dartFiber v e = {d} := by
  obtain ⟨d, hed, hvd⟩ := (M.inc_iff_exists_dart e v).1 h.inc
  use d
  let w := h.inc.other
  have hwne : w ≠ v := by simpa [w] using h.other_ne
  obtain ⟨d', hed', hwd'⟩ := (M.inc_iff_exists_dart e w).1 (h.inc.choose_spec.inc_right)
  have hd'ne : d ≠ d' := by
    rintro rfl
    exact hwne <| Part.mem_unique hwd' hvd
  have hpair' : M.fₑ.preimage {e} = {d, d'} := M.preimage_singleton_pair hed hed' hd'ne
  ext x
  refine ⟨fun hx ↦ (hpair' ▸ hx.1).resolve_right fun h ↦ ?_, ?_⟩
  · rintro rfl
    simp [dartFiber, hed, hvd]
  have := by simpa only [PFun.mem_preimage, mem_singleton_iff, exists_eq_left] using hx.2
  exact (hwne <| Part.mem_unique hwd' (h ▸ this)).elim

lemma dartFiber_encard_isNonloopAt {v e} (h : G.IsNonloopAt e v) :
    (M.dartFiber v e).encard = 1 := by
  obtain ⟨d, hfiber⟩ := h.dartFiber_eq_singleton M
  simp [hfiber]

lemma preimage_fᵥ_encard_eq_eDegree (M : DartStructure G D) (v : V) :
    (M.fᵥ.preimage {v}).encard = G.eDegree v := by
  rw [eDegree_eq_encard_add_encard, M.fᵥ_preimage_eq_iUnion_dartFiber v,
    ← ENat.tsum_encard_eq_encard_biUnion (M.dartFiber_pairwiseDisjoint v),
    incEdges_eq_isLoopAt_union_isNonloopAt, tsum_union_disjoint (f := (M.dartFiber v · |>.encard))
    G.disjoint_isLoopAt_isNonLoopAt, tsum_congr (fun e ↦ M.dartFiber_encard_isLoopAt e.prop),
    tsum_congr (fun e ↦ M.dartFiber_encard_isNonloopAt e.prop), ENat.tsum_const, ENat.tsum_const,
    one_mul, ENat.card_coe_set_eq, ENat.card_coe_set_eq]

lemma preimage_fᵥ_ncard_eq_degree (M : DartStructure G D) (v : V) :
    (M.fᵥ.preimage {v}).ncard = G.degree v := by
  unfold degree ncard
  rw [preimage_fᵥ_encard_eq_eDegree]

section Subgraph

variable {X : Set V} {F : Set E}

@[simps]
def restrict (M : DartStructure G D) (F : Set E) : DartStructure (G ↾ F) D where
  fₑ := M.fₑ.codRestrict F
  ran_fₑ := by simp [M.ran_fₑ]
  preimage_encard e he := by
    rw [preimage_codRestrict, inter_eq_left.mpr (by simp [he.2])]
    exact M.preimage_encard he.1
  fᵥ := M.fᵥ.restrict (M.dom_fᵥ ▸ preimage_subset_dom M.fₑ F)
  dom_fᵥ := by simp
  ran_fᵥ := by
    simp only [ran_restrict, vertexSet_restrict]
    exact M.fᵥ.image_subset_ran.trans M.ran_fᵥ
  inc_iff_exists_dart e v := by
    simp only [restrict_inc, PFun.mem_restrict]
    grind [M.inc_iff_exists_dart]

lemma mem_preimage_fₑ_iff (d : D) (hd : d ∈ M.fₑ.Dom) (S : Set E) :
    d ∈ M.fₑ.preimage S ↔ (M.fₑ d).get hd ∈ S := by
  grind [Part.get_mem]

lemma preimage_fₑ_edgeSet_diff (F : Set E) :
    M.fₑ.preimage (E(G) \ F) = M.fₑ.Dom \ M.fₑ.preimage F := by
  ext d
  grind [mem_dom, mem_edgeSet_of_mem_fₑ]

@[simps!]
def deleteEdges (M : DartStructure G D) (F : Set E) : DartStructure (G ＼ F) D :=
  M.restrict (E(G) \ F) |>.copy (G.restrict_edgeSet_diff_eq_deleteEdges F)

@[simp]
lemma dom_fₑ_deleteEdges (F : Set E) : (M.deleteEdges F).fₑ.Dom = M.fₑ.Dom \ M.fₑ.preimage F := by
  simp [preimage_fₑ_edgeSet_diff]

@[simp]
lemma preimage_fᵥ_deleteEdges (F : Set E) (X : Set V) :
    (M.deleteEdges F).fᵥ.preimage X = M.fᵥ.preimage X \ M.fₑ.preimage F := by
  rw [fᵥ_deleteEdges, preimage_restrict, preimage_fₑ_edgeSet_diff, ← inter_diff_assoc,
    ← M.dom_fᵥ, inter_eq_left.mpr (preimage_subset_dom ..)]

@[simps]
def induce (M : DartStructure G D) (X : Set V) : DartStructure G[X] D where
  fₑ := M.fₑ.codRestrict E(G[X])
  ran_fₑ := by simp [ran_codRestrict, M.ran_fₑ, edgeSet_induce_subset]
  preimage_encard e he := by
    rw [preimage_codRestrict, inter_eq_left.mpr (by simpa using he)]
    exact M.preimage_encard (G.edgeSet_induce_subset X he)
  fᵥ := M.fᵥ.restrict (by simp [dom_codRestrict, dom_fᵥ])
  dom_fᵥ := dom_restrict _
  ran_fᵥ v := by
    simp only [ran_restrict, dom_codRestrict, mem_image_iff, mem_inter_iff, mem_dom,
      PFun.mem_preimage, vertexSet_induce, forall_exists_index, and_imp]
    exact fun d e hed f hf hfd hvd ↦ M.inc_iff_exists_dart f v |>.mpr ⟨d, hfd, hvd⟩
      |>.of_compatible (compatible_induce G X) hf |>.vertex_mem
  inc_iff_exists_dart e v := by
    simp only [induce_inc, M.inc_iff_exists_dart, mem_codRestrict,
      PFun.mem_restrict, mem_dom]
    grind

@[simp]
lemma preimage_fᵥ_induce (X Y : Set V) :
    (M.induce X).fᵥ.preimage Y = M.fᵥ.preimage Y ∩ M.fₑ.preimage E(G[X]) := by
  rw [fᵥ_induce, preimage_restrict, dom_codRestrict, ← inter_assoc, ← M.dom_fᵥ,
    inter_eq_left.mpr (M.fᵥ.preimage_subset_dom Y)]

@[simps!]
def deleteVerts (M : DartStructure G D) (X : Set V) : DartStructure (G - X) D :=
  M.induce (V(G) \ X) |>.copy (G.deleteVerts_def X)

@[simp]
lemma dom_fₑ_deleteVerts (X : Set V) :
    (M.deleteVerts X).fₑ.Dom = M.fₑ.Dom \ M.fₑ.preimage E(G, X) := by
  have hE : E(G[V(G) \ X]) = E(G) \ E(G, X) := by
    rw [← deleteVerts_def, deleteVerts_edgeSet_diff]
  grind [fₑ_deleteVerts, preimage_fₑ_edgeSet_diff]

@[simp]
lemma preimage_fᵥ_deleteVerts (X Y : Set V) :
    (M.deleteVerts X).fᵥ.preimage Y = M.fᵥ.preimage Y \ M.fₑ.preimage E(G, X) := by
  have hE : E(G[V(G) \ X]) = E(G) \ E(G, X) := by
    rw [← deleteVerts_def, deleteVerts_edgeSet_diff]
  simp only [fᵥ_deleteVerts, preimage_restrict, hE, dom_codRestrict, preimage_fₑ_edgeSet_diff]
  rw [inter_eq_right.mpr diff_subset, ← inter_diff_assoc, ← M.dom_fᵥ,
    inter_eq_left.mpr (preimage_subset_dom ..)]

def of_le (h : H ≤ G) (M : DartStructure G D) : DartStructure H D :=
  (M.induce V(H)).restrict E(H) |>.copy (h.induce_restrict_eq)

@[simp]
lemma fₑ_of_le (hle : H ≤ G) : (M.of_le hle).fₑ = M.fₑ.codRestrict E(H) := by
  simp only [of_le, fₑ_copy, fₑ_restrict, fₑ_induce]
  rw [codRestrict_codRestrict, inter_eq_left.mpr (le_induce_self hle).edgeSet_mono]

@[simp]
lemma fᵥ_of_le (hle : H ≤ G) :
    (M.of_le hle).fᵥ = M.fᵥ.restrict (M.dom_fᵥ ▸ M.fₑ.preimage_subset_dom E(H)) := by
  simp only [of_le, fᵥ_copy, fᵥ_restrict, fᵥ_induce, fₑ_induce, PFun.restrict_restrict]
  congr
  rw [preimage_codRestrict, inter_eq_left.mpr (le_induce_self hle).edgeSet_mono,
    dom_codRestrict, inter_eq_right.mpr (preimage_subset_dom ..), inter_eq_right]
  exact M.fₑ.preimage_mono (le_induce_self hle).edgeSet_mono

end Subgraph

section Map

variable {V' : Type*} {φ : V → V'}

@[simps]
def map (φ : V → V') : DartStructure (φ ''ᴳ G) D where
  fₑ := M.fₑ
  ran_fₑ := M.ran_fₑ
  preimage_encard e he := M.preimage_encard he
  fᵥ := PFun.map φ M.fᵥ
  dom_fᵥ := M.dom_fᵥ
  ran_fᵥ v hv := by grind [PFun.ran_map, vertexSet_map, mem_image_iff, M.ran_fᵥ]
  inc_iff_exists_dart e v := by
    simp only [map_inc, M.inc_iff_exists_dart, PFun.mem_map]
    grind

end Map

section Contract

variable {V' : Type*} {φ : V → V'} {C : Set E}

@[simps!]
def contract (C : Set E) (φ : V → V') : DartStructure (G /[C, φ]) D :=
  (M.map φ).deleteEdges C

@[simp]
lemma dom_fₑ_contract (C : Set E) (φ : V → V') :
    (M.contract C φ).fₑ.Dom = M.fₑ.Dom \ M.fₑ.preimage C := by
  rw [contract, dom_fₑ_deleteEdges, fₑ_map]

@[simp]
lemma preimage_fᵥ_contract (C : Set E) (φ : V → V') (X : Set V') :
    (M.contract C φ).fᵥ.preimage X = M.fᵥ.preimage (φ ⁻¹' X) \ M.fₑ.preimage C := by
  rw [contract, preimage_fᵥ_deleteEdges, fₑ_map, fᵥ_map, preimage_map]

end Contract

section Minor

variable {H : Graph V E} (M : DartStructure H D) (F : minorMap G H)

noncomputable def of_minorMap (M : DartStructure H D) (F : minorMap G H) : DartStructure G D :=
  M.contract (⋃ x : V(G), E(F.map x)) F.repFun |>.of_le F.le_contract_repFun

@[simp]
lemma fₑ_of_minorMap : (M.of_minorMap F).fₑ = M.fₑ.codRestrict E(G) := by
  simp only [of_minorMap, fₑ_of_le, fₑ_contract, codRestrict_codRestrict]
  congr 1
  rw [inter_eq_left, subset_diff, disjoint_iUnion_right]
  exact ⟨F.edgeSet_mono, F.edge_disj⟩

@[simp]
lemma fᵥ_of_minorMap : (M.of_minorMap F).fᵥ =
    (M.fᵥ.map F.repFun).restrict (M.dom_fᵥ ▸ M.fₑ.preimage_subset_dom E(G)) := by
  simp only [of_minorMap, fᵥ_of_le, fᵥ_contract, fₑ_contract, PFun.restrict_restrict]
  congr 1
  rw [preimage_codRestrict, ← inter_diff_assoc, inter_eq_left.mpr F.edgeSet_mono,
    F.disjoint_edgeSet_iUnion.sdiff_eq_left, inter_eq_right]
  apply PFun.preimage_mono
  rw [subset_diff]
  use F.edgeSet_mono, F.disjoint_edgeSet_iUnion

noncomputable def of_isMinor (M : DartStructure H D) (h : G ≤m H) : DartStructure G D :=
  M.of_minorMap h.some

@[simp]
lemma fₑ_of_isMinor (M : DartStructure H D) (h : G ≤m H) :
    (M.of_isMinor h).fₑ = M.fₑ.codRestrict E(G) := by
  simp [of_isMinor, fₑ_of_minorMap]

@[simp]
lemma fᵥ_of_isMinor (M : DartStructure H D) (h : G ≤m H) : (M.of_isMinor h).fᵥ =
    (M.fᵥ.map h.some.repFun).restrict (M.dom_fᵥ ▸ M.fₑ.preimage_subset_dom E(G)) := by
  simp [of_isMinor, fᵥ_of_minorMap]

end Minor

lemma dom_fₑ_finite (M : DartStructure G D) [G.Finite] : M.fₑ.Dom.Finite := by
  convert G.edgeSet_finite.biUnion fun e heG ↦ finite_of_encard_eq_coe (M.preimage_encard heG)
  ext d
  simp only [mem_dom, mem_iUnion, PFun.mem_preimage, mem_singleton_iff, exists_eq_left, exists_prop]
  exact exists_congr fun e ↦ iff_and_self.mpr <| mem_edgeSet_of_mem_fₑ M

lemma locallyFinite_iff_fᵥ_preimage_finite (M : DartStructure G D) :
    G.LocallyFinite ↔ ∀ v, (M.fᵥ.preimage {v}).Finite:= by
  simp_rw [← forall_eDegree_ne_top_iff, ← M.preimage_fᵥ_encard_eq_eDegree, encard_ne_top_iff]

lemma fᵥ_preimage_finite [G.LocallyFinite] (M : DartStructure G D) (v : V) :
    (M.fᵥ.preimage {v}).Finite :=
  M.locallyFinite_iff_fᵥ_preimage_finite.mp inferInstance v

end DartStructure

/-- `Graph.Dart` is a type for darts or length 1 walks of `Graph`. Every edge of a graph is composed
  of two darts: for loops, there are `fwd` and `bwd` darts, and for non-loops, there are two `dir`
  darts. -/
inductive IncidenceType (α β : Type*) : Type _ where
  | dir : β → ∀ (u v : α), u ≠ v → IncidenceType α β
  | fwd : β → α → IncidenceType α β
  | bwd : β → α → IncidenceType α β

open IncidenceType

variable {d : IncidenceType V E}

/-- The edge of a `IncidenceType`. -/
@[expose]
def IncidenceType.edge (d : IncidenceType V E) : E :=
  match d with
  | .dir e _ _ _ => e
  | .fwd e _ => e
  | .bwd e _ => e

@[simp, grind =]
lemma IncidenceType.range_edge [Nonempty V] :
    range (IncidenceType.edge (V := V) (E := E)) = univ := by
  ext e
  simp only [mem_range, mem_univ, iff_true]
  exact ⟨fwd e (Classical.arbitrary V), rfl⟩

/-- The source of a `IncidenceType`. -/
@[expose]
def IncidenceType.source (d : IncidenceType V E) : V :=
  match d with
  | .dir _ u _ _ => u
  | .fwd _ v => v
  | .bwd _ v => v

@[simp, grind =]
lemma IncidenceType.range_source [Nonempty E] :
    range (IncidenceType.source (V := V) (E := E)) = univ := by
  ext v
  simp only [mem_range, mem_univ, iff_true]
  exact ⟨fwd (Classical.arbitrary E) v, rfl⟩

/-- The target of a `IncidenceType`. -/
@[expose]
def IncidenceType.target (d : IncidenceType V E) : V :=
  match d with
  | .dir _ _ v _ => v
  | .fwd _ v => v
  | .bwd _ v => v

@[simp, grind =]
lemma IncidenceType.range_target [Nonempty E] :
    range (IncidenceType.target (V := V) (E := E)) = univ := by
  ext v
  simp only [mem_range, mem_univ, iff_true]
  exact ⟨bwd (Classical.arbitrary E) v, rfl⟩

lemma IncidenceType.dir_of_ne (hne : d.source ≠ d.target) :
    d = dir d.edge d.source d.target hne := by
  cases d <;> grind [source, target, edge]

lemma IncidenceType.fwd_or_bwd_of_eq (heq : d.source = d.target) :
    d = fwd d.edge d.source ∨ d = bwd d.edge d.target := by
  cases d <;> grind [source, target, edge]

section inc12

variable [DecidableEq V] (e : E) (u v : V)

/-- The first incidence of a link. -/
def inc1 := if h : u = v then fwd e u else dir e u v h

/-- The second incidence of a link. -/
def inc2 := if h : u = v then bwd e u else dir e v u (Ne.symm h)

@[simp, grind =]
lemma inc1_edge : (inc1 e u v).edge = e := by
  by_cases huv : u = v <;> simp [inc1, huv, edge]

@[simp, grind =]
lemma inc2_edge : (inc2 e u v).edge = e := by
  by_cases huv : u = v <;> simp [inc2, huv, edge]

@[simp, grind =]
lemma inc1_source : (inc1 e u v).source = u := by
  by_cases huv : u = v <;> simp [inc1, huv, source]

@[simp, grind =]
lemma inc2_source : (inc2 e u v).source = v := by
  by_cases huv : u = v <;> simp [inc2, huv, source]

@[simp, grind =]
lemma inc1_target : (inc1 e u v).target = v := by
  by_cases huv : u = v <;> simp [inc1, huv, target]

@[simp, grind =]
lemma inc2_target : (inc2 e u v).target = u := by
  by_cases huv : u = v <;> simp [inc2, huv, target]

@[simp, grind .]
lemma inc1_ne_inc2 : inc1 e u v ≠ inc2 e u v := by
  by_cases huv : u = v <;> simp [inc1, inc2, huv]

omit [DecidableEq V]
lemma isLink_iff_exists_incidenceType : G.IsLink e u v ↔ ∃ i j : IncidenceType V E, i ≠ j ∧
    G.IsLink i.edge i.source i.target ∧ G.IsLink j.edge j.source j.target ∧
    (G.IsLink i.edge i.source i.target ∧ i.source = u ∧ i.edge = e) ∧
    (G.IsLink j.edge j.source j.target ∧ j.source = v ∧ j.edge = e) := by
  classical
  refine ⟨fun h => ?_, fun ⟨i, j, hij, hi, hj, hi', hj'⟩ => ?_⟩
  · refine ⟨inc1 e u v, inc2 e u v, inc1_ne_inc2 e u v, ?_, ?_,
      ⟨?_, inc1_source e u v, inc1_edge e u v⟩, ?_, inc2_source e u v, inc2_edge e u v⟩
    all_goals simp [h, h.symm]
  obtain ⟨-, rfl, rfl⟩ := hi'
  obtain ⟨-, rfl, he⟩ := hj'
  have := hi.eq_and_eq_or_eq_and_eq (he ▸ hj)
  obtain heq | hne := eq_or_ne i.source i.target
  · grind
  obtain ⟨hs, ht⟩ | ⟨hs, ht⟩ := this.symm
  · grind
  have hjne : j.source ≠ j.target := by grind
  grind [dir_of_ne hne, dir_of_ne hjne]

end inc12

section dartStructure

private def dart_fₑ (G : Graph V E) : IncidenceType V E →. E :=
  fun d ↦ Part.mk (G.IsLink d.edge d.source d.target) fun _ ↦ d.edge

private def dart_fᵥ (G : Graph V E) : IncidenceType V E →. V :=
  fun d ↦ Part.mk (G.IsLink d.edge d.source d.target) fun _ ↦ d.source

@[simp]
lemma mem_dart_fₑ_iff (d : IncidenceType V E) :
    e ∈ dart_fₑ G d ↔ G.IsLink d.edge d.source d.target ∧ d.edge = e := by
  simp [dart_fₑ, mem_mk_iff]

@[simp]
lemma mem_dart_fᵥ_iff {v : V} (d : IncidenceType V E) :
    v ∈ dart_fᵥ G d ↔ G.IsLink d.edge d.source d.target ∧ d.source = v := by
  simp [dart_fᵥ, mem_mk_iff]

@[simp]
lemma mem_dart_fₑ_preimage_iff {d : IncidenceType V E} :
    d ∈ (dart_fₑ G).preimage {e} ↔ G.IsLink d.edge d.source d.target ∧ d.edge = e := by
  simp [PFun.mem_preimage, mem_dart_fₑ_iff, mem_singleton_iff, eq_comm]

variable [DecidableEq V]

lemma dart_fₑ_preimage_eq_pair {u v : V} (h : G.IsLink e u v) :
    (dart_fₑ G).preimage {e} = {inc1 e u v, inc2 e u v} := by
  ext d
  rw [mem_dart_fₑ_preimage_iff, mem_insert_iff, mem_singleton_iff, iff_comm]
  refine ⟨?_,  fun ⟨hlink, hed⟩ ↦ ?_⟩
  · rintro (rfl | rfl)
    · exact ⟨by simpa [inc1_edge, inc1_source, inc1_target] using h, inc1_edge e u v⟩
    exact ⟨by simpa [inc2_edge, inc2_source, inc2_target] using h.symm, inc2_edge e u v⟩
  subst e
  obtain rfl | hne := eq_or_ne u v
  · cases d <;> grind [h.eq_and_eq_or_eq_and_eq hlink, inc1, inc2, edge, source, target]
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h.eq_and_eq_or_eq_and_eq hlink
  · exact Or.inl ((dir_of_ne hne).trans (by grind [inc1]))
  exact Or.inr ((dir_of_ne hne.symm).trans (by grind [inc2]))

def IncidenceType.dartStructure (G : Graph V E) :
    DartStructure G (IncidenceType V E) where
  fₑ := dart_fₑ G
  ran_fₑ := by
    ext e
    simp only [ran, mem_dart_fₑ_iff, mem_setOf_eq, edge_mem_iff_exists_isLink]
    exact ⟨fun ⟨d, h, he⟩ ↦ ⟨d.source, d.target, he ▸ h⟩, fun ⟨u, v, h⟩ ↦ ⟨inc1 e u v, by
      simpa [inc1_edge, inc1_source, inc1_target] using h, inc1_edge e u v⟩⟩
  preimage_encard e he := by
    obtain ⟨u, v, huv⟩ := exists_isLink_of_mem_edgeSet he
    rw [dart_fₑ_preimage_eq_pair huv, encard_pair (inc1_ne_inc2 e u v)]
  fᵥ := dart_fᵥ G
  dom_fᵥ := by
    ext d
    simp [mem_dom, mem_dart_fₑ_iff, mem_dart_fᵥ_iff]
  ran_fᵥ v hv := by
    obtain ⟨d, hlink, rfl⟩ := hv
    exact hlink.left_mem
  inc_iff_exists_dart e v := by
    simp only [Inc, mem_dart_fₑ_iff, mem_dart_fᵥ_iff]
    refine ⟨fun ⟨y, h⟩ ↦ ?_, fun ⟨d, ⟨hlink, he⟩, ⟨_, hv⟩⟩ ↦ ⟨d.target, hv ▸ he ▸ hlink⟩⟩
    exact ⟨inc1 e v y, ⟨by simpa [inc1_edge, inc1_source, inc1_target] using h, inc1_edge e v y⟩,
      ⟨by simpa [inc1_edge, inc1_source, inc1_target] using h, inc1_source e v y⟩⟩

end dartStructure

end Graph
