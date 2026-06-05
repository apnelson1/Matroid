import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.OrderOfElement
import Matroid.Graph.Minor.Defs
import Mathlib.Data.PFun

open Set PFun Part Equiv

variable {V E D : Type*} {G H : Graph V E} {e : E} {d d' : D}

namespace PFun

variable {α β γ : Type*} {f : α →. β} {φ : β → γ} {S T : Set β} {a b : α} {x y : β}

attribute [grind <=] mem_unique
attribute [simp, grind .] preimage_subset_dom
attribute [gcongr] preimage_mono

lemma mem_preimage_self (h : a ∈ f.Dom) : a ∈ f.preimage {(f a).get h} := by
  simp only [mem_preimage, mem_singleton_iff, exists_eq_left]
  exact get_mem h

lemma preimage_inter' {S T : Set β} : f.preimage (S ∩ T) = f.preimage S ∩ f.preimage T := by
  grind

@[simp]
lemma mem_image_iff {S : Set α} : x ∈ f.image S ↔ ∃ a ∈ S, x ∈ f a := by
  simp [image, graph']

lemma image_subset_ran {S : Set α} : f.image S ⊆ f.ran := by
  intro a
  simp only [mem_image_iff, ran, mem_setOf_eq, forall_exists_index, and_imp]
  grind

@[simp]
lemma dom_restrict {S : Set α} (hS : S ⊆ f.Dom) : (f.restrict hS).Dom = S := by
  ext a
  simp only [mem_dom, mem_restrict, exists_and_left, and_iff_left_iff_imp]
  exact fun haS ↦ dom_iff_mem.mp (hS haS)

@[simp]
lemma ran_restrict {S : Set α} (hS : S ⊆ f.Dom) : (f.restrict hS).ran = f.image S := by
  ext a
  simp [ran]

@[simp]
lemma preimage_restrict {S : Set α} (hS : S ⊆ f.Dom) :
    (f.restrict hS).preimage T = f.preimage T ∩ S := by
  ext a
  simp only [mem_preimage, mem_restrict]
  grind

@[simp]
lemma restrict_restrict {S T : Set α} (hS : S ⊆ f.Dom) (hT : T ⊆ (f.restrict hS).Dom) :
    (f.restrict hS).restrict hT = f.restrict (p := S ∩ T) (by grind) := by
  ext a x
  grind [mem_restrict]

def codRestrict (f : α →. β) (S : Set β) : α →. β :=
  f.restrict (preimage_subset_dom f S)

@[simp, grind =]
lemma mem_codRestrict : x ∈ (f.codRestrict S) a ↔ x ∈ f a ∧ x ∈ S := by
  simp only [codRestrict, mem_restrict, mem_preimage]
  grind

@[simp, grind =]
lemma ran_codRestrict : (f.codRestrict S).ran = f.ran ∩ S := by
  ext x
  simp only [ran, codRestrict, mem_restrict]
  grind

@[simp, grind =]
lemma dom_codRestrict : (f.codRestrict S).Dom = f.Dom ∩ f.preimage S := by
  ext a
  simp only [codRestrict, mem_dom, mem_restrict, mem_inter_iff]
  grind

@[simp] lemma preimage_codRestrict : (f.codRestrict S).preimage T = f.preimage (T ∩ S) := by grind

@[simp]
lemma codRestrict_codRestrict : (f.codRestrict S).codRestrict T = f.codRestrict (T ∩ S) := by
  simp only [codRestrict, restrict_restrict]
  congr
  grind [preimage_restrict]

@[simp]
lemma dom_map : (PFun.map φ f).Dom = f.Dom := by
  ext a
  simp only [mem_dom, PFun.map, Part.mem_map_iff]
  grind

@[simp]
lemma mem_map (a : α) (c : γ) : c ∈ (PFun.map φ f) a ↔ ∃ b ∈ f a, φ b = c := by
  simp [PFun.map]

@[simp]
lemma ran_map : (PFun.map φ f).ran = φ '' f.ran := by
  ext c
  simp only [ran, mem_map]
  grind

@[simp]
lemma preimage_map (S : Set γ) : (PFun.map φ f).preimage S = f.preimage (φ ⁻¹' S) := by
  ext a
  simp only [mem_preimage, mem_map]
  grind

end PFun

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
  have htwo := M.preimage_encard (M.mem_edgeSet_of_mem_fₑ hd)
  rw [encard_eq_two] at htwo
  rcases htwo with ⟨x, y, hxy, hpair⟩
  replace hd : d ∈ M.fₑ.preimage {e} := by simpa
  replace hd' : d' ∈ M.fₑ.preimage {e} := by simpa
  grind

@[simp, grind =]
lemma fₑ_otherDart (d : D) : M.fₑ (M.otherDart d) = M.fₑ d := by
  by_cases h : d ∈ M.fₑ.Dom
  · have : (M.fₑ d).get h ∈ M.fₑ (M.otherDart d) := by simpa using M.mem_preimage_other h
    exact (eq_of_mem h this).symm
  simp [h]

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
    simpa [PFun.mem_preimage, e] using mem_of_mem_diff this
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

@[simps]
def copy (M : DartStructure G D) (h : G = H) : DartStructure H D where
  fₑ := M.fₑ
  ran_fₑ := by simp [h]
  preimage_encard e he := M.preimage_encard (h ▸ he)
  fᵥ := M.fᵥ
  dom_fᵥ := M.dom_fᵥ
  ran_fᵥ := h ▸ M.ran_fᵥ
  inc_iff_exists_dart := h ▸ M.inc_iff_exists_dart

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
  use F.edgeSet_mono, F.edge_disj

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

def LocallyFinite (M : DartStructure G D) := ∀ v, (M.fᵥ.preimage {v}).Finite

lemma IsSubgraph.LocallyFinite (h : H ≤ G) (hM : M.LocallyFinite) :
    (M.of_le h).LocallyFinite := by
  intro v
  simp only [fᵥ_of_le, preimage_restrict]
  exact (hM v).inter_of_left (M.fₑ.preimage E(H))

end DartStructure

end Graph
