import Matroid.Graph.Tree


variable {α β γ: Type*} {x y z u v w : α} {e f : β} {G : Graph α β} {H : Graph γ β} {X Y : Set α}

open Set

namespace Graph

lemma components_finite (G : Graph α β) [G.Finite] : G.Components.Finite := by
  rw [← encard_ne_top_iff, ← lt_top_iff_ne_top]
  exact (G.components_encard_le).trans_lt G.vertexSet_finite.encard_lt_top

lemma girth_ne_top (hG : ¬ G.IsForest) : G.cycleMatroid.girth ≠ ⊤ := by
  refine G.cycleMatroid.girth_eq_top_iff_ground_indep.not.mpr ?_
  rw [← Matroid.ground_indep_iff_eq_freeOn, cycleMatroid_indep, cycleMatroid_E, isAcyclicSet_iff]
  simpa


def matroidalDual (G : Graph α β) (H : Graph γ β) : Prop := G.cycleMatroid✶ = H.cycleMatroid

instance : Std.Symm (matroidalDual (α := α) (β := β)) where
  symm _ _ h := Matroid.eq_dual_iff_dual_eq.mp h.symm

@[symm] lemma matroidalDual_symm (h : G.matroidalDual H) : H.matroidalDual G :=
  Matroid.eq_dual_iff_dual_eq.mp h.symm

lemma matroidalDual_comm : G.matroidalDual H ↔ H.matroidalDual G :=
  ⟨matroidalDual_symm, matroidalDual_symm⟩

namespace matroidalDual

variable {h : G.matroidalDual H}

lemma edgeSet_eq (h : G.matroidalDual H) : E(G) = E(H) := congrArg (·.E) h

theorem euler_formula (h : G.matroidalDual H) :
    V(G).encard + V(H).encard = E(G).encard + c(G) + c(H) := by
  rw [← G.cycleMatroid_E, ← G.cycleMatroid.eRank_add_eRank_dual, h, add_add_add_comm', add_assoc,
    H.eRank_cycleMatroid_add_numberOfComponents, G.eRank_cycleMatroid_add_numberOfComponents]

theorem euler_formula_of_connected (h : G.matroidalDual H) (hG : G.Connected) (hH : H.Connected) :
    V(G).encard + V(H).encard = E(G).encard + 2 := by
  rw [h.euler_formula, hG.numberOfComponents, hH.numberOfComponents, add_assoc]
  rfl

-- lemma bound_vertex_encard_of_eDegree  {k : ℕ} (hd : G.MinDegreeGE k) :
--     k * V(G).encard ≤ 2 * E(G).encard := hd.le_encard_edgeSet

lemma isbridge_iff_isloop (h : G.matroidalDual H) : G.IsBridge e ↔ ∃ v, H.IsLoopAt e v := by
  rw [← cycleMatroid_coloop, ← matroidalDual_symm h, Matroid.dual_isColoop_iff_isLoop,
    cycleMatroid_isLoop]

lemma isForest_of_faceSet_subsingleton (h : G.matroidalDual H) (hVH : V(H).Subsingleton) :
    G.IsForest := by
  intro e he
  rw [h.isbridge_iff_isloop]
  obtain ⟨u, v, huv⟩ := H.exists_isLink_of_mem_edgeSet (h.edgeSet_eq ▸ he)
  obtain rfl := hVH huv.left_mem huv.right_mem
  use u, huv

lemma bound_face_encard_of_girth (h : G.matroidalDual H) (hG : ¬ G.IsForest) (hH : H.Preconnected) :
    G.cycleMatroid.girth * V(H).encard ≤ 2 * E(G).encard := by
  have hVH : V(H).Nontrivial :=
    Set.not_subsingleton_iff.mp <| mt h.isForest_of_faceSet_subsingleton hG
  replace hG := G.girth_ne_top hG
  suffices H.MinDegreeGE G.cycleMatroid.girth.toNat by
    rw [← ENat.coe_toNat_eq_self.mpr hG]
    exact h.edgeSet_eq ▸ this.le_encard_edgeSet
  refine EdgeConnGE.minDegreeGE hVH ?_
  rw [← hH.cycleMatroid_dual_girth, matroidalDual_symm h, ENat.coe_toNat hG]

lemma girth_edgeConn_bound_of_connected (h : G.matroidalDual H) {k g : ℕ} (hk : G.EdgeConnGE k)
    (hg : g ≤ G.cycleMatroid.girth) (hGF : ¬ G.IsForest) (hG : G.Connected) (hH : H.Connected)
    (hVG : V(G).Nontrivial) :
    8 + k * V(G).encard + g * V(H).encard ≤ 4 * (V(G).encard + V(H).encard) := by
  have h1 := euler_formula_of_connected h hG hH
  have h2 := hk.minDegreeGE hVG |>.le_encard_edgeSet
  have h3 := h.bound_face_encard_of_girth hGF hH.pre
  replace hG := G.girth_ne_top hGF
  enat_to_nat!
  nlinarith

lemma not_matroidalDual_K33 (G : Graph α _) : ¬ (CompleteBipartiteGraph 3 3).matroidalDual G := by
  rintro h
  have := h.girth_edgeConn_bound_of_connected (k := 3) (g := 4) (by simp) ?_ ?_
    (completeBipartiteGraph_connected (by simp) (by simp)) ?_
    (by use Sum.inl 0, by simp, Sum.inr 0, by simp, by simp)
  rw [mul_add] at this
  norm_num at this
  sorry

end matroidalDual

end Graph
