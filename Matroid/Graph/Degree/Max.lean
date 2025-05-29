import Matroid.Graph.Connected
import Matroid.Graph.Tree
import Matroid.Graph.Degree.Constructions

variable {α β : Type*} {x y z u v w : α} {e f : β} {G H : Graph α β} {F F₁ F₂ : Set β} {X Y : Set α}
{d : ℕ}

open Set WList

namespace Graph



/-! ### Maximum degree -/

/-- `G.MaxDegreeLE d` means that `G` has maximum degree at most `d`.  -/
def MaxDegreeLE (G : Graph α β) (d : ℕ) : Prop := ∀ v, G.eDegree v ≤ d

lemma MaxDegreeLE.degree_le (h : G.MaxDegreeLE d) (v : α) : G.degree v ≤ d :=
  ENat.toNat_le_of_le_coe (h v)

lemma MaxDegreeLE.mono (h : G.MaxDegreeLE d) (hle : H ≤ G) : H.MaxDegreeLE d :=
  fun v ↦ (eDegree_mono hle _).trans <| h v

lemma MaxDegreeLE.locallyFinite (h : G.MaxDegreeLE d) : G.LocallyFinite where
  finite x := finite_of_encard_le_coe <| (G.encard_setOf_inc_le_eDegree x).trans (h x)

lemma MaxDegreeLE.encard_edgeSet_le (h : G.MaxDegreeLE d) : 2 * E(G).encard ≤ d * V(G).encard := by
  rw [← handshake_eDegree_subtype, ← ENat.tsum_one, ENat.mul_tsum]
  exact ENat.tsum_le_tsum fun x ↦ (h x).trans_eq <| by simp

lemma MaxDegreeLE.ncard_edgeSet_le [G.Finite] (h : G.MaxDegreeLE d) :
    2 * E(G).ncard ≤ d * V(G).ncard := by
  simp_rw [← Nat.cast_le (α := ℕ∞), Nat.cast_mul, Nat.cast_ofNat]
  rw [G.edgeSet_finite.cast_ncard_eq, G.vertexSet_finite.cast_ncard_eq]
  exact h.encard_edgeSet_le

/-- A nontrivial connected graph with max degree at most two is loopless. -/
lemma Connected.loopless_of_maxDegreeLE_two (hG : G.Connected) (hmax : G.MaxDegreeLE 2)
    (hnt : V(G).Nontrivial) : G.Loopless where
  not_isLoopAt e x h := by
    have := hmax.locallyFinite
    obtain ⟨f, y, hf, hne⟩ := hG.exists_isLink_of_mem hnt h.vertex_mem
    have hle := hmax.degree_le x
    have h1 : 1 ≤ {e | G.IsLoopAt e x}.ncard :=
      Nat.one_le_iff_ne_zero.2 <| ncard_ne_zero_of_mem h G.finite_setOf_isLoopAt
    have h2 : 1 ≤ {e | G.IsNonloopAt e x}.ncard :=
      Nat.one_le_iff_ne_zero.2 <| ncard_ne_zero_of_mem ⟨y, hne, hf⟩ G.finite_setOf_isNonloopAt
    rw [degree_eq_ncard_add_ncard] at hle
    linarith

-- lemma Connected.simple_of_maxDegreeLE_two (hG : G.Connected) (hmax : G.MaxDegreeLE 2)
--     (hcard : 3 ≤ V(G).encard) : G.Simple := by
--   sorry

/-! ### Paths -/

def IsPathGraph (G : Graph α β) : Prop := ∃ P, G.IsPath P ∧ G = P.toGraph

def IsCycleGraph (G : Graph α β) : Prop := ∃ C, G.IsCycle C ∧ G = C.toGraph

/-- If `v` and `w` are leaves of a connected graph `G` with maximum degree `2`,
then `G` is a path from `v` to `w`. -/
lemma Connected.exists_isPath_of_leaves [G.Finite] (hG : G.Connected) (hmax : G.MaxDegreeLE 2)
    (hv : G.IsLeaf v) (hw : G.IsLeaf w) (hne : v ≠ w) :
    ∃ P, G.IsPath P ∧ P.first = v ∧ P.last = w ∧ G = P.toGraph := by
  have hlf := hmax.locallyFinite
  obtain ⟨P, hP, rfl, rfl⟩ := (hG.vertexConnected hv.mem hw.mem).exists_isPath
  refine ⟨P, hP, rfl, rfl, Eq.symm ?_⟩
  refine eq_of_le_of_forall_degree_ge hG hP.isWalk.toGraph_le (by simp) fun x hx ↦ ?_
  have hPne : P.Nonempty := by rwa [first_ne_last_iff hP.nodup] at hne
  obtain rfl | hne0 := eq_or_ne x P.first
  · rw [(hP.first_isLeaf_toGraph hPne).degree, hv.degree]
  obtain rfl | hne1 := eq_or_ne x P.last
  · rw [(hP.last_isLeaf_toGraph hPne).degree, hw.degree]
  rw [hP.degree_toGraph_eq_two (by simpa using hx) hne0 hne1]
  apply hmax.degree_le

/-- Every connected graph with maximum degree two and a vertex of degree less than 2 is a path. -/
lemma Connected.isPathGraph_of_degree [G.Finite] (hG : G.Connected) (hmax : G.MaxDegreeLE 2)
    (hv : ∃ v ∈ V(G), G.degree v ≤ 1) : G.IsPathGraph := by
  simp_rw [Nat.le_one_iff_eq_zero_or_eq_one, degree_eq_one_iff] at hv
  obtain ⟨v, hvG, h0 | hv⟩ := hv
  · obtain hV | hnt := eq_singleton_or_nontrivial hvG
    · exact ⟨nil v, by simpa, Eq.symm <|
        hG.eq_of_le_of_forall_degree_ge (by simpa) (by simp) (by simpa)⟩
    simpa [h0] using (hG.minDegreePos hnt).one_le_degree hvG
  obtain ⟨w, hwv, hw⟩ : ∃ w ≠ v, G.IsLeaf w := by
    simp_rw [← degree_eq_one_iff]
    by_contra! hcon
    have h2 : ∀ w ∈ V(G), w ≠ v → G.degree w = 2 := by
      refine fun w hw hwv ↦ (hmax.degree_le w).antisymm <| not_lt.1 fun hlt ↦ hcon _ hwv ?_
      have := (hG.minDegreePos hv.vertexSet_nontrivial).one_le_degree hw
      omega
    have hhs := G.handshake_degree_subtype
    rw [← finsum_mem_add_diff (s := {v}) (by simpa using hv.mem) (by simp)] at hhs
    simp only [mem_singleton_iff, finsum_cond_eq_left, hv.degree] at hhs
    rw [finsum_mem_congr (s := V(G) \ {v}) rfl (g := 2) (by simpa)] at hhs
    simp_rw [Pi.ofNat_apply, finsum_mem_const, smul_eq_mul] at hhs
    have hmod := congr_arg (fun x ↦ x % 2) hhs
    simp at hmod
  obtain ⟨P, hP, rfl, rfl, rfl⟩ := hG.exists_isPath_of_leaves hmax hv hw hwv.symm
  exact ⟨P, hP, rfl⟩

/-- Every `2`-regular connected graph is a cycle. -/
lemma Connected.isCycleGraph_of_degree [G.Finite] (hG : G.Connected)
    (hdeg : ∀ v ∈ V(G), G.degree v = 2) : G.IsCycleGraph := by
  have hE : E(G).Nonempty := by
    obtain ⟨v, hv⟩ := hG.nonempty
    have h0 : ¬ G.degree v = 0 := by simp [hdeg v hv]
    obtain ⟨e, he : G.Inc e v⟩ := by simpa [degree_eq_zero_iff_inc] using h0
    exact ⟨e, he.edge_mem⟩
  by_cases hF : G.IsForest
  · obtain ⟨x, hx⟩ := hF.exists_isLeaf hE
    simpa [hx.degree] using hdeg x hx.mem
  obtain ⟨C, hC : G.IsCycle C⟩ := by simpa [IsForest] using hF
  refine ⟨C, hC, Eq.symm <| hG.eq_of_le_of_forall_degree_ge hC.isWalk.toGraph_le (by simp) ?_⟩
  simp +contextual only [toGraph_vertexSet, mem_vertexSet_iff, hC.degree_toGraph_eq_two]
  exact fun x hxC ↦ (hdeg x (hC.isWalk.vertex_mem_of_mem hxC)).le
