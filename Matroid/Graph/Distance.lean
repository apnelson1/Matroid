import Matroid.Graph.Connected

open Set Function Nat

variable {α β : Type*} {G H : Graph α β} {u v x x₁ x₂ y y₁ y₂ z : α} {e e' f g : β}
  {U V S T : Set α} {F F' R R': Set β} {C W P Q : WList α β}

open WList

namespace Graph

/-! ### Distance -/

/-- The number of edges of the shortest walk between two vertices `x,y` of `G`, as an `ℕ∞`.
Equal to `⊤` if `x` and `y` are not `VertexConnected` in `G`, in particular if `x = y ∉ V(G)`. -/
protected noncomputable def dist (G : Graph α β) (x y : α) : ℕ∞ :=
  ⨅ (W : {W // G.IsWalk W ∧ W.first = x ∧ W.last = y}), (W.1.length : ℕ∞)

lemma VertexConnected.dist_lt_top (h : G.VertexConnected x y) : G.dist x y < ⊤ := by
  obtain ⟨P, hP, rfl, rfl⟩ := h.exists_isWalk
  exact (iInf_le _ ⟨P, by simpa⟩).trans_lt (by simp)

lemma IsWalk.dist_le_length (hW : G.IsWalk W) : G.dist W.first W.last ≤ W.length := by
  let W' : {W' // G.IsWalk W' ∧ W'.first = W.first ∧ W'.last = W.last} := ⟨W, hW, rfl, rfl⟩
  apply iInf_le (i := W')

lemma IsWalk.isPath_of_length_eq_dist (hP : G.IsWalk P) (hlen : P.length = G.dist P.first P.last) :
    G.IsPath P := by
  classical
  rw [isPath_iff, and_iff_right hP, ← dedup_eq_self_iff]
  refine P.dedup_isSublist.eq_of_length_ge <| (Nat.cast_le (α := ℕ∞)).1 ?_
  rw [hlen, ← dedup_first, ← dedup_last]
  apply (hP.sublist P.dedup_isSublist).dist_le_length

/-- The distance from `x` to `y` is realized by a *path* from `x` to `y`. -/
lemma VertexConnected.exists_isPath_length_eq_dist (h : G.VertexConnected x y) :
    ∃ P, G.IsPath P ∧ P.first = x ∧ P.last = y ∧ P.length = G.dist x y := by
  have hd := h.dist_lt_top
  have hne : Nonempty {W // G.IsWalk W ∧ W.first = x ∧ W.last = y} := by
    obtain ⟨W, hW, rfl, rfl⟩ := h.exists_isWalk
    exact ⟨W, by simp [hW]⟩
  obtain ⟨⟨W,hWp, rfl, rfl⟩, hW : W.length = G.dist _ _⟩ :=
    ENat.exists_eq_iInf (ι := {W // G.IsWalk W ∧ W.first = x ∧ W.last = y})
    (fun W ↦ (W.1.length : ℕ∞))
  exact ⟨W, hWp.isPath_of_length_eq_dist hW, rfl, rfl, hW⟩

@[simp]
lemma dist_lt_top_iff : G.dist x y < ⊤ ↔ G.VertexConnected x y := by
  refine ⟨fun h ↦ ?_, VertexConnected.dist_lt_top⟩
  obtain ⟨⟨P,hP', rfl, rfl⟩, hP⟩ := iInf_lt_top.1 h
  exact hP'.vertexConnected_first_last

@[simp]
lemma dist_eq_top_iff : G.dist x y = ⊤ ↔ ¬ G.VertexConnected x y := by
  rw [← dist_lt_top_iff, lt_top_iff_ne_top, not_not]

lemma dist_comm (x y) : G.dist x y = G.dist y x := by
  suffices aux : ∀ x y, G.dist x y ≤ G.dist y x from (aux x y).antisymm (aux y x)
  intro x y
  simp only [Graph.dist, le_iInf_iff, Subtype.forall, and_imp]
  rintro W hW rfl rfl
  exact iInf_le_of_le ⟨W.reverse, by simpa⟩ <| by simp

lemma dist_self (G : Graph α β) (hx : x ∈ V(G)) : G.dist x x = 0 := by
  rw [Graph.dist, ENat.iInf_eq_zero]
  exact ⟨⟨WList.nil x, by simpa⟩, by simp⟩

lemma dist_self_eq_zero_iff : G.dist x x = 0 ↔ x ∈ V(G) :=
  ⟨fun h ↦ by simpa using (G.dist_lt_top_iff (x := x) (y := x)).1 (by simp [h]), G.dist_self⟩

@[simp]
lemma dist_eq_zero_iff : G.dist x y = 0 ↔ x = y ∧ x ∈ V(G) := by
  wlog h : G.VertexConnected x y
  · rw [← dist_eq_top_iff] at h
    simp only [h, ENat.top_ne_zero, false_iff, not_and]
    rintro rfl hx
    simp [hx] at h
  obtain ⟨P, hP, rfl, rfl, hl⟩ := h.exists_isPath_length_eq_dist
  simp [← hl, hP.isWalk.first_mem, first_eq_last_iff hP.nodup]

lemma Adj.dist_le_one (hxy : G.Adj x y) : G.dist x y ≤ 1 := by
  obtain ⟨e, he⟩ := hxy
  simpa using he.walk_isWalk.dist_le_length

lemma Adj.dist_eq_one_of_ne (hxy : G.Adj x y) (hne : x ≠ y) : G.dist x y = 1 :=
  hxy.dist_le_one.antisymm <| by simp [ENat.one_le_iff_ne_zero, hne]

lemma dist_triangle (G : Graph α β) (x y z : α) : G.dist x z ≤ G.dist x y + G.dist y z := by
  wlog hxy : G.VertexConnected x y
  · simp [dist_eq_top_iff.2 hxy]
  wlog hyz : G.VertexConnected y z
  · simp [dist_eq_top_iff.2 hyz]
  obtain ⟨P, hP, rfl, rfl, hPl⟩ := hxy.exists_isPath_length_eq_dist
  obtain ⟨Q, hQ, hQ1, rfl, hQl⟩ := hyz.exists_isPath_length_eq_dist
  have hle := (hP.isWalk.append hQ.isWalk hQ1.symm).dist_le_length
  rwa [append_first_of_eq hQ1.symm, append_last, append_length, Nat.cast_add,
    hPl, hQl] at hle

lemma Adj.dist_le_add_one (hxy : G.Adj x y) (z : α) : G.dist x z ≤ G.dist y z + 1 := by
  by_cases hyz : G.VertexConnected y z
  · obtain ⟨P, hP, rfl, rfl, hl⟩ := hyz.exists_isPath_length_eq_dist
    refine (G.dist_triangle x P.first P.last).trans ?_
    rw [add_comm, dist_comm]
    exact add_le_add_left hxy.dist_le_one _
  simp [dist_eq_top_iff.2 hyz]

/-- If `x` and `y` are distinct vertices that are connected in `G`,
then `y` has a neighbour `y'` whose distance to `x` is one less than that of `y`. -/
lemma VertexConnected.exists_adj_dist_eq_add_one (hconn : G.VertexConnected x y) (hne : x ≠ y) :
    ∃ y', G.Adj y' y ∧ G.dist x y = G.dist x y' + 1 := by
  obtain ⟨P, hP, rfl, rfl, hl⟩ := hconn.symm.exists_isPath_length_eq_dist
  cases P with
  | nil u => simp at hne
  | cons u e P =>
  · rw [cons_length, cast_add, cast_one, first_cons, last_cons, dist_comm, eq_comm] at hl
    simp only [first_cons, last_cons, hl]
    rw [cons_isPath_iff] at hP
    refine ⟨P.first, hP.2.1.adj.symm, ?_⟩
    rw [WithTop.add_right_inj (by simp), dist_comm, le_antisymm_iff,
      and_iff_left hP.1.isWalk.dist_le_length]
    have ht := G.dist_triangle u P.first P.last
    rw [dist_comm, hl] at ht
    replace ht := ht.trans (add_le_add_right hP.2.1.adj.dist_le_one _)
    rwa [add_comm, WithTop.add_le_add_iff_left (by simp)] at ht

lemma exists_adj_of_dist_eq_add_one {n : ℕ} (hxy : G.dist x y = n + 1) :
    ∃ y', G.Adj y' y ∧ G.dist x y' = n := by
  have hconn : G.VertexConnected x y := by
    simp [← dist_lt_top_iff, hxy, show (1 : ℕ∞) < ⊤ from compareOfLessAndEq_eq_lt.mp rfl]
  have hne : x ≠ y := by
    rintro rfl
    rw [dist_eq_zero_iff.2 (by simp [hconn.left_mem]), eq_comm] at hxy
    simp at hxy
  obtain ⟨y', hyy', hdist⟩ := hconn.exists_adj_dist_eq_add_one hne
  exact ⟨y', hyy', by rwa [← WithTop.add_right_inj (z := 1) (by simp), ← hdist]⟩

/-! ### `ℕ` - valued distance -/

protected noncomputable def ndist (G : Graph α β) (x y : α) : ℕ := (G.dist x y).toNat

lemma ndist_comm (G : Graph α β) (x y : α) : G.ndist x y = G.ndist y x := by
  rw [Graph.ndist, dist_comm, ← Graph.ndist]

lemma VertexConnected.cast_ndist (hG : G.VertexConnected x y) : G.ndist x y = G.dist x y := by
  obtain ⟨P, hP, rfl, rfl, hl⟩ := hG.exists_isPath_length_eq_dist
  simpa [Graph.ndist]

lemma Connected.cast_ndist (hG : G.Connected) (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
    G.ndist x y = G.dist x y :=
  (hG.vertexConnected hx hy).cast_ndist

lemma VertexConnected.exists_isPath_length_eq_ndist (hG : G.VertexConnected x y) :
    ∃ P, G.IsPath P ∧ P.first = x ∧ P.last = y ∧ P.length = G.ndist x y := by
  obtain ⟨P, hP, rfl, rfl, h⟩ := hG.exists_isPath_length_eq_dist
  exact ⟨P, hP, rfl, rfl, by simp [Graph.ndist, ← h]⟩

lemma IsWalk.ndist_le_length (hW : G.IsWalk W) : G.ndist W.first W.last ≤ W.length := by
  simpa [← hW.vertexConnected_first_last.cast_ndist, Nat.cast_le] using hW.dist_le_length

lemma ndist_triangle (hxy : G.VertexConnected x y) (z) :
    G.ndist x z ≤ G.ndist x y + G.ndist y z := by
  by_cases hxz : G.VertexConnected x z
  · have hyz : G.VertexConnected y z := hxy.symm.trans hxz
    rw [← Nat.cast_le (α := ℕ∞), Nat.cast_add, hxy.cast_ndist, hyz.cast_ndist,
      (hxy.trans hyz).cast_ndist]
    exact dist_triangle G x y z
  simp [Graph.ndist, dist_eq_top_iff.2 hxz]

/-! ### Shortest Paths -/

/-- `G.IsShortestPath P` means that `P` there is no walk of `G` between the ends of `P` with fewer
edges than `P` itself. -/
structure IsShortestPath (G : Graph α β) (P : WList α β) : Prop where
  isPath : G.IsPath P
  length_eq_dist : P.length = G.dist P.first P.last

lemma IsShortestPath.length_eq_ndist (hP : G.IsShortestPath P) :
    P.length = G.ndist P.first P.last := by
  rw [← Nat.cast_inj (R := ℕ∞), hP.length_eq_dist,
    hP.isPath.isWalk.vertexConnected_first_last.cast_ndist]

lemma IsWalk.isShortestPath_of_length_le (hP : G.IsWalk P)
    (hdist : P.length ≤ G.ndist P.first P.last) : G.IsShortestPath P := by
  have hlen : P.length = G.dist P.first P.last := by
    rw [← hP.vertexConnected_first_last.cast_ndist, Nat.cast_inj]
    exact hdist.antisymm <| hP.ndist_le_length
  exact ⟨hP.isPath_of_length_eq_dist hlen, hlen⟩

lemma isShortestPath_nil (hx : x ∈ V(G)) : G.IsShortestPath (nil x) :=
  ⟨by simpa, by simp [dist_self _ hx]⟩

lemma VertexConnected.exists_isShortestPath (hxy : G.VertexConnected x y) :
    ∃ P, G.IsShortestPath P ∧ P.first = x ∧ P.last = y := by
  obtain ⟨P, hP, rfl, rfl, hlen⟩ := hxy.exists_isPath_length_eq_ndist
  exact ⟨P, hP.isWalk.isShortestPath_of_length_le hlen.le, rfl, rfl⟩

lemma IsShortestPath.reverse (hP : G.IsShortestPath P) : G.IsShortestPath P.reverse :=
  hP.isPath.isWalk.reverse.isShortestPath_of_length_le <| by simp [hP.length_eq_ndist, ndist_comm]

@[simp]
lemma isShortestPath_reverse_iff : G.IsShortestPath P.reverse ↔ G.IsShortestPath P :=
  ⟨fun h ↦ by simpa using h.reverse, fun h ↦ h.reverse⟩

@[simp]
lemma isShortestPath_nil_iff : G.IsShortestPath (nil x) ↔ x ∈ V(G) :=
  ⟨fun h ↦ h.isPath.isWalk.first_mem, isShortestPath_nil⟩

-- Maybe induction with `hQ` is better here.
lemma IsShortestPath.prefix (hP : G.IsShortestPath P) (hQ : Q.IsPrefix P) : G.IsShortestPath Q := by
  obtain ⟨Q', hQ', rfl⟩ := hQ.exists_eq_append
  have hQpath := hP.isPath.prefix hQ
  refine hQpath.isWalk.isShortestPath_of_length_le ?_
  have hdist := hP.length_eq_ndist
  rw [append_length, append_last, append_first_of_eq hQ'] at hdist
  obtain ⟨Q₀, hQ₀, h1, h2⟩ := hQpath.isWalk.vertexConnected_first_last.exists_isShortestPath
  rw [← add_le_add_iff_right (a := Q'.length), hdist, ← h1, ← h2, ← hQ₀.length_eq_ndist,
    ← append_length]
  have hQ₀Q' := hQ₀.isPath.isWalk.append (hP.isPath.isWalk.suffix (isSuffix_append_left ..))
    (by rw [h2, hQ'])
  convert hQ₀Q'.ndist_le_length using 2
  · rw [append_first_of_eq (by rwa [h2])]
  simp

lemma IsShortestPath.suffix (hP : G.IsShortestPath P) (hQ : Q.IsSuffix P) : G.IsShortestPath Q := by
  simpa using hP.reverse.prefix hQ.reverse_isPrefix_reverse

lemma IsShortestPath.sublist (hP : G.IsShortestPath P) (hQ : Q.IsSublist P) :
    G.IsShortestPath Q := by
  obtain ⟨P', hP'⟩ := hQ.exists_isPrefix_isSuffix hP.isPath.nodup
  exact (hP.prefix hP'.1).suffix hP'.2




end Graph
