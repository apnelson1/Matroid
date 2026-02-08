import Matroid.Graph.Connected.Defs
import Matroid.ForMathlib.ENat

open Set Function Nat

variable {α β : Type*} {G H : Graph α β} {u v x x₁ x₂ y y₁ y₂ z : α} {e e' f g : β}
  {U V S T : Set α} {F F' R R': Set β} {C W P Q : WList α β}

open WList

namespace Graph

/-! ### Distance -/

/-- The number of edges of the shortest walk between two vertices `x,y` of `G`, as an `ℕ∞`.
Equal to `⊤` if `x` and `y` are not `ConnBetween` in `G`, in particular if `x = y ∉ V(G)`. -/
protected noncomputable def eDist (G : Graph α β) (x y : α) : ℕ∞ :=
  ⨅ (W : {W // G.IsWalk W ∧ W.first = x ∧ W.last = y}), (W.1.length : ℕ∞)

lemma ConnBetween.eDist_lt_top (h : G.ConnBetween x y) : G.eDist x y < ⊤ := by
  obtain ⟨P, hP, rfl, rfl⟩ := h
  exact (iInf_le _ ⟨P, by simpa⟩).trans_lt (by simp)

lemma IsWalk.eDist_le_length (hW : G.IsWalk W) : G.eDist W.first W.last ≤ W.length := by
  let W' : {W' // G.IsWalk W' ∧ W'.first = W.first ∧ W'.last = W.last} := ⟨W, hW, rfl, rfl⟩
  apply iInf_le (i := W')

lemma IsWalk.isPath_of_length_eq_eDist (hP : G.IsWalk P)
    (hlen : P.length = G.eDist P.first P.last) : G.IsPath P := by
  classical
  rw [isPath_iff, and_iff_right hP, ← dedup_eq_self_iff]
  refine P.dedup_isSublist.eq_of_length_ge <| (Nat.cast_le (α := ℕ∞)).1 ?_
  rw [hlen, ← dedup_first, ← dedup_last]
  apply (hP.sublist P.dedup_isSublist).eDist_le_length

/-- The eDistance from `x` to `y` is realized by a *path* from `x` to `y`. -/
lemma ConnBetween.exists_isPath_length_eq_eDist (h : G.ConnBetween x y) :
    ∃ P, G.IsPath P ∧ P.first = x ∧ P.last = y ∧ P.length = G.eDist x y := by
  have hd := h.eDist_lt_top
  have hne : Nonempty {W // G.IsWalk W ∧ W.first = x ∧ W.last = y} := by
    obtain ⟨W, hW, rfl, rfl⟩ := h
    exact ⟨W, by simp [hW]⟩
  obtain ⟨⟨W,hWp, rfl, rfl⟩, hW : W.length = G.eDist _ _⟩ :=
    ENat.exists_eq_iInf (ι := {W // G.IsWalk W ∧ W.first = x ∧ W.last = y})
    (fun W ↦ (W.1.length : ℕ∞))
  exact ⟨W, hWp.isPath_of_length_eq_eDist hW, rfl, rfl, hW⟩

@[simp]
lemma eDist_lt_top_iff : G.eDist x y < ⊤ ↔ G.ConnBetween x y := by
  refine ⟨fun h ↦ ?_, ConnBetween.eDist_lt_top⟩
  obtain ⟨⟨P,hP', rfl, rfl⟩, hP⟩ := iInf_lt_top.1 h
  exact hP'.connBetween_first_last

@[simp]
lemma eDist_eq_top_iff : G.eDist x y = ⊤ ↔ ¬ G.ConnBetween x y := by
  rw [← eDist_lt_top_iff, lt_top_iff_ne_top, not_not]

lemma eDist_comm (x y) : G.eDist x y = G.eDist y x := by
  suffices aux : ∀ x y, G.eDist x y ≤ G.eDist y x from (aux x y).antisymm (aux y x)
  intro x y
  simp only [Graph.eDist, le_iInf_iff, Subtype.forall, and_imp]
  rintro W hW rfl rfl
  exact iInf_le_of_le ⟨W.reverse, by simpa⟩ <| by simp

lemma eDist_self (G : Graph α β) (hx : x ∈ V(G)) : G.eDist x x = 0 := by
  rw [Graph.eDist, ENat.iInf_eq_zero]
  exact ⟨⟨WList.nil x, by simpa⟩, by simp⟩

lemma eDist_self_eq_zero_iff : G.eDist x x = 0 ↔ x ∈ V(G) :=
  ⟨fun h ↦ by simpa using (G.eDist_lt_top_iff (x := x) (y := x)).1 (by simp [h]), G.eDist_self⟩

@[simp]
lemma eDist_eq_zero_iff : G.eDist x y = 0 ↔ x = y ∧ x ∈ V(G) := by
  wlog h : G.ConnBetween x y
  · rw [← eDist_eq_top_iff] at h
    simp only [h, ENat.top_ne_zero, false_iff, not_and]
    rintro rfl hx
    simp [hx] at h
  obtain ⟨P, hP, rfl, rfl, hl⟩ := h.exists_isPath_length_eq_eDist
  simp [← hl, hP.isWalk.first_mem, first_eq_last_iff hP.nodup]

lemma Adj.eDist_le_one (hxy : G.Adj x y) : G.eDist x y ≤ 1 := by
  obtain ⟨e, he⟩ := hxy
  simpa using he.walk_isWalk.eDist_le_length

lemma Adj.eDist_eq_one_of_ne (hxy : G.Adj x y) (hne : x ≠ y) : G.eDist x y = 1 :=
  hxy.eDist_le_one.antisymm <| by simp [ENat.one_le_iff_ne_zero, hne]

lemma eDist_triangle (G : Graph α β) (x y z : α) : G.eDist x z ≤ G.eDist x y + G.eDist y z := by
  wlog hxy : G.ConnBetween x y
  · simp [eDist_eq_top_iff.2 hxy]
  wlog hyz : G.ConnBetween y z
  · simp [eDist_eq_top_iff.2 hyz]
  obtain ⟨P, hP, rfl, rfl, hPl⟩ := hxy.exists_isPath_length_eq_eDist
  obtain ⟨Q, hQ, hQ1, rfl, hQl⟩ := hyz.exists_isPath_length_eq_eDist
  have hle := (hP.isWalk.append hQ.isWalk hQ1.symm).eDist_le_length
  rwa [append_first_of_eq hQ1.symm, append_last, append_length, Nat.cast_add,
    hPl, hQl] at hle

lemma Adj.eDist_le_add_one (hxy : G.Adj x y) (z : α) : G.eDist x z ≤ G.eDist y z + 1 := by
  by_cases hyz : G.ConnBetween y z
  · obtain ⟨P, hP, rfl, rfl, hl⟩ := hyz.exists_isPath_length_eq_eDist
    refine (G.eDist_triangle x P.first P.last).trans ?_
    rw [add_comm, eDist_comm]
    exact add_le_add_right hxy.eDist_le_one _
  simp [eDist_eq_top_iff.2 hyz]

/-- If `x` and `y` are eDistinct vertices that are connected in `G`,
then `y` has a neighbour `y'` whose eDistance to `x` is one less than that of `y`. -/
lemma ConnBetween.exists_adj_eDist_eq_add_one (hconn : G.ConnBetween x y) (hne : x ≠ y) :
    ∃ y', G.Adj y' y ∧ G.eDist x y = G.eDist x y' + 1 := by
  obtain ⟨P, hP, rfl, rfl, hl⟩ := hconn.symm.exists_isPath_length_eq_eDist
  cases P with
  | nil u => simp at hne
  | cons u e P =>
  · rw [cons_length, cast_add, cast_one, first_cons, last_cons, eDist_comm, eq_comm] at hl
    simp only [first_cons, last_cons, hl]
    rw [cons_isPath_iff] at hP
    refine ⟨P.first, hP.1.adj.symm, ?_⟩
    rw [WithTop.add_right_inj (by simp), eDist_comm, le_antisymm_iff,
      and_iff_left hP.2.1.isWalk.eDist_le_length]
    have ht := G.eDist_triangle u P.first P.last
    rw [eDist_comm, hl] at ht
    replace ht := ht.trans (add_le_add_left hP.1.adj.eDist_le_one _)
    rwa [add_comm, WithTop.add_le_add_iff_left (by simp)] at ht

lemma exists_adj_of_eDist_eq_add_one {n : ℕ} (hxy : G.eDist x y = n + 1) :
    ∃ y', G.Adj y' y ∧ G.eDist x y' = n := by
  have hconn : G.ConnBetween x y := by
    simp [← eDist_lt_top_iff, hxy, show (1 : ℕ∞) < ⊤ from compareOfLessAndEq_eq_lt.mp rfl]
  have hne : x ≠ y := by
    rintro rfl
    rw [eDist_eq_zero_iff.2 (by simp [hconn.left_mem]), eq_comm] at hxy
    simp at hxy
  obtain ⟨y', hyy', heDist⟩ := hconn.exists_adj_eDist_eq_add_one hne
  exact ⟨y', hyy', by rwa [← WithTop.add_right_inj (z := 1) (by simp), ← heDist]⟩

/-! ### `ℕ` - valued eDistance -/

protected noncomputable def dist (G : Graph α β) (x y : α) : ℕ := (G.eDist x y).toNat

-- notation "d(" G ", " x ", " y ")" => Graph.dist G x y

lemma dist_comm (G : Graph α β) (x y : α) : G.dist x y = G.dist y x := by
  rw [Graph.dist, eDist_comm, ← Graph.dist]

lemma ConnBetween.cast_dist (hG : G.ConnBetween x y) : G.dist x y = G.eDist x y := by
  obtain ⟨P, hP, rfl, rfl, hl⟩ := hG.exists_isPath_length_eq_eDist
  simpa [Graph.dist]

lemma Connected.cast_dist (hG : G.Connected) (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
    G.dist x y = G.eDist x y :=
  (hG.connBetween hx hy).cast_dist

lemma ConnBetween.exists_isPath_length_eq_dist (hG : G.ConnBetween x y) :
    ∃ P, G.IsPath P ∧ P.first = x ∧ P.last = y ∧ P.length = G.dist x y := by
  obtain ⟨P, hP, rfl, rfl, h⟩ := hG.exists_isPath_length_eq_eDist
  exact ⟨P, hP, rfl, rfl, by simp [Graph.dist, ← h]⟩

lemma IsWalk.dist_le_length (hW : G.IsWalk W) : G.dist W.first W.last ≤ W.length := by
  simpa [← hW.connBetween_first_last.cast_dist, Nat.cast_le] using hW.eDist_le_length

lemma dist_triangle (hxy : G.ConnBetween x y) (z) :
    G.dist x z ≤ G.dist x y + G.dist y z := by
  by_cases hxz : G.ConnBetween x z
  · have hyz : G.ConnBetween y z := hxy.symm.trans hxz
    rw [← Nat.cast_le (α := ℕ∞), Nat.cast_add, hxy.cast_dist, hyz.cast_dist,
      (hxy.trans hyz).cast_dist]
    exact eDist_triangle G x y z
  simp [Graph.dist, eDist_eq_top_iff.2 hxz]

/-! ### Shortest Paths -/

/-- `G.IsShortestPath P` means that `P` there is no walk of `G` between the ends of `P` with fewer
edges than `P` itself. -/
structure IsShortestPath (G : Graph α β) (P : WList α β) : Prop where
  isPath : G.IsPath P
  length_eq_eDist : P.length = G.eDist P.first P.last

lemma IsShortestPath.length_eq_dist (hP : G.IsShortestPath P) :
    P.length = G.dist P.first P.last := by
  rw [← Nat.cast_inj (R := ℕ∞), hP.length_eq_eDist,
    hP.isPath.isWalk.connBetween_first_last.cast_dist]

lemma IsWalk.isShortestPath_of_length_le (hP : G.IsWalk P)
    (heDist : P.length ≤ G.dist P.first P.last) : G.IsShortestPath P := by
  have hlen : P.length = G.eDist P.first P.last := by
    rw [← hP.connBetween_first_last.cast_dist, Nat.cast_inj]
    exact heDist.antisymm <| hP.dist_le_length
  exact ⟨hP.isPath_of_length_eq_eDist hlen, hlen⟩

lemma isShortestPath_nil (hx : x ∈ V(G)) : G.IsShortestPath (nil x) :=
  ⟨by simpa, by simp [eDist_self _ hx]⟩

lemma ConnBetween.exists_isShortestPath (hxy : G.ConnBetween x y) :
    ∃ P, G.IsShortestPath P ∧ P.first = x ∧ P.last = y := by
  obtain ⟨P, hP, rfl, rfl, hlen⟩ := hxy.exists_isPath_length_eq_dist
  exact ⟨P, hP.isWalk.isShortestPath_of_length_le hlen.le, rfl, rfl⟩

lemma IsShortestPath.reverse (hP : G.IsShortestPath P) : G.IsShortestPath P.reverse :=
  hP.isPath.isWalk.reverse.isShortestPath_of_length_le <| by simp [hP.length_eq_dist, dist_comm]

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
  have heDist := hP.length_eq_dist
  rw [append_length, append_last, append_first_of_eq hQ'] at heDist
  obtain ⟨Q₀, hQ₀, h1, h2⟩ := hQpath.isWalk.connBetween_first_last.exists_isShortestPath
  rw [← add_le_add_iff_right (a := Q'.length), heDist, ← h1, ← h2, ← hQ₀.length_eq_dist,
    ← append_length]
  have hQ₀Q' := hQ₀.isPath.isWalk.append (hP.isPath.isWalk.suffix (isSuffix_append_left ..))
    (by rw [h2, hQ'])
  convert hQ₀Q'.dist_le_length using 2
  · rw [append_first_of_eq (by rwa [h2])]
  simp

lemma IsShortestPath.suffix (hP : G.IsShortestPath P) (hQ : Q.IsSuffix P) : G.IsShortestPath Q := by
  simpa using hP.reverse.prefix hQ.reverse_isPrefix_reverse

lemma IsShortestPath.sublist (hP : G.IsShortestPath P) (hQ : Q.IsSublist P) :
    G.IsShortestPath Q := by
  obtain ⟨P', hP'⟩ := hQ.exists_isPrefix_isSuffix hP.isPath.nodup
  exact (hP.prefix hP'.1).suffix hP'.2




end Graph
