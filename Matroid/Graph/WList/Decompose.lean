import Matroid.Graph.WList.TakeDrop

open Set Function List Nat WList

variable {α β : Type*} {u v x y z : α} {e e' f g : β} {S T U: Set α}
  {F F' : Set β} {w w₁ w₂ w₃ l l₁ l₂ l₃ : WList α β}

namespace WList

/- This is a subwalk of `w` from the last vertex in `S`, `s`, to the first vertex in `T` after
  `s`, if any such vertex exists. Otherwise, it returns `w`.
  In the case where `w` is a path with some vertex in `S` before some vertex in `T`,
  its result satisfies `w.IsPathFrom S T`. -/
def extractPathFrom (w : WList α β) (S T : Set α) [DecidablePred (· ∈ S)]
    [DecidablePred (· ∈ T)] : WList α β :=
  (w.suffixFromLast (· ∈ S)).prefixUntil (· ∈ T)

@[simp]
lemma extractPathFrom_isSublist (w : WList α β) (S T : Set α) [DecidablePred (· ∈ S)]
    [DecidablePred (· ∈ T)] : (w.extractPathFrom S T).IsSublist w :=
  (prefixUntil_isPrefix _ _).isSublist.trans (w.suffixFromLast_isSuffix (· ∈ S)).isSublist

lemma extractPathFrom_first_mem [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (hw : ∃ x ∈ w, x ∈ S) : (w.extractPathFrom S T).first ∈ S := by
  rw [extractPathFrom, prefixUntil_first]
  exact suffixFromLast_prop_first hw

lemma extractPathFrom_first_eq_of_mem [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (hv : v ∈ w.extractPathFrom S T) (hvS : v ∈ S) : (w.extractPathFrom S T).first = v := by
  rw [extractPathFrom, prefixUntil_first]
  exact suffixFromLast_first_eq_of_prop ((prefixUntil_isPrefix _ _).mem hv) hvS

lemma extractPathFrom_first_eq_iff_mem [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (hw : ∃ x ∈ w, x ∈ S) :
    (w.extractPathFrom S T).first = v ↔ v ∈ V(w.extractPathFrom S T) ∧ v ∈ S :=
  ⟨fun h ↦ ⟨h ▸ first_mem, h ▸ extractPathFrom_first_mem hw⟩,
    fun ⟨hv, hvS⟩ ↦ extractPathFrom_first_eq_of_mem hv hvS⟩

/- When there are multiple `S` to `T` segments in `w`, `w.extractPathFrom S T` will return the
  last such segment. This is an arbitrary choice and it means that `extractPathFrom_first_mem`
  only requires having some vertex from `S` in `w`, whereas for this lemma, it is more strict. -/
lemma extractPathFrom_last_mem [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (hw : ∃ u ∈ w.suffixFromLast (· ∈ S), u ∈ T) : (w.extractPathFrom S T).last ∈ T := by
  rw [extractPathFrom]
  exact prefixUntil_prop_last hw

lemma extractPathFrom_last_eq_of_mem [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (hv : v ∈ w.extractPathFrom S T) (hvT : v ∈ T) : (w.extractPathFrom S T).last = v :=
  prefixUntil_last_eq_of_prop hv hvT

lemma extractPathFrom_last_eq_iff_mem [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (hw : ∃ u ∈ w.suffixFromLast (· ∈ S), u ∈ T) :
    (w.extractPathFrom S T).last = v ↔ v ∈ V(w.extractPathFrom S T) ∧ v ∈ T :=
  ⟨fun h ↦ ⟨h ▸ last_mem, h ▸ extractPathFrom_last_mem hw⟩,
    fun ⟨hv, hvT⟩ ↦ extractPathFrom_last_eq_of_mem hv hvT⟩

def breakAt_aux (w : WList α β) (P : α → Prop) [DecidablePred P] (e' : β) (w' : WList α β)
    (L : List (WList α β)) : List (WList α β) :=
  match w with
  | nil x => if P x then nil x :: (cons x e' w') :: L else (cons x e' w') :: L
  | cons x e w => if P x
    then breakAt_aux w P e (nil x) ((cons x e' w') :: L)
    else breakAt_aux w P e (cons x e' w') L

@[simp]
lemma breakAt_aux_length (w : WList α β) (P : α → Prop) [DecidablePred P] (e' : β) (w' : WList α β)
    (L : List (WList α β)) :
    (breakAt_aux w P e' w' L).length = w.vertex.countP P + L.length + 1 := by
  match w with
  | nil x => by_cases hPx : P x <;> unfold breakAt_aux <;> simp [hPx, add_comm]
  | cons x e w =>
    by_cases hPx : P x <;> unfold breakAt_aux <;> simp only [hPx, ↓reduceIte, cons_vertex,
      decide_false, Bool.false_eq_true, not_false_eq_true, decide_true, countP_cons_of_pos,
      countP_cons_of_neg] <;> rw [breakAt_aux_length]
    simp only [length_cons, Nat.add_right_cancel_iff]
    omega

lemma breakAt_aux_append (w : WList α β) (P : α → Prop) [DecidablePred P] (e' : β) (w' : WList α β)
    (L : List (WList α β)) :
    (breakAt_aux w P e' w' L) = breakAt_aux w P e' w' [] ++ L := by
  match w with
  | nil x => by_cases hPx : P x <;> unfold breakAt_aux <;> simp [hPx]
  | cons x e w =>
    by_cases hPx : P x <;> unfold breakAt_aux
    · simp only [hPx, ↓reduceIte]
      rw [breakAt_aux_append, breakAt_aux_append w P (L := [cons x e' w'])]
      simp
    simp only [hPx, ↓reduceIte]
    rw [breakAt_aux_append]

lemma breakAt_aux_eq_concat (w : WList α β) (P : α → Prop) [DecidablePred P] (e' : β)
    (w' w'' : WList α β) :
    (breakAt_aux w P e' w' [w'']) = (breakAt_aux w P e' w' []).concat w'' := by
  rw [breakAt_aux_append, concat_eq_append]

@[simp]
lemma breakAt_aux_foldl (w : WList α β) (P : α → Prop) [DecidablePred P] (e' : β) (w' : WList α β):
    (breakAt_aux w P e' w' []).foldl (· ++ ·) (nil x) = w.reverse.concat e' w'.first ++ w' := by
  match w with
  | nil x => by_cases hPx : P x <;> unfold breakAt_aux <;> simp [hPx]
  | cons x e w =>
    by_cases hPx : P x <;> unfold breakAt_aux <;> simp only [hPx, ↓reduceIte, reverse_cons] <;>
    rw [breakAt_aux_append, List.foldl_append, breakAt_aux_foldl] <;> simp

lemma breakAt_aux_ne_nil' (w : WList α β) (P : α → Prop) [DecidablePred P] (e' : β)
    (w' : WList α β) : (breakAt_aux w P e' w' []) ≠ [] := by
  match w with
  | nil x => by_cases hPx : P x <;> unfold breakAt_aux <;> simp [hPx]
  | cons x e w =>
    by_cases hPx : P x <;> unfold breakAt_aux <;> simp only [hPx, ↓reduceIte]
    · rw [breakAt_aux_append]
      simp
    exact breakAt_aux_ne_nil' w P e (cons x e' w')

@[simp]
lemma breakAt_aux_ne_nil (w : WList α β) (P : α → Prop) [DecidablePred P] (e' : β) (w' : WList α β)
    (L : List (WList α β)) : (breakAt_aux w P e' w' L) ≠ [] := by
  rw [breakAt_aux_append]
  simp [breakAt_aux_ne_nil']

lemma breakAt_aux_getLast (w : WList α β) (P : α → Prop) [DecidablePred P] (e' : β)
    (w' : WList α β) : (breakAt_aux w P e' w' []).getLast (by simp) =
    (w.prefixUntil P).reverse ++ cons w.first e' w' := by
  match w with
  | nil u => by_cases hPu : P u <;> unfold breakAt_aux <;> simp [hPu]
  | cons u e w =>
    by_cases hPu : P u <;> unfold breakAt_aux <;> simp only [hPu, ↓reduceIte, prefixUntil_cons,
      reverse_nil, first_cons, nil_append]
    · suffices (w.breakAt_aux P e (nil u) [] ++ [cons u e' w']).getLast (by simp) = cons u e' w' by
        convert this using 2
        rw [breakAt_aux_append]
      simp
    rw [breakAt_aux_getLast]
    simp

lemma breakAt_aux_head (w : WList α β) (P : α → Prop) [DecidablePred P] (e' : β) (w' : WList α β) :
    (breakAt_aux w P e' w' []).head (by simp) = if w.vertex.all (¬ P ·)
    then (w.suffixFromLast P).reverse ++ cons w.first e' w' else (w.suffixFromLast P).reverse := by
  match w with
  | nil x => by_cases hPx : P x <;> unfold breakAt_aux suffixFromLast <;> simp [hPx]
  | cons x e w =>
    unfold breakAt_aux suffixFromLast
    have h : (w.breakAt_aux P e (nil x) [cons x e' w']).head (by simp) =
      if (w.vertex.all fun x ↦ decide ¬P x)
      then (w.suffixFromLast P).reverse ++ cons w.first e (nil x)
      else (w.suffixFromLast P).reverse := by
      simp only [← breakAt_aux_head, breakAt_aux_append w P e (nil x) [cons x e' w'],
        ne_eq, breakAt_aux_ne_nil, not_false_eq_true, head_append_of_ne_nil]
    by_cases hPx : P x <;> by_cases hPw : w.vertex.all fun x ↦ !decide (P x) <;> simp [hPx, hPw, h]
    · simp only [suffixFromLast, reverse_reverse, prefixUntil_concat, reverse_vertex, decide_not,
      all_reverse, hPw, ↓reduceIte]
      rw [WList.concat_eq_append, prefixUntil_eq_self_of_forall (by simpa using hPw)]
      simp
    · simp [suffixFromLast, prefixUntil_concat, hPw]
    · rw [breakAt_aux_head]
      simp only [decide_not, hPw, ↓reduceIte, suffixFromLast, reverse_reverse, prefixUntil_concat,
        reverse_vertex, all_reverse, WList.concat_append, reverse_last]
      rw [prefixUntil_eq_self_of_forall (by simpa using hPw)]
    rw [breakAt_aux_head]
    simp [hPw, suffixFromLast, prefixUntil_concat]

lemma breakAt_aux_isChain_eq (w : WList α β) (P : α → Prop) [DecidablePred P] {e' : β}
    {w' : WList α β} : (w.breakAt_aux P e' w' []).IsChain (·.last = ·.first) := by
  unfold breakAt_aux
  match w with
  | nil u => by_cases hPu : P u <;> simp [hPu]
  | cons u e w =>
    by_cases hPu : P u <;> simp only [hPu, ↓reduceIte]
    · rw [breakAt_aux_append, List.isChain_append]
      simp only [breakAt_aux_isChain_eq, Option.mem_def, head?_cons,
        Option.some.injEq, forall_eq', first_cons, true_and]
      rw [getLast?_eq_getLast_of_ne_nil (by simp)]
      simp [breakAt_aux_getLast]
    exact w.breakAt_aux_isChain_eq P

lemma nonempty_of_mem_breakAt_aux_tail (w : WList α β) (P : α → Prop) [DecidablePred P] {e' : β}
    {w' Q : WList α β} (hQ : Q ∈ (w.breakAt_aux P e' w' []).tail) : Q.Nonempty := by
  unfold breakAt_aux at hQ
  match w with
  | nil x => by_cases hPx : P x <;> simp_all
  | cons x e w =>
    by_cases hPx : P x <;> simp_all only [↓reduceIte]
    · rw [breakAt_aux_append] at hQ
      obtain hQ | rfl := by simpa using hQ
      · exact w.nonempty_of_mem_breakAt_aux_tail P hQ
      simp
    exact w.nonempty_of_mem_breakAt_aux_tail P hQ

lemma breakAt_aux_map_first_eq_vertex_filter (w : WList α β) (P : α → Prop) [DecidablePred P]
    {e' : β} {w' : WList α β} :
    (w.breakAt_aux P e' w' []).tail.map (·.first) = (w.vertex.filter P).reverse := by
  unfold breakAt_aux
  match w with
  | nil x => by_cases hPx : P x <;> simp [hPx]
  | cons x e w =>
    by_cases hPx : P x <;> simp [hPx, ↓reduceIte, -map_tail]
    · rw [breakAt_aux_append]
      simp only [List.map_append, List.map_cons, first_cons, List.map_nil, ne_eq,
        breakAt_aux_ne_nil, not_false_eq_true, tail_append_of_ne_nil]
      rw [w.breakAt_aux_map_first_eq_vertex_filter P]
    rw [breakAt_aux_map_first_eq_vertex_filter]

/-- The segmentation of `w` breaks `w` at every vertex satisfying `P` and returns
  the list of segments. With the possible exception of the first and the last segment,
  all segments have the endpoints satisfying `P`.
  If `P` never occurs, this is `[w]`.
  If `w.first` satisfies `P`, then the first segment is `nil w.first`.
  Similarly, if `w.last` satisfies `P`, then the last segment is `nil w.last`. -/
def breakAt (w : WList α β) (P : α → Prop) [DecidablePred P] : List (WList α β) :=
  match w.reverse with
  | nil x => if P x then [nil x, nil x] else [nil x]
  | cons x e w => if P x
    then breakAt_aux w P e (nil x) [nil x]
    else breakAt_aux w P e (nil x) []

variable {P : α → Prop} [DecidablePred P]

@[simp]
lemma breakAt_nil : (nil x (β := β)).breakAt P = if P x then [nil x, nil x] else [nil x] := rfl

lemma breakAt_reverse_ne_nil (w : WList α β) (P : α → Prop) [DecidablePred P] :
    w.reverse.breakAt P ≠ [] := by
  match w with
  | nil u => by_cases hPu : P u <;> simp [hPu]
  | cons u e w => by_cases hPu : P u <;> simp [breakAt, hPu]

@[simp]
lemma breakAt_ne_nil : w.breakAt P ≠ [] := by
  rw [← w.reverse_reverse]
  apply breakAt_reverse_ne_nil

lemma breakAt_reverse_length (w : WList α β) (P : α → Prop) [DecidablePred P] :
    (w.reverse.breakAt P).length = w.vertex.countP P + 1 := by
  match w with
  | nil x => by_cases hPx : P x <;> simp [hPx]
  | cons x e w => by_cases hPx : P x <;> simp [breakAt, hPx, breakAt_aux_length]

@[simp]
lemma breakAt_length (w : WList α β) (P : α → Prop) [DecidablePred P] :
    (w.breakAt P).length = w.vertex.countP P + 1 := by
  conv_lhs => rw [← w.reverse_reverse]
  rw [breakAt_reverse_length]
  simp

lemma breakAt_reverse_foldl_append_cancel (w : WList α β) (P : α → Prop) [DecidablePred P] :
    (w.reverse.breakAt P).foldl (· ++ ·) (nil x) = w.reverse := by
  unfold breakAt
  rw [reverse_reverse]
  match w with
  | nil u => by_cases hPu : P u <;> simp [hPu]
  | cons u e w =>
    by_cases hPu : P u <;> simp only [hPu, ↓reduceIte, breakAt_aux_foldl, nil_first, concat_last,
      append_nil, reverse_cons]
    rw [breakAt_aux_append, List.foldl_append, breakAt_aux_foldl]
    simp

@[simp]
lemma breakAt_foldl_append_cancel (w : WList α β) (P : α → Prop) [DecidablePred P] :
    (w.breakAt P).foldl (· ++ ·) (nil x) = w := by
  rw [← w.reverse_reverse, breakAt_reverse_foldl_append_cancel]

@[simp]
lemma breakAt_appendList [Inhabited α] (w : WList α β) (P : α → Prop) [DecidablePred P] :
    (w.breakAt P)⁺ = w := breakAt_foldl_append_cancel w P

lemma breakAt_reverse_getLast (w : WList α β) (P : α → Prop) [DecidablePred P] :
    (w.reverse.breakAt P).getLast (by simp) = (w.prefixUntil P).reverse := by
  unfold breakAt
  match w with
  | nil u => by_cases hPu : P u <;> simp [hPu, prefixUntil]
  | cons u e w =>
    by_cases hPu : P u <;> simp only [reverse_cons, concat_reverse, reverse_reverse, hPu,
      ↓reduceIte, prefixUntil]
    · suffices (w.breakAt_aux P e (nil u) [] ++ [nil u]).getLast (by simp) = nil u by
        convert this using 2
        rw [breakAt_aux_append]
      simp
    rw [breakAt_aux_getLast, WList.concat_eq_append]
    simp

lemma breakAt_getLast (w : WList α β) (P : α → Prop) [DecidablePred P] :
    (w.breakAt P).getLast (by simp) = w.suffixFromLast P := by
  rw [← w.reverse_reverse, breakAt_reverse_getLast, reverse_reverse]
  rfl

lemma breakAt_reverse_head (w : WList α β) (P : α → Prop) [DecidablePred P] :
    (w.reverse.breakAt P).head (by simp) = (w.suffixFromLast P).reverse := by
  unfold breakAt
  match w with
  | nil u => by_cases hPu : P u <;> simp [hPu, suffixFromLast]
  | cons u e w =>
    by_cases hPu : P u <;> simp only [reverse_cons, concat_reverse, reverse_reverse, hPu,
      ↓reduceIte, suffixFromLast]
    · suffices (w.breakAt_aux P e (nil u) [] ++ [nil u]).head (by simp) =
        (w.reverse.concat e u).prefixUntil P by
        convert this using 2
        rw [breakAt_aux_append]
      simp only [ne_eq, breakAt_aux_ne_nil, not_false_eq_true, head_append_of_ne_nil,
        breakAt_aux_head, decide_not, suffixFromLast, reverse_reverse]
      by_cases hPw : w.vertex.all fun x ↦ !decide (P x) <;> simp [hPw, prefixUntil_concat]
      simp [w.reverse.prefixUntil_eq_self_of_forall (by simpa [mem_reverse] using hPw),
        WList.concat_eq_append]
    simp only [breakAt_aux_head, decide_not, suffixFromLast, reverse_reverse]
    by_cases hPw : w.vertex.all fun x ↦ !decide (P x) <;> simp [hPw, prefixUntil_concat]
    simp [WList.concat_eq_append, w.reverse.prefixUntil_eq_self_of_forall (by simpa using hPw)]

@[simp]
lemma breakAt_head (w : WList α β) (P : α → Prop) [DecidablePred P] :
    (w.breakAt P).head (by simp) = w.prefixUntil P := by
  rw [← w.reverse_reverse, breakAt_reverse_head, suffixFromLast, reverse_reverse]

lemma breakAt_reverse_isChain_eq (w : WList α β) (P : α → Prop) [DecidablePred P] :
    (w.reverse.breakAt P).IsChain (·.last = ·.first) := by
  simp only [breakAt, reverse_reverse]
  match w with
  | nil x => by_cases hPx : P x <;> simp [hPx]
  | cons x e w =>
    by_cases hPx : P x <;> simp only [hPx, ↓reduceIte]
    · rw [breakAt_aux_append, List.isChain_append]
      simp only [breakAt_aux_isChain_eq, Option.mem_def, head?_cons,
        Option.some.injEq, forall_eq', nil_first, true_and]
      rw [getLast?_eq_getLast_of_ne_nil (by simp)]
      simp [breakAt_aux_getLast]
    exact breakAt_aux_isChain_eq w P

lemma breakAt_isChain_eq (w : WList α β) (P : α → Prop) [DecidablePred P] :
    (w.breakAt P).IsChain (·.last = ·.first) := by
  rw [← w.reverse_reverse]
  apply w.reverse.breakAt_reverse_isChain_eq

@[simp]
lemma decomposeTo_breakAt [Inhabited α] (w : WList α β) (P : α → Prop) [DecidablePred P] :
    w.DecomposeTo (w.breakAt P) where
  nonempty := breakAt_ne_nil
  append := (w.breakAt_appendList P).symm
  chain_eq := breakAt_isChain_eq w P

lemma nonempty_of_mem_breakAt_dropLast_tail' (w : WList α β) (P : α → Prop) [DecidablePred P]
    {Q : WList α β} (hQ : Q ∈ (w.reverse.breakAt P).dropLast.tail) : Q.Nonempty := by
  unfold breakAt at hQ
  match w with
  | nil x => by_cases hPx : P x <;> simp [hPx] at hQ
  | cons x e w =>
    by_cases hPx : P x <;> simp [hPx] at hQ
    · rw [breakAt_aux_append, ← concat_eq_append] at hQ
      simp only [concat_eq_append, ne_eq, cons_ne_self, not_false_eq_true,
        dropLast_append_of_ne_nil, dropLast_singleton, List.append_nil] at hQ
      exact nonempty_of_mem_breakAt_aux_tail w P hQ
    rw [tail_dropLast] at hQ
    exact nonempty_of_mem_breakAt_aux_tail w P <| mem_of_mem_dropLast hQ

lemma nonempty_of_mem_breakAt_dropLast_tail (w : WList α β) (P : α → Prop) [DecidablePred P]
    {Q : WList α β} (hQ : Q ∈ (w.breakAt P).dropLast.tail) : Q.Nonempty := by
  rw [← w.reverse_reverse] at hQ
  exact nonempty_of_mem_breakAt_dropLast_tail' w.reverse P hQ

lemma breakAt_reverse_tail_map_first_eq_vertex_filter_reverse (w : WList α β) (P : α → Prop)
    [DecidablePred P] : (w.reverse.breakAt P).tail.map (·.first) = w.reverse.vertex.filter P := by
  unfold breakAt
  match w with
  | nil x => by_cases hPx : P x <;> simp [hPx]
  | cons x e w =>
    by_cases hPx : P x <;> conv_lhs => simp only [reverse_cons, concat_reverse, reverse_reverse,
      hPx, ↓reduceIte]
    · conv_lhs => simp [breakAt_aux_eq_concat, -map_tail]
      simp [w.breakAt_aux_map_first_eq_vertex_filter P, hPx]
    simpa [w.breakAt_aux_map_first_eq_vertex_filter P]

lemma breakAt_tail_map_first_eq_vertex_filter (w : WList α β) (P : α → Prop) [DecidablePred P] :
    (w.breakAt P).tail.map first = w.vertex.filter P := by
  rw [← w.reverse_reverse, breakAt_reverse_tail_map_first_eq_vertex_filter_reverse, reverse_reverse]

lemma breakAt_tail_map_first_eq_inter (w : WList α β) (S : Set α) [DecidablePred (· ∈ S)] :
    {x | x ∈ (w.breakAt (· ∈ S)).tail.map first} = V(w) ∩ S := by
  ext x
  rw [breakAt_tail_map_first_eq_vertex_filter]
  simp

-- lemma nil_mem_breakAt_iff (w : WList α β) (P : α → Prop) [DecidablePred P] (x : α) :
--     nil x ∈ w.breakAt P ↔ (P w.first ∧ x = w.first) ∨ (P w.last ∧ x = w.last) := by
--   sorry

end WList
