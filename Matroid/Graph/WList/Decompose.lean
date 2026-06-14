import Matroid.Graph.WList.TakeDrop

open Set Function List Nat WList

variable {α β : Type*} {u v x y z : α} {e e' f g : β} {S T U: Set α}
  {F F' : Set β} {w w₁ w₂ w₃ l l₁ l₂ l₃ : WList α β}

namespace WList

/- This is a subwalk of `w` from the vertex in `S` to the vertex in `T` with all intermediate
  vertices not in `S` or `T`, if such subwalk exists. Otherwise, it starts/ends at the boundary of
  the given walk. If there are multiple such subwalks, it returns the last one.
  In the case where `w` is a path with some vertex in `S` before some vertex in `T`,
  its result satisfies `w.IsPathFrom S T`. -/
def betweenSets (w : WList α β) (S T : Set α) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)] :
    WList α β := (w.suffixFromLast (· ∈ S)).prefixUntil (· ∈ T)

variable {S T : Set α} [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]

@[simp]
lemma betweenSets_isInfix (w : WList α β) (S T : Set α) [DecidablePred (· ∈ S)]
    [DecidablePred (· ∈ T)] : (w.betweenSets S T).IsInfix w :=
  (prefixUntil_isPrefix _ _).isInfix.trans (w.suffixFromLast_isSuffix (· ∈ S)).isInfix

@[grind =]
lemma betweenSets_first_mem_iff (w : WList α β) (S T : Set α) [DecidablePred (· ∈ S)]
    [DecidablePred (· ∈ T)] : (w.betweenSets S T).first ∈ S ↔ ∃ x ∈ w, x ∈ S := by
  rw [betweenSets, prefixUntil_first]
  exact suffixFromLast_prop_first_iff ..

lemma betweenSets_first_mem (hw : ∃ x ∈ w, x ∈ S) : (w.betweenSets S T).first ∈ S := by
  rw [betweenSets, prefixUntil_first]
  exact suffixFromLast_prop_first hw

lemma betweenSets_first_eq_of_mem  (hv : v ∈ w.betweenSets S T) (hvS : v ∈ S) :
    (w.betweenSets S T).first = v := by
  rw [betweenSets, prefixUntil_first]
  exact suffixFromLast_first_eq_of_prop ((prefixUntil_isPrefix _ _).mem hv) hvS

lemma betweenSets_first_eq_iff_mem (hw : ∃ x ∈ w, x ∈ S) :
    (w.betweenSets S T).first = v ↔ v ∈ V(w.betweenSets S T) ∧ v ∈ S :=
  ⟨fun h ↦ ⟨h ▸ first_mem, h ▸ betweenSets_first_mem hw⟩,
    fun ⟨hv, hvS⟩ ↦ betweenSets_first_eq_of_mem hv hvS⟩

lemma betweenSets_vertex_tail_not_prop (w : WList α β) (S T : Set α) [DecidablePred (· ∈ S)]
    [DecidablePred (· ∈ T)] : ∀ x ∈ (w.betweenSets S T).vertex.tail, x ∉ S := by
  intro x hx
  have := (w.suffixFromLast (· ∈ S)).prefixUntil_isPrefix (· ∈ T) |>.prefix.tail
  exact suffixFromLast_vertex_tail_not_prop (this.mem hx)

/- When there are multiple `S` to `T` segments in `w`, `w.betweenSets S T` will return the
  last such segment. This is an arbitrary choice and it means that `betweenSets_first_mem`
  only requires having some vertex from `S` in `w`, whereas for this lemma, it is more strict. -/
lemma betweenSets_last_mem (hw : ∃ u ∈ w.suffixFromLast (· ∈ S), u ∈ T) :
    (w.betweenSets S T).last ∈ T := by
  rw [betweenSets]
  exact prefixUntil_prop_last hw

lemma betweenSets_last_eq_of_mem (hv : v ∈ w.betweenSets S T) (hvT : v ∈ T) :
    (w.betweenSets S T).last = v :=
  prefixUntil_last_eq_of_prop hv hvT

lemma betweenSets_last_eq_iff_mem (hw : ∃ u ∈ w.suffixFromLast (· ∈ S), u ∈ T) :
    (w.betweenSets S T).last = v ↔ v ∈ V(w.betweenSets S T) ∧ v ∈ T :=
  ⟨fun h ↦ ⟨h ▸ last_mem, h ▸ betweenSets_last_mem hw⟩,
    fun ⟨hv, hvT⟩ ↦ betweenSets_last_eq_of_mem hv hvT⟩

lemma betweenSets_vertex_dropLast_not_prop (w : WList α β) (S T : Set α) [DecidablePred (· ∈ S)]
    [DecidablePred (· ∈ T)] : ∀ x ∈ (w.betweenSets S T).vertex.dropLast, x ∉ T :=
  fun _ ↦ prefixUntil_vertex_dropLast_not_prop

lemma betweenSets_isPrefix_iff (S T : Set α) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (hnd : w.vertex.Nodup) : (w.betweenSets S T).IsPrefix w ↔ ∀ x ∈ w.vertex.tail, x ∉ S := by
  rw [← suffixFromLast_eq_self_iff w (· ∈ S)]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · refine (w.suffixFromLast_isSuffix (· ∈ S)).eq_of_first_mem hnd ?_
    have hf : (w.suffixFromLast (· ∈ S)).first = w.first := by simpa [betweenSets] using h.first_eq
    exact hf ▸ first_mem
  rw [betweenSets, h]
  exact prefixUntil_isPrefix ..

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
      obtain hQ | rfl : Q ∈ (w.breakAt_aux P e (nil x) []).tail ∨ Q = cons x e' w' := by
        simpa using hQ
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

lemma exists_infix_of_prop {p q : α → Prop} (hfirst : p w.first) (hlast : q w.last) :
    ∃ w' : WList α β, w'.IsInfix w ∧ p w'.first ∧ q w'.last ∧ (∀ x ∈ w'.vertex.tail, ¬ p x) ∧
      (∀ x ∈ w'.vertex.dropLast, ¬ q x) := by
  classical
  exact ⟨w.betweenSets p q, betweenSets_isInfix w p q,
    betweenSets_first_mem ⟨w.first, by simp, hfirst⟩,
    betweenSets_last_mem ⟨w.last, (w.suffixFromLast_last p) ▸ last_mem, hlast⟩,
    betweenSets_vertex_tail_not_prop w p q,
    betweenSets_vertex_dropLast_not_prop w p q⟩

lemma exists_infix_of_exists_prop {p q : α → Prop} (hp : ∃ x ∈ w, p x) (hq : ∃ x ∈ w, q x) :
    ∃ w' : WList α β, w'.IsInfix w ∧ ((p w'.first ∧ q w'.last ∧ (∀ x ∈ w'.vertex.tail, ¬ p x) ∧
    (∀ x ∈ w'.vertex.dropLast, ¬ q x)) ∨ (q w'.first ∧ p w'.last ∧ (∀ x ∈ w'.vertex.tail, ¬ q x) ∧
    (∀ x ∈ w'.vertex.dropLast, ¬ p x))) := by
  classical
  obtain h | h := suffixFrom_vertex_filter_eq_vertex_filter w p q
  · have hp' : ∃ x ∈ w.suffixFrom p, q x := by
      obtain ⟨x, hxw, hqx⟩ := hq
      have hfilt : x ∈ w.vertex.filter (fun b => decide (q b)) := by simp [hxw, hqx]
      exact ⟨x, mem_vertex.mp (List.mem_filter.mp (h.symm ▸ hfilt)).1, hqx⟩
    let w' := w.suffixFrom p |>.prefixUntilLast q
    have hw'f : p w'.first := by simpa [w'] using suffixFrom_prop_first hp
    have hw'l : q w'.last := by simpa [w'] using prefixUntilLast_prop_last hp'
    obtain ⟨w'', hinfix, hpw''f, hqw''l, hpw'', hqw''⟩ := exists_infix_of_prop hw'f hw'l
    refine ⟨w'', ?_, Or.inl ⟨hpw''f, hqw''l, hpw'', hqw''⟩⟩
    exact hinfix.trans <| ((w.suffixFrom p).prefixUntilLast_isPrefix q).isInfix.trans
      (w.suffixFrom_isSuffix p).isInfix
  have hq' : ∃ x ∈ w.suffixFrom q, p x := by
    obtain ⟨x, hxw, hpx⟩ := hp
    have hfilt : x ∈ w.vertex.filter (fun b => decide (p b)) := by simp [hxw, hpx]
    exact ⟨x, mem_vertex.mp (List.mem_filter.mp (h.symm ▸ hfilt)).1, hpx⟩
  let w' := w.suffixFrom q |>.prefixUntilLast p
  have hw'f : q w'.first := by simpa [w'] using suffixFrom_prop_first hq
  have hw'l : p w'.last := by simpa [w'] using prefixUntilLast_prop_last hq'
  obtain ⟨w'', hinfix, hqw''f, hpw''l, hqw'', hpw''⟩ := exists_infix_of_prop hw'f hw'l
  refine ⟨w'', ?_, Or.inr ⟨hqw''f, hpw''l, hqw'', hpw''⟩⟩
  exact hinfix.trans <| ((w.suffixFrom q).prefixUntilLast_isPrefix p).isInfix.trans
    (w.suffixFrom_isSuffix q).isInfix

/-- If a proposition `P` holds at the first vertex of `w` but not the last,
then `w` has a directed edge `e` from `x` to `y` such that `x` satisfies `P` but `y` doesn't. -/
lemma exists_dInc_prop_not_prop {P : α → Prop} (hfirst : P w.first) (hlast : ¬ P w.last) :
    ∃ e x y, w.DInc e x y ∧ P x ∧ ¬ P y := by
  induction w with
  | nil => simp_all
  | cons u e w ih =>
    by_cases hP : P w.first
    · obtain ⟨f, x, y, h, hx, hy⟩ := ih hP (by simpa using hlast)
      exact ⟨f, x, y, h.cons .., hx, hy⟩
    exact ⟨e, u, w.first, DInc.cons_left .., hfirst, hP⟩

lemma exists_dInc_not_prop_prop {P : α → Prop} (hfirst : ¬ P w.first) (hlast : P w.last) :
    ∃ e x y, w.DInc e x y ∧ ¬ P x ∧ P y := by
  obtain ⟨e, x, y, h, hx, hy⟩ := exists_dInc_prop_not_prop (P := fun x ↦ ¬ P x) hfirst (by simpa)
  exact ⟨e, x, y, h, hx, by simpa using hy⟩

lemma exists_isLink_prop_not_prop {P : α → Prop} (hxw : x ∈ V(w)) (hT : P x) (hyw : y ∈ V(w))
    (hF : ¬ P y) : ∃ e x y, w.IsLink e x y ∧ P x ∧ ¬ P y := by
  obtain ⟨w₀, hsub, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := exists_sublist_of_mem_mem hxw hyw
  · obtain ⟨e, x, y, h, hx, hy⟩ := exists_dInc_prop_not_prop hT hF
    exact ⟨e, x, y, (h.of_isSublist hsub).isLink, hx, hy⟩
  · rw [← w₀.reverse_reverse] at hF hT
    rw [reverse_first] at hF
    rw [reverse_last] at hT
    obtain ⟨e, x, y, h, hx, hy⟩ := exists_dInc_prop_not_prop hT hF
    refine ⟨e, x, y, ?_, hx, hy⟩
    rw [dInc_reverse_iff] at h
    exact (h.of_isSublist hsub).isLink.symm

end WList
