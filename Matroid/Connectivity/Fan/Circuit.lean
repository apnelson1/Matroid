import Matroid.Connectivity.Fan.Basic
import Matroid.Connectivity.Separation.Vertical


open Set List



set_option linter.style.longLine false

variable {α : Type*} {M : Matroid α} {X Y C K T : Set α} {e f g x y : α} {b c d : Bool}
    {J : Bool → List α} {L : List α} {n i j : ℕ} {F J : List α} {b c : Bool} {L : List ℕ}

def List.valsBetween (L : List α) (p q : ℕ) (b : Bool) : Set α :=
    {x | ∃ (i : ℕ) (hi : i < L.length), p ≤ i ∧ i ≤ q ∧ i.bodd = b ∧ L[i] = x}

lemma List.valsBetween_subset_iff (L : List α) p q b : L.valsBetween p q b ⊆ X ↔
    ∀ i (hi : i < L.length), p ≤ i → i ≤ q → i.bodd = b → L[i] ∈ X := by
  grind [List.valsBetween]

lemma List.valsBetween_subset (L : List α) p q b : L.valsBetween p q b ⊆ {e | e ∈ L} := by
  grind [List.valsBetween]

lemma List.valsBetween_self_eq_empty {L : List α} {p : ℕ} (hp : p.bodd = !b) :
    L.valsBetween p p b = ∅ := by
  grind [List.valsBetween]

lemma valsBetween_add_two (L : List α) {p q : ℕ} (hpq : p ≤ q) (hq : q.bodd = !b)
    (hqn : q + 1 < L.length) :
    L.valsBetween p (q + 2) b = insert L[q + 1] (L.valsBetween p q b) := by
  refine subset_antisymm ?_ <| insert_subset ⟨q + 1, hqn, by lia, by lia, by simpa, rfl⟩ ?_
  · rintro _ ⟨i, hi, hpi, hiq, rfl, rfl⟩
    by_cases hi : i < q
    · exact .inr ⟨i, by grind⟩
    grind [show i ≠ (q + 2) by rintro rfl; simp at hq]
  grind [List.valsBetween]

lemma valsBetween_insert_drop_two {L : List α} {p q : ℕ} (hpq : p ≤ q + 1)
    (hplt : p + 1 < L.length) (hp : p.bodd = !b) :
    insert L[p + 1] ((L.drop 2).valsBetween p q b) = L.valsBetween p (q + 2) b := by
  simp only [valsBetween, getElem_drop, length_drop, exists_and_left, Set.ext_iff,
    Set.mem_insert_iff, mem_setOf_eq, iff_def, forall_exists_index, and_imp]
  refine fun i ↦ ⟨?_, ?_⟩
  · rintro (rfl | ⟨i, hpi, hiq, rfl, hilt, rfl⟩)
    · exact ⟨p + 1, by lia, by lia, by simpa, by lia, rfl⟩
    exact ⟨2 + i, by lia, by lia, by simp, by lia, rfl⟩
  rintro i hpi hiq rfl hlt rfl
  by_contra! hcon
  obtain rfl | rfl | i := i; grind; grind
  exact hcon.2 i (by lia) (by lia) (by simp) (by lia) (by grind)

def List.fanCircuit (L : List α) (p q : ℕ) : Set α :=
    L.get '' {i : Fin L.length | i = p ∨ i = q ∨ p < i ∧ i < q ∧ (i : ℕ).bodd != p.bodd}
      -- {x | ∃ (i : ℕ) (hi : i < L.lenght) }

namespace Matroid

/-- The joints are always independent, unless the first and last element are parallel joints. -/
lemma IsFan.joints_indep (hF : M.IsFan F b c)
    (h_pair : b = false → c = false → ¬ M.Parallel (F.head hF.ne_nil) (F.getLast hF.ne_nil)) :
    M.Indep {e | ∃ (i : ℕ) (hi : i < F.length), i.bodd = b ∧ F[i] = e} := by
  rw [indep_iff_forall_subset_not_isCircuit']
  simp only [exists_and_left, Set.subset_def, mem_setOf_eq, forall_exists_index, and_imp]
  refine ⟨fun C hFC hC ↦ ?_, by grind [hF.get_mem_ground]⟩
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le' hF.two_le_length
  have hodd : ∀ (i : ℕ) (hi : i < F.length), F[i] ∈ C → i.bodd = b := by grind
  have hcon : ∀ (i : ℕ) (hi : i < F.length), F[i] ∈ C → i = 0 ∨ i = n + 1 := by
    rintro (rfl | j) hj hiC; simp
    wlog hnj : j < n; grind
    obtain ⟨j', hj'b, hj', hj''⟩ := hFC _ hiC
    rw [hF.getElem_inj_iff] at hj''
    simp only [hj'', Nat.bodd_succ, Bool.not_eq_eq_eq_not] at hj'b
    rw [(hF.isTriangle_getElem j (by lia)).mem_iff_mem_of_isCircuit_bDual (K := C)
       (by simpa [hj'b])] at hiC
    · simpa [hj'b] using hodd _ _ hiC
    exact fun h' ↦ by simpa [hj'b] using hodd _ _ h'
  have hss : C ⊆ {F[0], F[n + 1]} := by grind
  have h0 := fun I ↦ ((hF.isNonloop (e := F[0]) (by simp))).indep.subset (I := I)
  have h1 := fun I ↦ ((hF.isNonloop (e := F[n + 1]) (by simp))).indep.subset (I := I)
  have h_eq : C = {F[0], F[n + 1]} := hss.eq_of_not_ssubset (by grind [hC.not_indep])
  obtain rfl : b = false := by simpa using hodd 0 (by lia) (by grind)
  have hnF : n.bodd = F.length.bodd := by simp [hn]
  obtain rfl : c = false := by simpa [hnF, hF.length_bodd_eq] using hodd (n + 1) (by lia) (by grind)
  refine h_pair rfl rfl ?_
  rw [parallel_iff_isCircuit (by grind), F.head_eq_getElem_zero, F.getLast_eq_getElem]
  simpa [hn, ← h_eq]

lemma IsFan.joints_indep' (hF : M.IsFan F b c)
    (h_pair : b = false → c = false → ¬ M.Parallel (F.head hF.ne_nil) (F.getLast hF.ne_nil)) :
    M.Indep (F.get '' {i | i.1.bodd = b}) := by
  convert hF.joints_indep h_pair
  refine Set.ext fun i ↦ ?_
  simp only [get_eq_getElem, mem_image, mem_setOf_eq, and_comm (a := _ = b)]
  constructor
  · rintro ⟨⟨x ,hx⟩, rfl, rfl⟩; grind
  rintro ⟨i, hi, rfl, rfl⟩
  use ⟨i, hi⟩

-- lemma encard_setOf_joint (hF : M.IsFan F b c) :
--     2 * {i | i < F.length ∧ i.bodd = b}.encard  = F.length + (b != c).toNat := by
--   induction hF using IsFan.induction₂ with
--   | of_pair M e f he hf hef d =>
--     simp [setOf_and]
--     cases d
--     sorry
--   | of_isTriangle M e f g d h =>
--     simp
--   | cons_cons M e f x y F c d h hT hf hT' he hey ih =>
--     simp_rw [length_cons (a := e), length_cons (a := f)

-- lemma IsFan.eRk_ge (hF : M.IsFan F b c) : F.length ≤ 2 * M.eRk {e | e ∈ F} := by
--   cases F with
--   | nil => simp

--   | cons e F =>
--     simp only [length_cons, Nat.cast_add, Nat.cast_one, mem_cons]
  -- cases b
  -- · cases c
  --   · cases hF using IsFan.induction₂_odd with
  --     | of_triangle M e f g b hT =>
  --       grw [IsTriangle.eRk (by simpa)]
  --       simp only [length_cons, length_nil, zero_add, Nat.reduceAdd, Nat.cast_ofNat]
  --       norm_num
  --     | cons_cons M e f x y F b h hT hf hT' he hey _ =>






lemma IsFan.getElem_mem_fanCircuit_iff {p q} (hF : M.IsFan F b c) {hi : i < F.length} :
    F[i] ∈ F.fanCircuit p q ↔ i = p ∨ i = q ∨ (p < i ∧ i < q ∧ i.bodd = !p.bodd) := by
  simp only [fanCircuit, get_eq_getElem, bne_iff_ne, ne_eq, mem_image, mem_setOf_eq,
    hF.nodup.getElem_inj_iff]
  exact ⟨by grind, fun h ↦ ⟨⟨i, hi⟩, by grind⟩⟩





lemma IsFan.getElem_mem_valsBetween_iff {p q d} (hF : M.IsFan F b c) {hi : i < F.length} :
    F[i] ∈ F.valsBetween p q d ↔ p ≤ i ∧ i ≤ q ∧ i.bodd = d := by
  simp only [valsBetween, exists_and_left, mem_setOf_eq]
  grind [hF.getElem_inj_iff]

lemma IsFan.baz (hF : M.IsFan F false false)
    (h_para : ¬ M.Parallel (F.head hF.ne_nil) (F.getLast hF.ne_nil)) :
    M.IsCircuit (insert (F.head hF.ne_nil) (insert (F.getLast hF.ne_nil)
      (F.valsBetween 0 (F.length - 1) true))) := by
  obtain ⟨n, hnF⟩ := Nat.exists_eq_add_of_le' hF.two_le_length
  induction n using Nat.twoStepInduction generalizing F with
  | zero => simpa [hnF] using hF.length_bodd_eq
  | one =>
    rw [hnF, show 1 + 2 - 1 = 0 + 2 from rfl, valsBetween_add_two _ rfl.le rfl (by lia),
      valsBetween_self_eq_empty rfl, head_eq_getElem, getLast_eq_getElem]
    simpa [hnF] using (hF.isTriangle_bDual (by grind)).swap_right.isCircuit
  | more n ih0 ih1 =>

    obtain rfl | n := n; sorry
    have hn_odd: n.bodd = false := sorry
    clear ih1
    have hF' : M.IsFan (List.drop 2 F) false false := by simpa using (hF.drop (k := 2) (by lia))
    specialize ih0 hF'
    simp only [head_eq_getElem, getElem_drop, add_comm 2, zero_add, getLast_eq_getElem, length_drop,
      hnF, add_assoc, Nat.reduceAdd, Nat.reduceSubDiff, Nat.add_one_sub_one, forall_const]
      at ih0 ⊢ h_para
    have h_even : n.bodd = false := by simpa [hnF] using hF.bool_right_eq
    specialize ih0 ?_
    · intro hpara
      have hp := (hF.isTriad_getElem_of_eq 1 (by lia) rfl).isCocircuit.mem_iff_mem_of_parallel hpara
      simp [hF.nodup.getElem_inj_iff] at hp

    have helim := ih0.strong_elimination (hF.isTriangle_getElem_of_eq 0 (by lia) rfl).isCircuit
      (e := F[2]) (f := F[n + 4]) (by simp) (by simp) (by simp) (by simp [hF.nodup.getElem_inj_iff])

    simp only [zero_add, union_insert, union_singleton, insert_comm (b := F[2]), Set.mem_insert_iff,
      true_or, insert_eq_of_mem, mem_singleton_iff, insert_diff_of_mem] at helim
    obtain ⟨C, hCss, hC, hnC⟩ := helim
    rw [insert_comm (F[1]), valsBetween_insert_drop_two (by lia) _ rfl] at hCss
    simp_rw [add_assoc, two_add_two_eq_four] at hCss


    have aux (d : ℕ) (hd : d ≤ n + 3) (hd_odd : d.bodd = true) : F[d] ∈ C ↔ F[1] ∈ C := by
      induction d using Nat.twoStepInduction with
      | zero => simp at hd_odd
      | one => rfl
      | more d ih ih1 =>
        obtain rfl | d := d; simp at hd_odd
        replace hd_odd : d.bodd = false := by simpa using hd_odd
        rw [← ih (by lia) (by simpa), (hF.isTriad_getElem_of_eq (d + 1) (by lia)
          (by simpa using hd_odd)).swap_left.mem_iff_mem_of_isCocircuit (by simpa)]
        refine notMem_subset hCss ?_
        simp [hF.getElem_mem_valsBetween_iff, hd_odd, hF.nodup.getElem_inj_iff,
          show d ≠ n + 2 by grind]

    obtain h1 | h1 := em' <| F[1] ∈ C
    · contrapose h_para
      rw [(hF.isNonloop (by simp)).parallel_iff_dep (hF.isNonloop (by simp))
        (by simp [hF.nodup.getElem_inj_iff])]
      refine hC.dep.superset ?_ (by grind [hF.get_mem_ground])
      intro x hxC
      suffices h' : x ∉ (F.drop 2).valsBetween 0 (n + 2) true by grind
      contrapose h1
      simp only [valsBetween, zero_le, getElem_drop, true_and, length_drop, exists_and_left,
        mem_setOf_eq] at h1
      obtain ⟨i, hin, hiodd, hilt, rfl⟩ := h1
      rwa [← aux (2 + i) _ (by simpa using hiodd)]
      grind [show i ≠ n + 2 by rintro rfl; simp [hn_odd] at hiodd]
    by_cases h0C : F[0] ∈ C
    · convert hC
      refine (hCss.trans diff_subset).antisymm' <| insert_subset h0C <| insert_subset hnC ?_
      simp only [valsBetween_subset_iff, zero_le, forall_const]
      intro i hi hile hiodd
      rwa [aux _ _ (by lia)]
      grind [show i ≠ n + 4 by rintro rfl; simp [hn_odd] at hiodd]






      -- simp only [valsBetween, zero_le, getElem_drop, true_and, length_drop, exists_and_left,
      --   mem_diff, Set.mem_insert_iff, mem_setOf_eq, mem_singleton_iff] at this
      -- simp [eq_comm (b := x)] at this









    --   _


    sorry

  -- generalize hb : false = b at hF

  -- induction hF using IsFan.induction₂_odd with
  -- | of_triangle M e f g b hT =>
  --   simp only [head_cons, ne_eq, reduceCtorEq, not_false_eq_true, getLast_cons, cons_ne_self,
  --     getLast_singleton, length_cons, length_nil, zero_add, Nat.reduceAdd]
  --   rw [valsBetween_add_two _ (by simp) rfl (by simp), valsBetween_self_eq_empty rfl]
  --   simpa [← hb] using hT.swap_right.isCircuit
  -- | cons_cons M e f x y F b h hT hf hT' he hey ih =>
  --   subst hb
  --   have hFne : F ≠ [] := by rintro rfl; simpa using h.bool_right_eq
  --   simp only [head_cons, ne_eq, reduceCtorEq, not_false_eq_true, getLast_cons, getLast_cons hFne,
  --     length_cons, add_tsub_cancel_right, forall_const] at *
  --   set u := F.getLast hFne with hu
  --   have hnp : ¬ M.Parallel x u := by
  --     intro hp
  --     grind [h.nodup, ((IsTriad.isCocircuit hT).mem_iff_mem_of_parallel hp).1 (by simp)]
  --   -- by the inductive hypothesis, the set `{x, u} ∪ K` is a circuit, where `K` is the set of
  --   -- cojoints between `x` and `u`. Apply strong elimination to this circuit and `{e, f, x}`
  --   -- to find a circuit `C` with `u ∈ C ⊆ {u, f} ∪ K`.
  --   obtain ⟨C, hCss, hC, heC⟩ := (ih hnp).strong_elimination hT'.isCircuit
  --     (e := x) (f := u) (by simp) (by simp) (by simp) (by grind [h.nodup])
  --   have aux (d : ℕ) (hd : d + 1 < (e :: f :: x :: y :: F).length) (hd_odd : d.bodd = false) :
  --       (e :: f :: x :: y :: F)[d + 1] ∈ C ↔ f ∈ C := by
  --     induction d using Nat.twoStepInduction with
  --     | one => simp at hd_odd
  --     | zero => simp
  --     | more n ih0 =>
  --       simp only [Nat.bodd_succ, Bool.not_not] at hd_odd
  --       rw [← ih0 (by grind) (by simpa using hd_odd)]
  --       have hK := ((h.cons hf hT).cons_not (e := e) (by grind) hT').isTriad_getElem_of_eq
  --         (i := n + 1) (by grind) (by simpa)
  --       simp_rw [add_right_comm]
  --       rw [hK.swap_left.mem_iff_mem_of_isCocircuit (K := C) (by simpa)]
  --       refine notMem_subset hCss ?_
  --       simp [h.getElem_mem_valsBetween_iff, hd_odd]
  --       suffices aux : (x :: y :: F)[n]'(by grind) ≠ u by grind
  --       rw [hu, ← getLast_cons (a := y), ← getLast_cons (a := x), getLast_eq_getElem,
  --         Ne, h.nodup.getElem_inj_iff]
  --       grind
  --   obtain hfC | hfC := em' <| f ∈ C
  --   · have hCss' : C ⊆ {e, u} := by
  --       intro z hzC
  --       simp only [union_insert, union_singleton, Set.mem_insert_iff, true_or,
  --         insert_eq_of_mem] at hCss
  --       have hzx : z ≠ x := by grind
  --       suffices z ∉ ((x :: y :: F).valsBetween 0 (F.length + 1) true) by grind
  --       simp only [valsBetween, zero_le, true_and, length_cons, Order.lt_add_one_iff,
  --         exists_and_left, mem_setOf_eq, not_exists, not_and]
  --       rintro (rfl | i) hi hi_odd hile rfl
  --       · simp at hi_odd
  --       rw [aux] at hzC



-- lemma IsFan.eq_first_last_of_parallel (hF : M.IsFan F b c) (h4 : 5 ≤ F.length) (hij : i < j)
--     (hj : j < F.length) (hp : M.Parallel F[i] F[j]) :
--     i = 0 ∧ j + 1 = F.length ∧ b = false ∧ c = false := by
--   have hc := hp.isCircuit_of_ne (by simpa [hF.nodup.getElem_inj_iff] using hij.ne)
--   obtain rfl | j := j; simp at hij
--   induction h : F.length generalizing F i j b c with
--   | zero => lia
--   | succ n ih =>
--     obtain rfl := hF.bool_right_eq
--     suffices i = 0 ∧ j + 1 = n ∧ b = false ∧ b = n.bodd by simpa [h]
--     obtain hjn | hjlt := ((show j + 2 ≤ F.length by grind).eq_or_lt).symm
--     · have hcon := ih (hF.dropLast (by lia)) ?_ _ hij (by grind) (by simpa) (by simpa) (by grind)
--       · simp only [h, Nat.bodd_succ, Bool.not_eq_eq_eq_not, Bool.not_false, beq_iff_eq] at hcon
--         obtain ⟨rfl, rfl, rfl, hbn⟩ := hcon
--         have hwin := (hF.isTriad_getElem_of_eq j (by lia)
--           (by simp [hbn])).swap_left.mem_or_mem_of_isCocircuit hc.isCocircuit (by simp)
--         simp [hF.nodup.getElem_inj_iff, show j ≠ 0 by grind] at hwin

--       obtain rfl | rfl | j := j
--       · obtain rfl : i = 0 := by grind
--         cases b
--         · have hT := (hF.isTriangle_getElem_of_eq 0 (by grind) rfl)
--           simpa [hF.nodup.getElem_inj_iff] using
--             hT.restrict_simple.eq_of_parallel_of_mem (e := F[0]) (f := F[1]) (by simp) (by simp) hp

--         sorry

--       -- have hi : i ≤ 2 := by grind
--       -- cases b
--       -- ·
--       --   have := (hF.isTriangle_getElem_of_eq 0 (by grind) rfl).restrict_simple.eq_of_parallel_of_mem
--       --     (e := F[i]) (f := F[j + 1])

--       sorry
--     sorry







      -- match F with
      -- | [] => sorry
      -- | F ++ [a] => sorry
      -- -- cases F using List.reverseRecOn with
      -- -- | nil => grind
      -- -- | append_singleton l a _ =>

    -- · sorry
    -- cases F using List.reverseRecOn with
    -- | nil => grind
    -- | append_singleton l a _ =>
    --   have :=

    -- obtain rfl | i := i
    -- · obtain hjn | hjlt := (show j + 1 ≤ F.length from hj).eq_or_lt
    --   · sorry
    --   cases F using List.reverseRecOn with
    --   | nil => grind
    --   | append_singleton l a _ =>
    --     have :=

  -- induction hF generalizing i j with
  -- | of_pair b e f he hf hne => simp at h4
  -- | cons_triangle e x y F b c h heF hT ih =>

  --   match F with
  --   | [] => simp at h4
  --   | [p, q] =>

  --     obtain rfl | i := i
  --     · obtain rfl | hlt := (show j ≤ 4 by grind).eq_or_lt
  --       · cases b
  --         · have hx := hT.mem_or_mem_of_isCircuit_bDual (K := {e, q}) (by simpa using hc) (by simp)
  --           grind [h.nodup]
  --         simp [h.bool_right_eq]


  --     --   obtain rfl | j := j; simp at hij
  --     --   have := ih (j := j) rfl.le ()
  --     -- sorry
  --       --
  --   | x :: y :: F => sorry

  #exit





      --
      -- · obtain rfl | i := i
      --   · cases b
      --     · have := hT.

  -- have hc := hp.isCircuit_of_ne (by simpa [hF.nodup.getElem_inj_iff] using hij.ne)
  -- obtain rfl | i := i
  -- · cases b
  --   · obtain hle | hlt := le_or_gt j 2
  --     · have hT := (hF.isTriangle_getElem_of_eq 0 (by lia) rfl)
  --       have := hT.isCircuit.eq_of_dep_subset hc.dep (by grind)
  --       grind [show (2 : ℕ∞) < 3 by norm_num, encard_pair_le, hT.three_elements]
  --     obtain rfl | rfl :=
  --     -- have := (hF.isTriad_getElem_of_eq (i := 1) (by lia) rfl).


  -- obtain rfl | hlt := (Order.add_one_le_of_lt hij).eq_or_lt
  -- ·
  --   obtain rfl | rfl := b.eq_or_eq_not i.bodd
  --   ·
  --     have := (hF.isTriangle_getElem_of_eq i ?_ rfl)



  -- match i with
  -- | 1 =>
  --   cases b
  --   · have hij :

  -- | i + 2 => sorry
  -- | 0 => sorry



/-- If `i` and `j` are joints in a fan with `i < j`, and `K` is the set of cojoints between
`i` and `j`, then `{i, j} ∪ K` is a circuit. -/
lemma IsFan.isCircuit_interval (hF : M.IsFan F b c) (h0i : 0 < i) (hij : i < j)
    (hjF : j + 1 < F.length) (hib : i.bodd = b) (hjb : j.bodd = b) :
    M.IsCircuit <| insert F[i] (insert F[j] (F.valsBetween i j (!b))) := by
  obtain ⟨d, hd, rfl⟩ : ∃ d, j = i + 2 * d + 2 := by
    subst hib
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hij
    cases hd : d.bodd; simp [hd] at hjb
    exact ⟨d.div2, by grind [d.bodd_add_div2]⟩
  induction d with
  | zero =>
    simp only [mul_zero, add_zero]
    rw [valsBetween_add_two _ (by lia) (by simpa) (by lia), valsBetween_self_eq_empty (by simpa),
      insert_empty_eq]
    exact (hF.isTriangle_getElem_of_eq (i := i) (by lia) hib).swap_right.isCircuit
  | succ d ih =>
    -- inductively, the set `C₀ = {i, i + 1, i + 3, ..., i + 2d + 1, i + 2d + 2}` is a circuit.
    specialize ih (by lia) (by lia) (by simpa)
    -- let `T` be the triangle starting with `i + 2 d + 2`.
    have hT := hF.isTriangle_getElem_of_eq (i := i + 2 * d + 2) (by lia) (by simpa)
    -- choose a circuit `C` containing `F i` and contained in `C ∪ T - F i`.
    obtain ⟨C, hCss, hC, hiC⟩ :=
      ih.strong_elimination hT.isCircuit (e := F[i + 2 * d + 2]) (f := F[i])
      (by simp) (by simp) (by simp) (by simp [hF.nodup.getElem_inj_iff, add_assoc])
    -- `C` is contained in the set we wish to show is a circuit; we want to show that
    -- in fact this set contains `C`.
    convert hC
    refine (hCss.trans ?_).antisymm' <| insert_subset hiC ?_
    · nth_rw 2 [valsBetween_add_two _ (by lia) (by simpa) (by lia)]
      grind
    suffices aux : ∀ x ≤ d + 1, F.valsBetween i (i + 2 * x + 2) (!b) ⊆ C
    · refine insert_subset ?_ (aux _ rfl.le)
      have hK := hF.isTriad_getElem_of_eq (i + 2 * (d + 1) + 1) (by lia) (by simpa)
      have h_or := hK.mem_or_mem_of_isCocircuit (K := C) (by simpa)
        (aux _ rfl.le ?_)
      · rwa [or_iff_left] at h_or
        refine notMem_subset hCss ?_
        simp [hF.nodup.getElem_inj_iff, add_assoc, mul_add, hF.getElem_mem_valsBetween_iff]
      simp [hF.getElem_mem_valsBetween_iff, hib, add_assoc]
    intro x hx
    induction x with
    | zero =>
      rw [valsBetween_add_two _ (by lia) (by simpa) (by lia), valsBetween_self_eq_empty (by simpa),
        insert_empty_eq]
      obtain rfl | i := i; simp at h0i
      have hT := hF.isTriad_getElem_of_eq i (by lia) (by simpa using hib)
      obtain hi | hi2 := hT.swap_left.mem_or_mem_of_isCocircuit (by simpa) hiC
      · simpa [hF.nodup.getElem_inj_iff, hF.getElem_mem_valsBetween_iff, add_assoc] using hCss hi
      simpa [add_assoc]
    | succ x ih =>
      rw [valsBetween_add_two _ (by lia) (by simpa) (by lia)]
      suffices F[i + 2 * x + 1 + 2] ∈ C by
        simpa [mul_add, ← add_assoc, insert_subset_iff, ih (by lia)]
      have hT := hF.isTriad_getElem_of_eq (i + 2 * x + 1) (by lia) (by simpa)
      rw [← hT.swap_left.mem_iff_mem_of_isCocircuit (by simpa)]
      · exact ih (by lia) <| by simpa [hF.getElem_mem_valsBetween_iff, add_assoc]
      refine notMem_subset hCss ?_
      suffices 2 * x = 2 * d + 1 ∨ 2 * x = 2 * d + 2 ∨ x = d → x = d by
        simpa [add_assoc, hF.nodup.getElem_inj_iff, hF.getElem_mem_valsBetween_iff, hib]
      lia


-- lemma IsFan.foo {b} (hF : M.IsFan F b c) (hC : M.IsCircuit C) (hCF : C ⊆ {e | e ∈ F})
--     (h0C : F.head hF.ne_nil ∉ C) (hlast : F.getLast hF.ne_nil ∉ C) :
--     (C = F.valsBetween 0 F.length (!b)) ∨
--     ∃ (i j : ℕ) (hi : 0 < i) (hij : i < j) (hj : j + 1 < F.length), i.bodd = b ∧ j.bodd = b ∧
--     C = insert F[i] (insert F[j] (F.valsBetween i j (!b))) := by
--   _

@[grind .]
lemma IsFan.length_ge_four_of_eq_ground [M.Simple] [M✶.Simple] (hF : M.IsFan F b c)
    (hFE : {e | e ∈ F} = M.E) : 4 ≤ F.length := by
  have hF2 := hF.two_le_length
  have hr := M.eRk_pair_eq (e := F[0]) (f := F[1]) (by simp [hF.nodup.getElem_inj_iff])
    (hF.get_mem_ground (i := 0)) (hF.get_mem_ground (i := 1))
  have hr1 := M✶.eRk_pair_eq (e := F[0]) (f := F[1]) (by simp [hF.nodup.getElem_inj_iff])
    (hF.get_mem_ground (i := 0)) (hF.get_mem_ground (i := 1))
  have hle := encard_le_encard hFE.symm.subset
  grw [← eRank_add_eRank_dual, F.encard_toSet_le, ← M.eRk_le_eRank {F[0], F[1]},
    ← M✶.eRk_le_eRank {F[0], F[1]}, hr, hr1] at hle
  enat_to_nat!; lia

/-- For any odd-length fan `F = [a, b, ..., z]` in which `a` is a joint
and `{a, b}` isn't a series pair, there is a circuit `C` with `a ∈ C ∩ F ⊆ {a, z}`. -/
lemma IsFan.exists_isCircuit_first_mem_of_length_odd (hF : M.IsFan F false c)
    (h_odd : Odd F.length) (h01 : ¬ M✶.Parallel (F[0]'(by grind)) (F[1]'hF.two_le_length)) :
    ∃ C, M.IsCircuit C ∧ F[0]'(by grind) ∈ C ∧ ∀ i (hi : i + 1 < F.length),
      F[i + 1] ∈ C → i + 2 = F.length := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hF.two_le_length
  suffices aux : ∀ k ≤ n, ∃ C, M.IsCircuit C ∧ F[0] ∈ C ∧
      ∀ i (hi : i + 1 < F.length), F[i + 1] ∈ C → k ≤ i from
    Exists.imp (by grind) <| aux n rfl.le
  rw [parallel_dual_iff_forall_circuit (hF.dual.isNonloop (by simp)) hF.get_mem_ground] at h01
  simp_rw [not_forall, exists_prop] at h01
  intro k hk
  induction k with
  | zero => exact Exists.imp (by grind) h01
  | succ k ih =>
    obtain rfl | k := k
    · exact Exists.imp (by grind) h01
    obtain ⟨C, hC, h0C, hClt⟩ := ih (by lia)
    obtain hkC | hkC := em' (F[k + 2] ∈ C)
    · exact ⟨C, by grind⟩
    by_cases hb : k.bodd = true
    · obtain hwin | hwin := (hF.isTriangle_getElem k (by lia)).reverse.mem_or_mem_of_isCircuit_bDual
        (by simpa [hb]) hkC
      · grind
      obtain rfl | k := k; simp at hb
      grind
    have hnk : n ≠ k + 2 := fun hnk ↦ by simpa [hn, hnk, hb] using h_odd.bodd
    have hT : M.IsTriangle {F[k + 2], F[k + 2 + 1], F[k + 2 + 2]} := by
      simpa [hb] using hF.isTriangle_getElem (k + 2) (by grind)
    obtain ⟨C', hC'ss, hC', h0C'⟩ := hC.strong_elimination hT.isCircuit hkC (by simp) h0C
      (by simp [hF.nodup.getElem_inj_iff])
    refine ⟨C', hC', h0C', fun i hilt hiC' ↦ ?_⟩
    obtain ⟨(rfl | rfl | hiC), hik⟩ : (i = k + 2 ∨ i = k + 3 ∨ F[i + 1] ∈ C) ∧ ¬i = k + 1 := by
      simpa [hF.nodup.getElem_inj_iff] using hC'ss hiC'
    all_goals grind


/-- If `M` is a simple, cosimple matroid whose ground set is a fan, then the fan is even
and wraps around its own beginning.  -/
lemma IsFan.isTriangle_of_simple (hF : M.IsFan F false c) {n : ℕ} (h3 : F.length = n + 2)
    (hM : M.Simple) (hM' : M✶.Simple) (hFE : {e | e ∈ F} = M.E) :
      Even F.length ∧ M.IsTriangle {F[n], F[n + 1]'(by grind), F[0]} := by
  obtain rfl | rfl | n := n
  · grind [hF.length_ge_four_of_eq_ground hFE]
  · grind [hF.length_ge_four_of_eq_ground hFE]
  have hnp : ¬M✶.Parallel F[0] F[1] := by
    rw [hM'.parallel_iff_eq (hF.dual.subset_ground (getElem_mem ..))]
    simp [hF.nodup.getElem_inj_iff]
  set m := if Odd n then n + 3 else n + 2 with hm
  have hmlt : m < F.length := by lia
  have hm_odd : Odd (m + 1) := by simp [hm, Nat.odd_add_one, apply_ite]
  -- Take away the last element if the fan is even, then find a circuit containing `F[0]`
  -- that intersects the fan in only possibly the last element.
  obtain ⟨C, hC, h0C, hlt⟩ :=
    (hF.take (show 2 ≤ m + 1 by grind) (by lia)).exists_isCircuit_first_mem_of_length_odd
    (by rwa [length_take_of_le (by lia)]) (by rwa [getElem_take, getElem_take])
  simp_rw [length_take_of_le (show m + 1 ≤ F.length by lia), getElem_take] at hlt
  have hss : C ⊆ {F[m], F[n + 3], F[0]} := by
    intro e he
    obtain ⟨rfl | i, hi, rfl⟩ := getElem_of_mem <| hC.subset_ground.trans hFE.symm.subset he
    · simp
    obtain hlt | hle := lt_or_ge i m
    all_goals grind
  obtain hn | hn := Nat.even_or_odd n
  · simp_rw [hm, if_neg (show ¬ Odd n by simpa)] at hss
    refine ⟨by grind, isTriangle_of_dep_of_encard_le
      (hC.dep.superset hss (by simp [insert_subset_iff, hF.get_mem_ground])) ?_⟩
    grw [encard_insert_le, encard_pair_le, show (2 : ℕ∞) + 1 = 3 from rfl]
  have hcard := encard_le_encard hss
  simp_rw [hm, if_pos hn] at hcard
  grw [insert_eq_of_mem (by simp), encard_pair_le, ← hC.girth_le_card, ← M.three_le_girth] at hcard
  norm_num at hcard

lemma IsFan.isTriangle_bDual_of_simple (hF : M.IsFan F b c) {n : ℕ} (h3 : F.length = n + 2)
    (hM : M.Simple) (hM' : M✶.Simple) (hFE : {e | e ∈ F} = M.E) : Even F.length ∧
      (M.bDual b).IsTriangle {F[n], F[n + 1]'(by grind), F[0]} := by
  simpa using IsFan.isTriangle_of_simple (M := M.bDual (b)) (F := F) (c := c != b) (by simpa) h3
    (by cases b with simpa) (by cases b with simpa) (by simpa)
