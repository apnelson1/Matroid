module

public import Matroid.Connectivity.Fan_.Basic
public import Matroid.Connectivity.Triangle
public import Matroid.Connectivity.Separation.Vertical
public import Matroid.ForMathlib.Fin
public import Mathlib.Data.Vector.Basic

@[expose] public section

set_option linter.style.longLine false

variable {α : Type*} {M : Matroid α} {X Y C K T : Set α} {e f g x y : α} {b c d : Bool}
    {J : Bool → List α} {L : List α} {n i j p q r : ℕ} {F J : List α} {b c : Bool}

open Set List

@[simp]
lemma List.range_getElem_fin {α : Type*} {L : List α} :
    Set.range (fun (i : Fin L.length) ↦ L[i.1]) = {e | e ∈ L} := by
  simp_rw [← get_eq_getElem, range_list_get]

lemma List.Nodup.injective_getElem_fin {α : Type*} {L : List α} (hL : L.Nodup) :
    Function.Injective fun (i : Fin L.length) ↦ L[i.1] :=
  hL.injective_get

lemma List.image_getElem_preimage_val_insert {α : Type*} {L : List α} (s : Set ℕ) {i : ℕ}
    (hi : i < L.length) : (fun x : Fin L.length ↦ L[x.1]) '' (Fin.val ⁻¹' (insert i s)) =
      insert L[i] ((fun x : Fin L.length ↦ L[x.1]'x.2) '' (Fin.val ⁻¹' s)) := by
  rw [← singleton_union, preimage_union, image_union, show Fin.val ⁻¹' {i} = {⟨i, hi⟩} by
    grind, image_singleton, singleton_union]

lemma List.Nodup.image_getElem_preimage_val_sdiff_singleton {L : List α} (hL : L.Nodup)
    (s : Set ℕ) {i : ℕ} (hi : i < L.length) :
    (fun x : Fin L.length ↦ L[x.1]) '' (Fin.val ⁻¹' s) \ {L[i]} =
    (fun x : Fin L.length ↦ L[x.1]) '' (Fin.val ⁻¹' (s \ {i})) := by
  rw [preimage_sdiff, image_sdiff hL.injective_getElem_fin,
  show Fin.val ⁻¹' {i} = {⟨i, hi⟩} by grind, image_singleton]

lemma List.image_getElem_preimage_val_singleton {α : Type*} {L : List α} {i : ℕ}
    (hi : i < L.length) : (fun x : Fin L.length ↦ L[x.1]) '' (Fin.val ⁻¹' {i}) = {L[i]} := by
  rw [← insert_empty_eq, image_getElem_preimage_val_insert _ hi]
  simp

lemma List.image_getElem_fin_rotate' {α : Type*} {L : List α} (k : Fin L.length)
    (s : Set (Fin (L.rotate k).length)) : (fun x ↦ (L.rotate k)[x.1]) '' s =
    (fun x ↦ L[x.1]) '' (fun x ↦ x + k) '' (Fin.cast (by simp)) ⁻¹' s := by
  have := k.neZero
  simp only [image_image, rotate_getElem_fin]
  simp [Set.ext_iff, Fin.exists_iff]

lemma List.image_getElem_fin_rotate {α : Type*} {L : List α} (k : Fin L.length)
    (s : Set (Fin (L.rotate k).length)) : (fun x ↦ (L.rotate k)[x.1]) '' s =
    (fun x ↦ L[x.1]) '' (fun x ↦ x - k) ⁻¹' (Fin.cast (by simp)) ⁻¹' s := by
  have := k.neZero
  rw [List.image_getElem_fin_rotate', image_eq_preimage_of_inverse
    (leftInverse_sub_add_left k) (leftInverse_add_left_sub k)]

lemma List.image_getElem_fin_reverse {α : Type*} {L : List α}
    (s : Set (Fin L.reverse.length)) : (fun x ↦ L.reverse[x.1]) '' s
    = (fun x : Fin L.length ↦ L[x.1]) '' Fin.rev ⁻¹' (Fin.cast (by simp)) ⁻¹' s := by
  simp_rw [reverse_getElem_fin, ← Fin.image_rev, image_image]
  simp [Set.ext_iff, Fin.exists_iff]

lemma List.image_getElem_preimage_val_rotate {α : Type*} {L : List α} (s : Set ℕ)
    (k : Fin L.length) : (fun x : Fin (L.rotate k).length ↦ (L.rotate k)[x.1]) '' (Fin.val ⁻¹' s) =
    (fun x ↦ L[x.1]) '' (fun i ↦ i + k) '' (Fin.val ⁻¹' s) := by
  have := k.neZero
  simp_rw [image_image, rotate_getElem_fin]
  simp [Set.ext_iff, Fin.exists_iff]

lemma List.image_getElem_preimage_val_rotate' {α : Type*} {L : List α} (s : Set ℕ)
    (k : Fin L.length) : (fun x : Fin (L.rotate k).length ↦ (L.rotate k)[x.1]) '' (Fin.val ⁻¹' s) =
    (fun x ↦ L[x.1]) '' (fun i ↦ i - k) ⁻¹' (Fin.val ⁻¹' s) := by
  have := k.neZero
  rw [image_getElem_preimage_val_rotate, image_eq_preimage_of_inverse
    (leftInverse_sub_add_left k) (leftInverse_add_left_sub k)]

lemma List.image_getElem_preimage_val_reverse {α : Type*} {L : List α} (s : Set ℕ) :
    (fun x : Fin L.reverse.length ↦ L.reverse[x.1]) '' (Fin.val ⁻¹' s) =
    (fun x : Fin L.length ↦ L[x.1]) '' (Fin.rev ⁻¹' Fin.val ⁻¹' s) := by
  rw [← Fin.rev_involutive.image_eq_preimage_symm, image_image]
  simp [add_comm _ 1, Nat.sub_sub, Set.ext_iff, Fin.exists_iff]

lemma List.Nodup.mem_image_getElem_preimage_val_iff {α : Type*} {L : List α} (hL : L.Nodup)
    {i : ℕ} {s : Set ℕ} (hi : i < L.length) :
    L[i] ∈ (fun x : Fin L.length ↦ L[x.1]) '' (Fin.val ⁻¹' s) ↔ i ∈ s := by
  rw! [show i = (⟨i, hi⟩ : Fin L.length).val from rfl, hL.injective_getElem_fin.mem_set_image,
    mem_preimage]
  rfl

lemma List.image_getElem_preimage_val_subset_iff {L : List α} {s : Set ℕ} {t : Set α} :
    (fun x : Fin L.length ↦ L[x.1]) '' (Fin.val ⁻¹' s) ⊆ t ↔
    ∀ i (hi : i < L.length), i ∈ s → L[i] ∈ t := by
  rw [image_subset_iff]
  exact ⟨fun h i hi his ↦ by simpa using h (show ⟨i, hi⟩ ∈ Fin.val ⁻¹' s from his),
    fun h i hi ↦ h i i.2 hi⟩

lemma List.getElem_mem_image_getElem_preimage_val {L : List α} {i : ℕ} {s : Set ℕ}
    {hi : i < L.length} (his : i ∈ s) : L[i] ∈ (fun x : Fin L.length ↦ L[x.1]) '' (Fin.val ⁻¹' s) :=
  ⟨⟨i, hi⟩, his, rfl⟩




namespace Matroid


lemma IsFan.isTriangle_get [NeZero F.length] (hF : M.IsFan F b c) (i : Fin F.length)
    (hi : i.val + 2 < F.length) :
    (M.bDual (b != i.1.bodd)).IsTriangle {F[i], F[i + 1], F[i + 2]} := by
  have : Fact (1 < F.length) := ⟨by lia⟩
  have := hF.isTriangle_getElem i hi
  rw! [Fin.getElem_fin, Fin.getElem_fin, Fin.getElem_fin, Fin.val_add_eq_of_add_lt,
    Fin.val_add_eq_of_add_lt (b := 2), Fin.val_one', Nat.one_mod',
    Fin.coe_ofNat_eq_mod, Nat.mod_eq_of_lt (show 2 < F.length by lia)]
  · assumption
  · rwa [Fin.coe_ofNat_eq_mod, Nat.mod_eq_of_lt (by lia)]
  grw [← hi, Fin.val_one', Nat.one_mod']
  lia

lemma IsFan.isTriangle_get' [NeZero F.length] (hF : M.IsFan F b c) (i : Fin F.length)
    (hitop : i ≠ ⊤) (hi' : i + 1 ≠ ⊤) :
    (M.bDual (b != i.1.bodd)).IsTriangle {F[i], F[i + 1], F[i + 2]} := by

  refine hF.isTriangle_get i ?_
  by_cases hF1 : F.length = 1
  · have hcon : i = ⊤ := by simpa using Subsingleton.elim (i.cast hF1) ⊤
    contradiction
  have _ : Fact (1 < F.length) := ⟨by lia⟩
  simp only [Ne, ← Fin.val_inj, Fin.val_top] at hi' hitop
  rw [Fin.val_add_eq_of_add_lt, Fin.val_one', Nat.one_mod'] at hi'
  · grind
  rw [Fin.val_one', Nat.one_mod']
  grind

lemma IsFan.isTriangle_get_sub_add [NeZero F.length] (hF : M.IsFan F b c) (i : Fin F.length)
    (hi0 : i ≠ 0) (hitop : i ≠ ⊤) :
    (M.bDual (b == i.1.bodd)).IsTriangle {F[i - 1], F[i], F[i + 1]} := by
  simpa [ne_eq, sub_eq_iff_eq_add, Fin.top_add, hi0, hitop, show i - 1 + 2 = i + 1 by grind,
    Fin.bodd_val_sub_one hi0] using hF.isTriangle_get' (i - 1)


/-- Under an appropriate nondegeneracy assumption, any interval of joints or cojoints
is independent. -/
lemma IsFan.joints_Icc_indep (hF : M.IsFan F b c) {p q : ℕ}
    (hpq : p = 0 → F.length ≤ q + 1 →
      ∀ (hb : b = false) (hc : c = false), ¬ M.Parallel F[0] F[F.length - 1]) :
    M.Indep (F.get '' Fin.val ⁻¹' (Icc p q ∩ Nat.bodd ⁻¹' {b})) := by
  by_cases h2 : F.length ≤ 2
  · match F with
    | [] =>
      grw [image_subset_range]
      simp
    | [e] =>
      grw [Set.inter_subset_right, preimage_singleton, preimage_ofPred_eq]
      cases b
      · simpa using (isFan_single_iff.1 hF).1
      simp
    | [e, f] =>
      grw [Set.inter_subset_right, preimage_singleton, preimage_ofPred_eq]
      cases b
      · exact hF.isNonloop_left.indep.subset <| by simp
      exact hF.isNonloop_right.indep.subset <| by simp
  rw [indep_iff_forall_subset_not_isCircuit (by grind)]
  simp only [subset_image_iff, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    get_eq_getElem]
  have : NeZero F.length := ⟨by lia⟩
  intro C hCodd hC
  by_cases hss : C ⊆ {0, ⊤}
  · obtain rfl : C = {0, ⊤} := by
      rw [← hF.nodup.injective_getElem_fin.image_injective.eq_iff,
        hC.dep.eq_of_subset_pair (by grw [hss, image_pair])
        (hF.isNonloop_getElem _ _ (by simp [h2])) (hF.isNonloop_getElem _ _ (by simp [h2])),
        image_pair]
    obtain ⟨⟨rfl, rfl⟩, hq, rfl⟩ : (p = 0 ∧ b = false) ∧ F.length ≤ q + 1 ∧ c = false := by
      simp only [preimage_inter, subset_inter_iff, pair_subset_iff, mem_preimage,
        Fin.coe_ofNat_eq_mod, Nat.zero_mod, mem_Icc, nonpos_iff_eq_zero, zero_le, and_true,
        Fin.val_top, tsub_le_iff_right, Nat.bodd_zero, mem_singleton_iff, Bool.false_eq,
        hF.length_sub_one_bodd_eq (by lia)] at hCodd
      grind
    rw [image_pair, ← parallel_iff_isCircuit (by
      simp [hF.nodup.getElem_inj_iff, show 0 ≠ F.length - 1 by lia])] at hC
    exact hpq rfl hq rfl rfl <| by simpa using hC
  obtain ⟨x, hxC, hne⟩ := not_subset.1 hss
  have hT := (hF.isTriangle_get_sub_add x (by grind) (by grind)).swap_left
  obtain h := hT.mem_or_mem_of_isCircuit_bDual (K := F.get '' C)
    (by simpa [show x.1.bodd = b from (hCodd hxC).2]) (mem_image_of_mem _ hxC)
  simp_rw [Fin.getElem_fin, ← get_eq_getElem, hF.nodup.injective_get.mem_set_image] at h
  have hxb : x.1.bodd = b := by grind
  obtain h | h := h
  · simpa [Fin.bodd_val_sub_one (show x ≠ 0 by grind), hxb] using hCodd h
  simpa [Fin.bodd_val_add_one (show x ≠ ⊤ by grind), hxb] using hCodd h

/-- Under an appropriate nondegeneracy assumption, any interval of joints or cojoints
is independent. -/
lemma IsFan.joints_Icc_fin_indep [NeZero F.length] (hF : M.IsFan F b c) {p q : Fin F.length}
    (hpq : p = 0 → q = ⊤ → ∀ (hb : b = false) (hc : c = false), ¬ M.Parallel F[0] F[F.length - 1]) :
    M.Indep (F.get '' {x ∈ Icc p q | x.1.bodd = b}) := by
  obtain ⟨p, hp⟩ := p
  obtain ⟨q, hq⟩ := q
  convert hF.joints_Icc_indep (p := p) (q := q) ?_ using 2
  · simp [Set.ext_iff, Fin.forall_iff]
  simpa [← Fin.val_inj, show q = F.length - 1 ↔ F.length ≤ q + 1 by lia] using hpq

lemma IsFan.image_getElem_Icc_subset_closure (hF : M.IsFan F b c) {p q : ℕ} (hq : q < F.length)
    (hpb : p.bodd = b) (hqb : q.bodd = b) :
      (fun x : Fin F.length ↦ F[x.1]) '' (Fin.val ⁻¹' (Icc p q)) ⊆
      M.closure ((fun x  : Fin F.length ↦ F[x.1]) ''
        Fin.val ⁻¹' ((Icc p q) ∩ Nat.bodd ⁻¹' {b})) := by
  rintro _ ⟨⟨i, hi⟩, ⟨hpi : p ≤ i, hiq : i ≤ q⟩, rfl⟩
  obtain rfl | rfl := b.eq_or_eq_not i.bodd
  · exact M.mem_closure_of_mem' (mem_image_of_mem _ (by simp [hpi, hiq])) hF.getElem_mem_ground
  obtain rfl | i := i
  · grind
  have hT := hF.isTriangle_getElem_of_eq i (by simp) (by grind)
  refine mem_of_mem_of_subset hT.mem_closure₂ <| M.closure_subset_closure <| pair_subset ?_ ?_
  · rw [hF.nodup.mem_image_getElem_preimage_val_iff]
    simp [show p ≤ i by grind, show i ≤ q by grind]
  rw [hF.nodup.mem_image_getElem_preimage_val_iff]
  simp [show p ≤ i + 2 by grind, show i + 2 ≤ q by grind]

/-- The joints are always independent, unless the first and last element are parallel joints. -/
lemma IsFan.joints_indep (hF : M.IsFan F b c)
    (h_pair : ∀ (hb : b = false) (hc : c = false), ¬ M.Parallel F[0] F[F.length - 1]) :
    M.Indep (F.get '' {i | i.1.bodd = b}) := by
  obtain rfl | hne := eq_or_ne F []
  · grw [image_subset_range]
    simp
  have : NeZero F.length := ⟨(length_pos_of_ne_nil hne).ne'⟩
  have hwin := hF.joints_Icc_indep (p := 0) (q := F.length - 1) (by grind)
  simp_rw [Icc_zero_left, ← Fin.range_val_eq_Iic, inter_comm, preimage_inter_range] at hwin
  assumption

lemma IsFan.eRk_ge (hF : M.IsFan F b c) :
    F.length ≤ 2 * M.eRk ({e | e ∈ F}) + F.length.bodd.toNat := by
  wlog hbc : b = false → c = false generalizing F b c with aux
  · simpa using aux hF.reverse (by grind)
  obtain h2 | h3 := lt_or_ge F.length 1
  · match F with | [] => simp
  obtain rfl | rfl := b
  · grw [← eRk_subset_le (X := F.tail.get '' {i | i.1.bodd = !false})
      _ (by simp), ((hF.tail (by grind)).joints_indep (by simp)).eRk_eq_encard, hF.length_bodd_eq,
      hF.nodup.tail.injective_get.encard_image]
    simpa [preimage, hF.length_sub_one_bodd_eq (by lia), hbc rfl]
      using (Fin.encard_setOf_bodd F.tail.length true).ge
  grw [← eRk_subset_le (X := F.get '' {i | i.1.bodd = true}) _ (by simp),
    (hF.joints_indep (by simp)).eRk_eq_encard, hF.nodup.injective_get.encard_image]
  cases c with simpa [preimage,hF.length_bodd_eq] using (Fin.encard_setOf_bodd F.length true).ge

lemma IsFan.eRk_eq (hF : M.IsFan F b b) (hpara : ¬ (M.bDual b).Parallel F[0] (F[F.length - 1])) :
    2 * (M.bDual b).eRk {e | e ∈ F} = F.length + 1 := by
  refine le_antisymm (by simpa using (hF.bDual b).eRk_le) ?_
  grw [← ((hF.bDual b).joints_indep (by simpa)).encard_le_eRk_of_subset (by simp),
    hF.nodup.injective_get.encard_image]
  simpa [hF.length_bodd_eq, preimage] using (Fin.encard_setOf_bodd F.length (b != b)).ge

/-- Let `F[p]` and `F[q]` be joints of a fan, and `K` be the set of cojoints between `p` and `q`.
If `F[p]` and `F[q]` are not parallel and at the beginning and the end of the fan,
then `{F[p], F[q]} ∪ K` is a circuit.

The nondegeracy hypothesis has some redundancy, since `i = 0` and `q + 1 = F.length` implies that
`b = c = false`; we include it so it is easier to discharge quickly in various cases.  -/
lemma IsFan.isCircuit_interval (hF : M.IsFan F b c) {p q : ℕ} (hpq : p < q) (hq : q < F.length)
    (hpb : p.bodd = b) (hqb : q.bodd = b)
    (hdg : b = false → c = false → p = 0 → q + 1 = F.length → ¬ M.Parallel F[0] F[F.length - 1]) :
    M.IsCircuit <| F.get '' Fin.val ⁻¹' ({p, q} ∪ (Icc p q ∩ Nat.bodd ⁻¹' {!b})) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hpq.le
  simp_rw [get_eq_getElem]
  rw! [preimage_union, image_union, image_getElem_preimage_val_insert _ (by lia),
    image_getElem_preimage_val_singleton hq]
  induction d using Nat.twoStepInduction with
  | zero => simp at hpq
  | one => simp [hpb] at hqb
  | more d ih _ =>
    replace hqb : d.bodd = false := by cases b with simpa [hpb] using hqb
    rw! [show p + (d + 2) = (p + d) + 1 + 1 by lia, ← insert_Icc_right_eq_Icc_add_one (by lia),
      insert_inter_of_notMem (by simp [hpb, hqb]), ← insert_Icc_right_eq_Icc_add_one (by lia),
      insert_inter_of_mem (by simp [hpb, hqb]), image_getElem_preimage_val_insert _ (by lia)]
    have hT := (hF.isTriangle_getElem_of_eq (p + d) (by simp [hpb, hqb])).swap_right
    obtain rfl | hne := eq_or_ne d 0
    · rw! [add_zero, Icc_self, singleton_inter_of_notMem (by simpa), preimage_empty, image_empty,
        insert_empty_eq, union_singleton]
      simpa using hT.reverse.swap_right.isCircuit
    generalize hC₀ : (fun x : Fin F.length ↦ F[x.1]) '' Fin.val ⁻¹'
      (Icc p (p + d) ∩ Nat.bodd ⁻¹' {!b}) = C₀ at ⊢ ih
    specialize ih (by lia) (by lia) (by simp [hpb, hqb]) (by lia)
    convert hT.union_diff_singleton_isCircuit ih (by simp) ?_
    · rw! [add_assoc, one_add_one_eq_two, pair_comm, insert_union, union_insert, pair_comm,
      insert_union, insert_sdiff_self_of_notMem]
      · rfl
      rw [← Ico_insert_right (by lia), insert_inter_of_notMem (by simp [hpb, hqb])] at hC₀
      simp +contextual [← hC₀, hF.nodup.getElem_inj_iff, hne, ne_of_lt]
    grw [← hC₀, inter_subset_left, union_eq_self_of_subset_left
      (pair_subset (getElem_mem_image_getElem_preimage_val (by simp))
      (getElem_mem_image_getElem_preimage_val (by simp))),
      hF.image_getElem_Icc_subset_closure (by lia) hpb (by simp [hpb, hqb]), closure_closure]
    refine notMem_subset (M.closure_subset_closure ?_) <|
      (hF.joints_Icc_indep (p := p) (q := p + d + 2) (by grind)).notMem_closure_sdiff_of_mem ?_
    · simp_rw [get_eq_getElem]
      rw! [hF.nodup.image_getElem_preimage_val_sdiff_singleton,
        show p + d + 2 = p + d + 1 + 1 by lia, ← insert_Icc_right_eq_Icc_add_one (by lia),
        insert_inter_of_mem (by simp [hpb, hqb]), ← insert_Icc_right_eq_Icc_add_one (by lia),
        insert_inter_of_notMem (by simp [hpb, hqb]), insert_sdiff_self_of_notMem (by simp)]
      rfl
    exact getElem_mem_image_getElem_preimage_val <| by simp [add_assoc, hpb, hqb]

lemma IsFan.isCircuit_interval_Ioo (hF : M.IsFan F b c) {p q : ℕ} (hpq : p < q) (hq : q < F.length)
    (hpb : p.bodd = b) (hqb : q.bodd = b)
    (hdg : b = false → c = false → p = 0 → q + 1 = F.length → ¬ M.Parallel F[0] F[F.length - 1]) :
    M.IsCircuit <| F.get '' Fin.val ⁻¹' ({p, q} ∪ (Ioo p q ∩ Nat.bodd ⁻¹' {!b})) := by
  convert hF.isCircuit_interval hpq hq hpb hqb hdg using 4
  obtain rfl | q := q
  · simp at hpq
  rw [← insert_Icc_add_one_left_eq_Icc hpq.le, insert_inter_of_notMem (by simpa),
    ← insert_Icc_right_eq_Icc_add_one (by lia), insert_inter_of_notMem
    (by cases b with simpa using hqb), Icc_add_one_left_eq_Ioc, Ioo_add_one_right_eq_Ioc]

lemma IsFan.isCircuit_quad (hF : M.IsFan F b c) (p) (hp : p + 4 < F.length) (hpb : p.bodd = b)
    (h5 : ∀ (h : F.length = 5), ¬ M.Parallel F[0] F[4]) :
    M.IsCircuit {F[p], F[p + 1], F[p + 3], F[p + 4]} := by
  have aux :
      b = false → c = false → p = 0 → p + 4 + 1 = F.length → ¬M.Parallel F[0] F[F.length - 1] := by
    rintro rfl rfl rfl h5'
    simpa [← h5'] using h5 h5'.symm
  have hC := hF.isCircuit_interval (show p < p + 4 by lia) hp hpb (by simpa) aux
  rw [pair_comm, insert_comm F[p + 1]]
  simp_rw [get_eq_getElem] at hC
  rwa [← insert_Icc_add_one_left_eq_Icc (by lia), insert_inter_of_notMem (by simpa),
    ← insert_Icc_add_one_left_eq_Icc (by lia), insert_inter_of_mem (by simpa),
    ← insert_Icc_add_one_left_eq_Icc (by lia), insert_inter_of_notMem (by simpa),
    ← insert_Icc_add_one_left_eq_Icc (by lia), insert_inter_of_mem (by simpa),
    show p + 1 + 1 + 1 = p + 3 from rfl, show p + 3 + 1 = p + 4 from rfl, Icc_self,
    singleton_inter_of_notMem (by simpa), insert_empty_eq, preimage_union, image_union,
    image_getElem_preimage_val_insert _ (by lia), image_getElem_preimage_val_insert _ (by lia),
    image_getElem_preimage_val_singleton (by lia), image_getElem_preimage_val_singleton (by lia),
    insert_union, singleton_union] at hC

/-- If a circuit `C` contains joints `F[p], F[q]` with `p < q`, and the cojoint `F[p + 1]`,
then `C` is an interval. -/
lemma IsFan.eq_interval_of_mem_mem_mem (hF : M.IsFan F b c) (hpq : p < q)
    (hqF : q < F.length) (hpb : p.bodd = b) (hqb : q.bodd = b) (hC : M.IsCircuit C)
    (hpC : F[p] ∈ C) (hp1C : F[p + 1] ∈ C) (hqC : F[q] ∈ C) :
    C = (fun x : Fin F.length ↦ F[x.1]) ''
      Fin.val ⁻¹' ({p, q} ∪ (Icc p q ∩ Nat.bodd ⁻¹' {!b})) := by
  induction q using Nat.strong_induction_on with | h q ihq =>
  suffices ∀ i (hi : i < F.length), p ≤ i → i ≤ q → i.bodd = !b → F[i] ∈ C by
    refine hC.eq_of_superset_isCircuit (hF.isCircuit_interval hpq hqF hpb hqb ?_) <| by
      refine image_getElem_preimage_val_subset_iff.2 fun i hiF hi ↦ by grind
    rintro rfl rfl rfl hq hpara
    replace hpara := (hpara.isCircuit_of_ne (by simp [hF.nodup.getElem_inj_iff,
      show 0 ≠ F.length - 1 by lia])).eq_of_subset_isCircuit hC
    obtain rfl : {F[0], F[q]} = C := by simpa [← hq, pair_subset hpC hqC] using hpara
    obtain rfl : 1 = q := by simpa [hF.nodup.getElem_inj_iff] using hp1C
    simp at hqb
  intro i hi hpi hiq hib
  obtain ⟨d, rfl⟩ := exists_add_of_le hpi
  induction d using Nat.twoStepInduction with
  | zero => simpa
  | one => exact hp1C
  | more d ih _ =>
    by_contra hcon
    specialize ih (by lia) (by lia) (by lia) (by simpa using hib)
    rw [← (hF.isTriad_getElem_of_eq (p + d) (by simpa using hib)).reverse.mem_iff_mem_of_isCircuit
      hC (by simpa)] at ih
    replace ihq := ihq (p + d + 1) (by lia) (by lia) (by lia) (by cases b with simpa using hib) hpC
      hp1C ih
    rw [ihq, hF.nodup.mem_image_getElem_preimage_val_iff] at hqC
    simp [hqb, hpq.ne.symm, show q ≠ p + d + 1 by lia] at hqC

/-- If a circuit of a matroid contains joints `F[p + 1], F[q]` of a fan `F`,
and does not contain the cojoint `F[p]`,
then it comprises precisely `F[p + 1], F[q]`, and the cojoints between them.  -/
lemma IsFan.eq_interval_of_notMem_mem_mem (hF : M.IsFan F b c) (hpq : p + 1 < q)
    (hqF : q < F.length) (hpb : p.bodd = !b) (hqb : q.bodd = b) (hC : M.IsCircuit C)
    (hpC : F[p] ∉ C) (hp1C : F[p + 1] ∈ C) (hqC : F[q] ∈ C) :
    C = (fun x : Fin F.length ↦ F[x.1]) '' Fin.val ⁻¹'
      ({p + 1, q} ∪ (Icc (p + 1) q ∩ Nat.bodd ⁻¹' {!b})) := by
  refine hF.eq_interval_of_mem_mem_mem hpq hqF (by simpa) hqb hC hp1C (by_contra fun h ↦ hpC ?_) hqC
  rwa [← (hF.isTriad_getElem_of_eq p hpb).reverse.mem_iff_mem_of_isCircuit hC h]

lemma IsFan.exists_eq_interval_of_notMem_mem_add_one (hF : M.IsFan F b c) (hpq : p + 1 < q)
    (hqF : q < F.length) (hpb : p.bodd = !b) (hqb : q.bodd = !b) (hC : M.IsCircuit C)
    (hpC : F[p] ∉ C) (hp1C : F[p + 1] ∈ C) (hqC : F[q] ∉ C) :
    ∃ (r : ℕ) (_ : p + 1 < r) (_ : r < q), r.bodd = b ∧
    C = (fun x : Fin F.length ↦ F[x.1]) '' Fin.val ⁻¹'
      ({p + 1, r} ∪ (Icc (p + 1) r ∩ Nat.bodd ⁻¹' {!b})) := by
  by_cases! hr : ¬ (∀ r (hr : r < q), p + 1 < r → r.bodd = !p.bodd → F[r] ∉ C)
  · push Not at hr
    obtain ⟨r, hrq, hpr, hrb, hrC⟩ := hr
    exact ⟨r, hpr, by lia, (by simpa [hrb] using hpb),
      hF.eq_interval_of_notMem_mem_mem hpr (by lia) hpb (by simpa [hrb] using hpb) hC hpC hp1C hrC⟩
  refine False.elim <| hqC ?_
  clear hqC
  obtain ⟨d, rfl⟩ := exists_add_of_le (show p + 2 ≤ q by lia)
  induction d using Nat.twoStepInduction with
  | zero =>
    rwa [← (hF.isTriad_getElem_of_eq p (by simpa using hqb)).mem_iff_mem_of_isCircuit hC hpC]
  | one => simp [hpb] at hqb
  | more d ih =>
    simp_rw [← add_assoc]
    obtain hd : d.bodd = false := by cases b with simpa [hpb] using hqb
    specialize ih (by lia) (by lia) (by simpa [hd]) hpC hp1C <| by grind
    rwa [← (hF.isTriad_getElem_of_eq (p + 2 + d) (by simpa [hd])).swap_left.mem_iff_mem_of_isCircuit
      hC <| hr _ (by lia) (by lia) <| by simp [hd]]

/-- If a circuit doesn't contain two particular cojoints `F[s], F[t]` of a fan `F`,
but it contains something between them, then it is an interval. -/
lemma IsFan.exists_eq_interval_of_notMem_mem_notMem {s t r : ℕ} (hF : M.IsFan F b c) (hsr : s < r)
    (hrt : r < t) (ht : t < F.length) (hsb : s.bodd = !b) (htb : t.bodd = !b)
    (hC : M.IsCircuit C) (hsC : F[s] ∉ C) (hrC : F[r] ∈ C) (htC : F[t] ∉ C) :
    ∃ (p q : ℕ) (_ : s < p) (_ : p < q) (_ : q < t), p.bodd = b ∧ q.bodd = b ∧
    C = (fun x : Fin F.length ↦ F[x.1]) '' Fin.val ⁻¹' ({p, q} ∪ (Icc p q ∩ Nat.bodd ⁻¹' {!b})) := by
  induction h : r - s using Nat.strong_induction_on generalizing r s with | h d ih =>
  by_cases hs1 : F[s + 1] ∈ C
  · obtain ⟨j, hsj, hjt, rfl, rfl⟩ :=
      hF.exists_eq_interval_of_notMem_mem_add_one (by lia) ht hsb htb hC hsC hs1 htC
    exact ⟨s + 1, j, by simp [hsb, hsj, hjt]⟩
  have hs1i : s + 1 < r := by grind
  rw [(hF.isTriad_getElem_of_eq s hsb).mem_iff_mem_of_isCircuit hC hsC] at hs1
  obtain ⟨p, q, hpq⟩ := ih (r - (s + 2)) (by lia) (by grind) hrt (by simpa) hs1 hrC rfl
  exact ⟨p, q, by grind⟩

/-- If the set of joints of a circuit `C` is contained in `F[p]`, and `C` contains the cojoint
`F[p + 1]`, then `C` contains all subsequent cojoints. -/
lemma IsFan.cojoint_mem_of_subsingleton_joint_mem_le (hF : M.IsFan F b c) (hpF : p + 1 < F.length)
    (hpb : p.bodd = b) (hC : M.IsCircuit C)
    (hpC : ∀ i (hi : i < F.length), i.bodd = b → F[i] ∈ C → i = p) (hp1 : F[p + 1] ∈ C)
    (hpq : p < q) (hq : q < F.length) (hqb : q.bodd = !b) : F[q] ∈ C := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hpq
  induction d using Nat.twoStepInduction with
  | zero => simpa
  | one => simp [hpb] at hqb
  | more d ih _ =>
    obtain hdb : d.bodd = false := by cases b with simpa [hpb] using hqb
    obtain h | h := (hF.isTriangle_getElem (p + d + 1) (by lia)).mem_or_mem_of_isCircuit_bDual
      (K := C) (by simpa [hpb, hdb]) (ih (by lia) (by lia) (by simp [hpb, hdb]))
    · simpa [add_assoc] using hpC _ (by lia) (by simp [hpb, hdb]) h
    simpa [add_assoc]

/-- If the set of joints of a circuit `C` is contained in `F[p]`, and `C` contains the cojoint
`F[p + 1]`, then `C` contains all earlier cojoints. -/
lemma IsFan.cojoint_mem_of_subsingleton_joint_mem_ge (hF : M.IsFan F b c) (hpF : p + 1 < F.length)
    (hpb : p.bodd = !b) (hC : M.IsCircuit C)
    (hpC : ∀ i (hi : i < F.length), i.bodd = b → F[i] ∈ C → i = p + 1) (hp1 : F[p] ∈ C)
    (hqp : q ≤ p) (hqb : q.bodd = !b) : F[q] ∈ C := by
  obtain ⟨d, rfl⟩ := exists_add_of_le hqp
  induction d using Nat.twoStepInduction generalizing q with
  | zero => simpa using hp1
  | one => simp [hqb] at hpb
  | more d ih _ =>
    obtain hdb : d.bodd = false := by cases b with simpa [hqb] using hpb
    specialize ih (q := q + 2) (by simpa) (by lia) (by simpa using hpb) (by grind)
      (by simpa [add_right_comm, add_assoc]) (by lia)
    obtain h | h := (hF.isTriangle_getElem q (by lia)).reverse.mem_or_mem_of_isCircuit_bDual
      (K := C) (by simpa [hdb, hqb]) ih
    · simpa using hpC (q + 1) (by lia) (by simpa) h
    assumption

/-- If `F[p]` is the unique joint in a circuit `C`, then `C` contains either all earlier cojoints
or all subsequent cojoints. -/
lemma IsFan.forall_cojoint_mem_le_or_forall_cojoint_mem_le (hF : M.IsFan F b c) (hpF : p < F.length)
    (hpb : p.bodd = b) (hpC : F[p] ∈ C) (hC : M.IsCircuit C)
    (hpC' : ∀ i (hi : i < F.length), i.bodd = b → F[i] ∈ C → i = p) :
    (∀ q (hq : q < p), q.bodd = !b → F[q] ∈ C) ∨
    (∀ q (hq : q < F.length), p < q → q.bodd = !b → F[q] ∈ C) := by
  obtain rfl | p := p
  · simp
  obtain h_eq | hlt := (show p + 2 ≤ F.length by lia).eq_or_lt
  · grind
  have hpb : p.bodd = !b := by simpa using hpb
  obtain h | h := (hF.isTriangle_getElem p (by lia)).swap_left.mem_or_mem_of_isCircuit_bDual
    (by simpa [hpb]) hpC
  · exact .inl fun q hq hqb ↦
      hF.cojoint_mem_of_subsingleton_joint_mem_ge hpF hpb hC hpC' h (by lia) hqb
  exact .inr fun q hq hqF hqb ↦ hF.cojoint_mem_of_subsingleton_joint_mem_le (by lia) (by simpa)
    hC hpC' h hqF hq hqb

/-- Each proper subset of the cojoints is independent. -/
lemma IsFan.indep_of_ssubset_cojoints (hF : M.IsFan F b c) {I : Set α}
    (hI : I ⊂ F.get '' {i | i.1.bodd = !b}) : M.Indep I := by
  by_cases h2 : F.length ≤ 2
  · suffices h1 : {i : Fin F.length | i.1.bodd = !b}.encard ≤ 1 by
      replace hI := Finite.encard_lt_encard (Finite.subset ?_ hI.subset) hI
      · grw [hF.nodup.injective_get.encard_image, h1] at hI
        simp [show I = ∅ by simpa using hI]
      exact (finite_range _).subset <| image_subset_range ..
    have hcon := (Fin.encard_setOf_bodd F.length !b).le
    grw [h2, Bool.toNat_le] at hcon
    enat_to_nat!; lia
  have hss : F.get '' {i | i.1.bodd = !b} ⊆ {e | e ∈ F} := by grind
  rw [indep_iff_forall_subset_not_isCircuit (hI.subset.trans (hss.trans hF.subset_ground))]
  refine fun C hCI hC ↦ ?_
  replace hCI := hCI.trans_ssubset hI
  clear! hI
  refine hCI.not_subset ?_
  simp only [get_eq_getElem, image_subset_iff]
  have hCb : ∀ {i} {hi : i < F.length}, F[i] ∈ C → i.bodd = !b := by
    intro i hi hiC
    lift i to Fin F.length using hi
    have hwin := hCI.subset hiC
    rwa [← get_eq_getElem, hF.nodup.injective_get.mem_set_image] at hwin
  simp only [get_eq_getElem, image_subset_iff] at hss
  by_cases! hi : ∃ (i : ℕ) (hi : i + 2 < F.length), F[i + 1] ∈ C
  · obtain ⟨i, hi, hiC⟩ := hi
    have hib : i.bodd = b := by simpa using hCb hiC
    refine fun ⟨q, hq⟩ hqb ↦ ?_
    obtain hiq | hiq := le_or_gt (i + 1) q
    · exact hF.cojoint_mem_of_subsingleton_joint_mem_le (by lia) (by simpa) hC (by grind) hiC
        (by lia) (by lia) hqb
    exact hF.cojoint_mem_of_subsingleton_joint_mem_ge hi (by simpa) hC (by grind) hiC hiq.le hqb
  obtain hss | hnt := C.subsingleton_or_nontrivial
  · obtain ⟨e, heC⟩ := hC.nonempty
    obtain ⟨i, hiF, hib, rfl⟩ := hCI.subset heC
    obtain rfl := hss.eq_singleton_of_mem (x := F[i]) heC
    exact False.elim <| (hF.isNonloop_getElem i (by simp) (by simp [h2])).not_isLoop
      (by simpa using hC)
  obtain ⟨f, hfC, hfne⟩ := hnt.exists_ne (F[F.length - 1])
  obtain ⟨⟨j, hj⟩, hjF, hjb, rfl⟩ := hCI.subset hfC
  obtain hne | rfl := ne_or_eq j 0
  · obtain rfl | j := j <;> grind
  obtain rfl : b = true := by simpa using hCb hfC
  obtain ⟨e, heC, he0⟩ := hnt.exists_ne F[0]
  obtain ⟨rfl | rfl | i, hiF, hib, rfl⟩ := hCI.subset heC
  · simp at he0
  · simpa using hCb heC
  obtain h | h :=
    (hF.isTriangle_getElem 0 (by grind)).mem_or_mem_of_isCircuit_bDual (by simpa) hfC
  · simpa using hCb h
  obtain h2 | h3 := (show 3 ≤ F.length by lia).eq_or_lt
  · grind
  exact False.elim <| hi _ h3 h

/-- A parallel pair in a fan is hard to find; it must either comprise both ends, or two consecutive
elements at one of the ends. The upper bound of 6 is best-possible,
since the `5`-fan `[0, 1, 2, 3, 4]` can have the pairs `[0, 2]` and `[1, 3]` both parallel. -/
lemma IsFan.eq_eq_of_parallel (h : M.IsFan F b c) (hF : 6 ≤ F.length) {hi : i < F.length}
    {hj : j < F.length} (hij : i < j) (hC : M.Parallel F[i] F[j]) :
    (b = true ∧ i = 0 ∧ j = 1) ∨ (c = true ∧ i + 2 = F.length ∧ j + 1 = F.length) ∨
    b = false ∧ c = false ∧ i = 0 ∧ j + 1 = F.length := by
  have aux (a : ℕ) (ha : a + 2 < F.length) (hab : a.bodd = b) :
    (i = a ∨ i = a + 1) → ¬ (j = a + 1 ∨ j = a + 2) := by
    have := (h.isTriangle_getElem_of_eq a (by simpa)).notMem_of_mem_of_parallel hC
    grind [h.nodup.getElem_inj_iff]
  have aux' (a : ℕ) (ha : a + 2 < F.length) (hab : a.bodd = !b) :
      ((i = a ∨ i = a + 1 ∨ i = a + 2) ↔ (j = a ∨ j = a + 1 ∨ j = a + 2)) := by
    have hwin := (h.isTriad_getElem_of_eq a hab).isCocircuit.mem_iff_mem_of_parallel hC
    simpa [h.nodup.getElem_inj_iff] using hwin
  obtain ⟨rfl | rfl | d, rfl⟩ := Nat.exists_eq_add_of_lt hij
  · obtain rfl | i := i
    · simp [show b = true by grind]
    obtain hib | hib := i.bodd.eq_or_eq_not b
    · simpa using aux i (by lia) hib
    by_cases hle : i + 3 < F.length
    · simpa using aux (i + 1) (by lia) (by simpa)
    simp [h.bool_right_eq, (show F.length = i + 3 by lia), hib]
  · obtain hib | hib := i.bodd.eq_or_eq_not b
    · simpa using aux i (by lia) hib
    by_cases! h2i : i < 2
    · simpa [add_assoc] using aux' (i + 2) (by lia) (by simpa)
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le' h2i
    simpa [add_assoc] using aux' i (by lia) (by simpa using hib)
  obtain rfl | i := i
  · obtain rfl | rfl := b
    · cases hdb : d.bodd
      · simpa [add_assoc] using aux' (d + 1) (by lia) (by simpa)
      obtain h_eq | hne := eq_or_ne (d + 4) F.length
      · simpa [← h_eq, h.bool_right_eq]
      simpa [add_assoc] using aux' (d + 2) (by lia) (by simpa)
    simpa [add_assoc] using aux' 0 (by lia) (by simp)
  exfalso
  simp only [add_assoc, add_comm 1, Nat.reduceAdd] at hC
  obtain hib | hib := i.bodd.eq_or_eq_not b
  · simpa [add_assoc, show 1 + (d + 3) ≠ 2 by lia, show 1 + (d + 3) ≠ 3 by lia]
      using aux' (i + 1) (by lia) (by simpa)
  simpa [add_assoc, show 1 + (d + 3) ≠ 2 by lia] using aux' i (by lia) (by simpa)

@[grind .]
lemma IsFan.length_ge_four_of_eq_ground [M.Simple] [M✶.Simple] (hF : M.IsFan F b c)
    (hFE : {e | e ∈ F} = M.E) (hFn : F ≠ []) : 4 ≤ F.length := by
  have hne : M.Nonempty := by simpa [← ground_nonempty_iff, ← hFE]
  have hF2 : 2 ≤ F.length := by
    grw [← ENat.natCast_le_natCast, ← hF.nodup.encard_toSet_eq, hFE, ← eRank_add_eRank_dual,
      ← one_le_eRank, ← one_le_eRank, one_add_one_eq_two, Nat.cast_ofNat]
  have hr := M.eRk_pair_eq (e := F[0]) (f := F[1]) (by simp [hF.nodup.getElem_inj_iff])
    (hF.getElem_mem_ground (i := 0)) (hF.getElem_mem_ground (i := 1))
  have hr1 := M✶.eRk_pair_eq (e := F[0]) (f := F[1]) (by simp [hF.nodup.getElem_inj_iff])
    (hF.getElem_mem_ground (i := 0)) (hF.getElem_mem_ground (i := 1))
  have hle := encard_le_encard hFE.symm.subset
  grw [← eRank_add_eRank_dual, F.encard_toSet_le, ← M.eRk_le_eRank {F[0], F[1]},
    ← M✶.eRk_le_eRank {F[0], F[1]}, hr, hr1] at hle
  enat_to_nat!; lia

/-- If `F` is a fan whose ends are joints, and `C` is a circuit containing the first but not
the second element of `F`, then `M` has a circuit containing the first element of `F`,
and no other elements of `F` except possibly the last.  -/
lemma IsFan.exists_isCircuit_subset_first_last (hF : M.IsFan F false false) (h2 : 2 ≤ F.length)
    (hC : M.IsCircuit C) (h0C : F[0] ∈ C) (h1C : F[1] ∉ C) :
    ∃ C₀ ⊆ insert F[F.length - 1] C, M.IsCircuit C₀ ∧ F[0] ∈ C₀ := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le h2
  suffices aux : ∀ k ≤ n, ∃ C₀, M.IsCircuit C₀ ∧ F[0] ∈ C₀ ∧ C₀ ⊆ C ∪ {e | e ∈ F} ∧
      ∀ i (hi : i + 1 < F.length), F[i + 1] ∈ C₀ → k ≤ i by
    refine Exists.imp ?_ <| aux n rfl.le
    simp only [and_imp]
    refine fun C₀ hC₀ h0C₀ hC₀ss h ↦ ⟨?_, hC₀, h0C₀⟩
    refine fun e heC₀ ↦ ?_
    by_cases heC : e ∈ C
    · exact .inr heC
    obtain ⟨rfl | i, hi, rfl⟩ := getElem_of_mem (show e ∈ F by grind)
    · grind
    obtain rfl : n = i := by grind
    simp [hn, add_comm]
  rintro (rfl | k) hk
  · use C; grind
  induction k with
  | zero => use C; grind
  | succ k ih =>
    obtain ⟨C₀', hC₀', h0C₀', hC₀'ss, hClt⟩ := ih (by lia)
    obtain hkC | hkC := em' (F[k + 2] ∈ C₀')
    · exact ⟨C₀', by grind⟩
    cases hb : !k.bodd
    · have hT' := (hF.isTriad_getElem_of_eq k (by simpa using hb)).reverse
      obtain h1 | h2 := hT'.mem_or_mem_of_isCocircuit (K := C₀') (by simpa) hkC
      · grind [hClt _ _ h1]
      obtain rfl | k := k
      · grind
      grind [hClt _ _ h2]
    obtain rfl | hlt := hk.eq_or_lt
    · simpa [hn, ← hb] using hF.length_bodd_eq
    have hT := hF.isTriangle_getElem_of_eq (k + 2) (by simpa using hb)
    have elim := hC₀'.strong_elimination hT.isCircuit (e := F[k + 2]) (f := F[0]) hkC (by simp)
      h0C₀' (by simp [hF.nodup.getElem_inj_iff])
    obtain ⟨C₀, hC₀ss, hC₀, h0C₀⟩ := elim
    refine ⟨C₀, hC₀, h0C₀, ?_, fun i hi hiC₀ ↦ by grind [hF.nodup.getElem_inj_iff]⟩
    grw [hC₀ss, hC₀'ss, sdiff_subset]
    grind [Set.union_subset_iff, insert_subset_iff]

/-- For any fan `F = [a, b, ..., z]` whose ends are joints and for which `{a, b}` isn't series,
there is a circuit `C` with `a ∈ C ∩ F ⊆ {a, z}`. -/
lemma IsFan.exists_isCircuit_first_mem_of_length_odd (hF : M.IsFan F false false)
    (h2 : 2 ≤ F.length) (h01 : ¬ M✶.Parallel F[0] (F[1])) :
    ∃ C, M.IsCircuit C ∧ F[0] ∈ C ∧ ∀ i (hi : i + 1 < F.length),
      F[i + 1] ∈ C → i + 2 = F.length := by
  replace h2 := h2.lt_of_ne (fun h ↦ by simpa [h.symm] using hF.length_bodd_eq)
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le h2.le
  suffices aux : ∀ k ≤ n, ∃ C, M.IsCircuit C ∧ F[0] ∈ C ∧
      ∀ i (hi : i + 1 < F.length), F[i + 1] ∈ C → k ≤ i from
    Exists.imp (by grind) <| aux n rfl.le

  rw [parallel_dual_iff_forall_circuit (hF.dual.isNonloop_getElem 0 (by lia) (by lia))
    hF.getElem_mem_ground] at h01
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
    have hnk : n ≠ k + 2 := fun hnk ↦ by simpa [hn, hnk, hb] using hF.length_bodd_eq
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
      F.length.bodd = false ∧ M.IsTriangle {F[n], F[n + 1]'(by grind), F[0]} := by
  obtain rfl | rfl | n := n
  · grind [hF.length_ge_four_of_eq_ground hFE (by grind)]
  · grind [hF.length_ge_four_of_eq_ground hFE (by grind)]
  have hnp : ¬M✶.Parallel F[0] F[1] := by
    rw [hM'.parallel_iff_eq (hF.dual.subset_ground (getElem_mem ..))]
    simp [hF.nodup.getElem_inj_iff]
  set m := n + 2 + (n.bodd).toNat with hm
  -- set m := if Odd n then n + 3 else n + 2 with hm
  have hmlt : m < F.length := by grind
  -- Take away the last element if the fan is even, then find a circuit containing `F[0]`
  -- that intersects the fan in only possibly the last element.
  have hF' := (hF.take (show 2 ≤ m + 1 by grind) (by lia))
  nth_rw 2 [hm] at hF'
  simp only [Nat.bodd_succ, Nat.bodd_add, Bool.not_not, Bool.toNat_bodd, bne_self_eq_false,
    Bool.not_false, beq_true] at hF'
  obtain ⟨C, hC, h0C, hlt⟩ := hF'.exists_isCircuit_first_mem_of_length_odd (by grind) (by simpa)
  simp_rw [length_take_of_le (show m + 1 ≤ F.length by lia), getElem_take] at hlt
  have hss : C ⊆ {F[m], F[n + 3], F[0]} := by
    intro e he
    obtain ⟨rfl | i, hi, rfl⟩ := getElem_of_mem <| hC.subset_ground.trans hFE.symm.subset he
    · simp
    obtain hlt | hle := lt_or_ge i m
    all_goals grind
  have hCT : M.IsTriangle {F[m], F[n + 3], F[0]} := isTriangle_of_dep_of_encard_le
    (hC.dep.superset hss (by grind)) (encard_triple_le ..)
  rw! [add_assoc, add_assoc, show 1 + 1 + 1 = 3 from rfl, one_add_one_eq_two]
  cases hn : n.bodd
  · exact ⟨by simp [h3, hn], by simpa [hm, hn] using hCT⟩
  simpa [hm, hn] using hCT.ne₁₂

lemma IsFan.isTriangle_bDual_of_simple (hF : M.IsFan F b c) {n : ℕ} (h3 : F.length = n + 2)
    (hM : M.Simple) (hM' : M✶.Simple) (hFE : {e | e ∈ F} = M.E) : F.length.bodd = false ∧
      (M.bDual b).IsTriangle {F[n], F[n + 1]'(by grind), F[0]} := by
  simpa using IsFan.isTriangle_of_simple (M := M.bDual (b)) (F := F) (c := c != b) (by simpa) h3
    (by cases b with simpa) (by cases b with simpa) (by simpa)

lemma IsFan.eConn_le_two (h : M.IsFan F b c) : M.eConn {e | e ∈ F} ≤ 2 := by
  grw [← ENat.add_le_add_iff_right (k := F.length) (by simp), ← h.nodup.encard_toSet_eq,
    ← eRk_add_eRk_dual_eq _ _ h.subset_ground,
    ← ENat.mul_le_mul_left_iff (a := 2) (by simp) (by simp), mul_add, h.eRk_le,
    h.dual.eRk_le, h.nodup.encard_toSet_eq]
  cases b with cases c with (simp; enat_to_nat!; lia)

/-- If the head is spanned by the tail in the appropriate dual of `b`, then the fan
has connectivity one. -/
lemma IsFan.eConn_le_one_of_mem_closure (h : M.IsFan F b c)
    (hcl :  ∀ (h0 : F ≠ []), F[0] ∈ (M.bDual (!b)).closure {x | x ∈ F.tail}) :
    M.eConn {e | e ∈ F} ≤ 1 := by
  cases h with
  | nil b => simp
  | cons' b c e F hF he heF hT =>
  match F with
  | [] => grw [eConn_le_encard]; simp
  | [f] => grw [← eConn_bDual M b, eConn_le_eRk, show {x | x ∈ [e, f]} = {e, f} by grind,
      eRk_insert_of_mem_closure (by simpa using hcl), eRk_singleton_le]
  | f :: g :: F =>
  have hcl' : e ∈ (M.bDual (!b)).closure {z | z ∈ f :: g :: F} :=
    mem_of_mem_of_subset (hT (by simp)).mem_closure₁ <| closure_subset_closure _ <| by grind
  simp only [mem_cons (b := e), ofPred_or, ofPred_eq_eq_singleton, singleton_union]
  grw [← eConn_bDual _ b, ← ENat.add_one_le_add_one_iff, eConn_insert_add_one_eq
    (by grind) (by simpa using hcl') (by grind), (hF.bDual _).eConn_le_two, one_add_one_eq_two]

/-- TODO : I think this should hold even if the fan has odd length. -/
lemma IsFan.eConn_eq_zero_of_mem_closure_mem_closure (h : M.IsFan F b (!b)) (hnil : F ≠ [])
    (hcl : F[0] ∈ (M.bDual (!b)).closure {x | x ∈ F.tail})
    (hcl' : F[F.length - 1] ∈ (M.bDual b).closure {x | x ∈ F.dropLast}) :
    M.eConn {e | e ∈ F} = 0 := by
  wlog hb : b = false generalizing F b with aux
  · obtain rfl : b = true := by simpa using hb
    simpa using aux (F := F.reverse) (b := false) (by simpa using h.reverse) (by simpa)
      (by simpa using hcl') (by simpa using hcl) rfl
  subst hb
  have hr := (M.eRk_add_eRk_dual_eq {e | e ∈ F} h.subset_ground).ge
  replace hcl' := eRk_insert_of_mem_closure hcl'
  rw [← toSet_concat_eq, ← getLast_eq_getElem hnil, dropLast_concat_getLast, bDual_false]
    at hcl'
  replace hcl := eRk_insert_of_mem_closure hcl
  rw [← toSet_cons_eq, getElem_zero, cons_head_tail, Bool.not_false, bDual_true] at hcl
  grw [← ENat.mul_le_mul_left_iff (a := 2) (by simp) (by simp), mul_add, mul_add, hcl, hcl',
    h.nodup.encard_toSet_eq] at hr
  obtain h2 | h3 := le_or_gt F.length 2
  · grw [eRk_le_encard, eRk_le_encard, encard_toSet_le, encard_toSet_le] at hr
    simp only [length_dropLast, ENat.natCast_sub, Nat.cast_one, length_tail] at hr
    enat_to_nat! <;> lia
  grw [(h.tail hnil).dual.eRk_le, (h.dropLast (by lia)).eRk_le] at hr
  simp only [length_dropLast, ENat.natCast_sub, Nat.cast_one, Bool.toNat_false,
    Bool.not_false, Bool.not_true, length_tail] at hr
  enat_to_nat! <;> lia
