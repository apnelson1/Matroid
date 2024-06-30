
import Mathlib.Data.Matroid.Basic
import Mathlib.Data.Fintype.Basic
import Matroid.Rank

open Set Function Classical

variable {α β : Type*}

def matching (G : α → β → Prop) (I :Set α) (J : Set β) (f : β → α) :=
  BijOn f J I ∧ (∀ v ∈ J, G (f v) v)


lemma finite_of_finite_univ [Fintype α] (I :Set α) : I.Finite :=
  Finite.subset finite_univ (subset_univ I)

lemma ncard_eq_of_matching [Fintype α] [Fintype β] {G : α → β → Prop} {I :Set α} {J : Set β}
  {f : β → α} (h : matching G I J f) : I.ncard = J.ncard :=
    (BijOn.image_eq h.1) ▸
    (ncard_image_iff <| finite_of_finite_univ J).mpr (BijOn.injOn h.1)



lemma invFunOn_subset_mem {A : Set β} {B : Set β} {f : β → α} {e : α} (hB : BijOn f B  (f '' B))
  (hs : A ⊆ B) (he : e ∈ f '' A) [Nonempty β]: invFunOn f B e ∈ A := by
  have : invFunOn f B e = invFunOn f A e := by
    have : f (invFunOn f B e) = f (invFunOn f A e) := by
      rw [invFunOn_eq (BijOn.surjOn hB ((monotone_image hs) he))]
      rw [invFunOn_eq (surjOn_image f A he)]
    apply BijOn.injOn hB (invFunOn_mem (BijOn.surjOn hB ((monotone_image hs) he)))
      (hs (invFunOn_mem (surjOn_image f A he))) this
  rw [this]
  apply invFunOn_mem (surjOn_image f A he)

lemma invFunOn_subset_image_subset {A : Set β} {B : Set β} {f : β → α} (hB : BijOn f B  (f '' B))
   (hs : A ⊆ B) [Nonempty β]: invFunOn f B '' (f '' A) ⊆ A := by
  refine fun e he ↦ ?_
  obtain ⟨a, ha, ha'⟩ := he
  rw [← ha']
  apply invFunOn_subset_mem hB hs ha

lemma not_in_singleton {a : α} {b : α} : a ∉ ({b} : Set α) → a ≠ b := by
  refine fun h ↦ ?_
  contrapose! h
  exact mem_singleton_of_eq h


lemma bijOn_insert {f : β → α} {s : Set β} {t : Set α} {x : β} {y : α} (h : BijOn f s t)
  (hx : x ∉ s) :
  BijOn f (insert x s) (insert y t) ↔ f x = y ∧ y ∉ t := by
    refine iff_def.mpr ⟨fun hb ↦ ?_ , fun ⟨hx', hy⟩ ↦ ⟨?_, ?_, ?_⟩⟩
    have h' : y ∉ t := by
      contrapose! hx
      rw [insert_eq_self.mpr hx] at hb
      obtain d := (InjOn.image_eq_image_iff (BijOn.injOn hb) (subset_insert x s) subset_rfl).mp
      rw [BijOn.image_eq h, BijOn.image_eq hb] at d
      exact insert_eq_self.mp (Eq.symm (d rfl))
    · refine ⟨((insert_inj h').mp (BijOn.image_eq h▸ image_insert_eq▸ BijOn.image_eq hb).symm).symm
        , h'⟩
    · rw [mapsTo', image_insert_eq, hx', BijOn.image_eq h]
    · exact (injOn_insert hx).mpr ⟨BijOn.injOn h, (BijOn.image_eq h) ▸ hx' ▸ hy⟩
    · rw [SurjOn, image_insert_eq, hx', BijOn.image_eq h]

lemma bijOn_reassign {f : β → α} {s : Set β} {t : Set α} {x : β} {y : α} (h : BijOn f s t)
  (hx : x ∈ s) (hy : y ∉ t) : ∃ g, g x = y ∧ BijOn g s (insert y (t \ {f x})) ∧ EqOn f g (s \ {x})
  := by
  set g := fun (a : β) ↦ if a = x then y else f a with hg
  have heq : EqOn f g (s \ {x}) := by
    rw [hg, EqOn]
    refine fun a ⟨_, ha'⟩ ↦ ?_
    simp only [mem_singleton_iff] at ha'
    simp only [ha', ↓reduceIte]
  have hf : f '' (s \ {x}) = (t \ {f x}) := (BijOn.image_eq h) ▸ image_singleton ▸
    InjOn.image_diff_subset (BijOn.injOn h) (singleton_subset_iff.mpr hx)
  have hxy : g x = y := by
    simp only [hg, ↓reduceIte]
  have hy' : y ∉ (t \ {f x}) := by
    contrapose! hy
    exact mem_of_mem_diff hy
  refine ⟨g, hxy, (insert_eq_of_mem hx) ▸ insert_diff_singleton ▸ (bijOn_insert
    ((EqOn.bijOn_iff heq).mp (hf ▸ (BijOn.subset_left h diff_subset)))
    (not_mem_diff_of_mem <| mem_singleton x)).mpr ⟨hxy, hy'⟩, heq⟩


lemma bijOn_reassign_with_matching {G :  α → β → Prop} {f : β → α} {s : Set β} {t : Set α} {x : β}
  {y : α} (h : matching G t s f) (hx : x ∈ s) (hy : y ∉ t) (hG : G y x) :
    ∃ g, g x = y ∧ matching G (insert y (t \ {f x})) s g ∧ EqOn f g (s \ {x}):= by
    obtain ⟨g, hxy, hbij, heq⟩ := bijOn_reassign h.1 hx hy
    refine ⟨g, hxy, ⟨hbij, fun v hv ↦ ?_⟩, heq⟩
    by_cases hv' : v = x
    · exact hv' ▸ hxy ▸ hG
    · exact (heq ((mem_diff v).mpr ⟨hv, hv'⟩)) ▸ h.2 v hv

lemma Finset.pair_eq_union {a b : α} : ({a, b} : Finset α) = ({a} : Finset α) ∪ ({b} : Finset α)
  := by apply Eq.refl

lemma Finset.subset_pair_left {a b : α} : ({a} : Finset α) ⊆ ({a, b} : Finset α) := by
  simp_all only [Finset.singleton_subset_iff, Finset.mem_insert, Finset.mem_singleton, true_or]

lemma Finset.subset_pair_right {a b : α} : ({b} : Finset α) ⊆ ({a, b} : Finset α) :=
  Finset.pair_comm a b ▸ Finset.subset_pair_left

lemma Finset.pair_diff_left {a b : α} (hne : a ≠ b) :
  ({a, b} : Finset α) \ ({a} : Finset α) = ({b} : Finset α) := by
  ext1 x
  simp_all only [mem_sdiff, mem_insert, mem_singleton]
  refine ⟨fun ⟨h, h'⟩ ↦ (false_or_iff (x = b)).mp ((eq_false h') ▸ h),
     fun h ↦ ⟨Or.inr h, ne_eq x a ▸ h ▸ (Ne.symm hne)⟩⟩

lemma Finset.pair_diff_right {a b : α} (hne : a ≠ b) :
  ({a, b} : Finset α) \ ({b} : Finset α) = ({a} : Finset α) :=
  Finset.pair_comm a b ▸ Finset.pair_diff_left (Ne.symm hne)

lemma Finset.insert_sdiff_self_of_not_mem {a : α} {s : Finset α} (h : a ∉ s) :
  insert a s \ {a} = s := by
  ext1 x
  simp_all only [mem_sdiff, mem_insert, mem_singleton]
  refine ⟨fun ⟨h, h'⟩ ↦ (false_or_iff _).mp ((eq_false h') ▸ h),
     fun hx ↦ ⟨Or.inr hx, ne_eq x a ▸ ?_⟩⟩
  contrapose! h
  exact h ▸ hx

lemma Nat.le_sSup {s : Set ℕ} {m : ℕ} (h : BddAbove s) (hm : m ∈ s) : m ≤ sSup s := by
  obtain ⟨n, hn⟩ := h
  set s' := {n - a | a ∈ s}
  sorry





-- lemma clstuff (M : Matroid α) {I J : Set α} {e : α} (hI : M.Indep I) (hIJ : J ⊆ I) (he : e ∈ I \ J):
--   e ∉ M.cl J := by
--   have: insert e J ⊆ I := insert_subset ((mem_diff e).mp he).left hIJ
--   have: M.Indep (insert e J) := Matroid.Indep.subset hI this
--   rw [← Set.insert_diff_self_of_not_mem he.right]
--   apply (M.indep_iff_not_mem_cl_diff_forall (Matroid.Indep.subset_ground this)).mp this
--   simp [mem_insert_iff, true_or] Finite.exists_encard_eq_coe


def Matroid_from_bipartite [Fintype α] [Fintype β] [Nonempty β] [Nonempty α] (MA: Matroid α)
  (G : α → β → Prop) : IndepMatroid β := by
  set Bmatch := fun (I : Set α) (J : Set β) (f : β → α) ↦ matching G I J f with hBM
  set BIndep := fun (J : Set β) ↦ ∃ I : Set α , ∃ f : β → α,
    MA.Indep I ∧ Bmatch I J f with hBI

  have exist_max_overlapping_matching {I J : Set β} (hI : BIndep I) (hJ : BIndep J): ∃ f g IA JA,
    matching G IA I f ∧ MA.Indep IA ∧ matching G JA J g ∧ MA.Indep JA ∧
    ∀ f' g' IA' JA', matching G IA' I f' ∧ MA.Indep IA' ∧ matching G JA' J g' ∧ MA.Indep JA' →
    {x ∈ I ∩ J | f' x = g' x}.ncard ≤ {x ∈ I ∩ J | f x = g x}.ncard := by
    set s := {n | ∃ f g IA JA, matching G IA I f ∧ MA.Indep IA ∧ matching G JA J g ∧ MA.Indep JA
    ∧ {x ∈ I ∩ J | f x = g x}.ncard = n}
    obtain ⟨IA, f, hIAI, hIAM⟩ := hI
    obtain ⟨JA, g, hJAI, hJAM⟩ := hJ
    have hnem : s.Nonempty := by
      refine ⟨{x ∈ I ∩ J | f x = g x}.ncard,
        mem_setOf_eq ▸ ⟨f, g, IA, JA, hIAM, hIAI, hJAM, hJAI, rfl⟩⟩
    have hbd : BddAbove s := by
      refine bddAbove_def.mpr ⟨(I ∩ J).ncard, fun x hx ↦ ?_⟩
      obtain ⟨_, _, _, _, _, _, _, _, _, h⟩ := mem_setOf_eq ▸ hx
      refine ncard_mono (fun x hx ↦ (mem_setOf_eq ▸ hx).1)
    obtain ⟨f, g, IA, JA, hIAM, hIAI, hJAM, hJAI, h⟩ := Nat.sSup_mem hnem hbd
    refine ⟨f, g, IA, JA, hIAM, hIAI, hJAM, hJAI,
      fun f' g' IA' JA' ⟨hIA'M, hIA'I, hJA'M, hJA'I⟩ ↦ h ▸ ?_⟩
    have hin : {x | x ∈ I ∩ J ∧ f' x = g' x}.ncard ∈ s := by
      refine mem_setOf.mpr ⟨f', g', IA', JA', hIA'M, hIA'I, hJA'M, hJA'I, rfl⟩
    exact Nat.le_sSup hbd hin

  have h_indep_empty : BIndep ∅ := by
    rw [hBI, hBM]
    simp only [exists_and_left]
    refine ⟨∅, MA.empty_indep, ?_⟩
    simp_rw [matching]
    simp only [mem_empty_iff_false, false_implies, implies_true, and_true]
    refine ⟨fun _ ↦ Classical.arbitrary α , bijOn_empty_iff_left.mpr rfl⟩

  exact IndepMatroid.ofFinite
    Set.finite_univ
    (Indep := fun I => BIndep I)
    (indep_empty := h_indep_empty)
    (indep_subset := by
      refine fun I J hJ hIJ ↦ ?_
      rw [hBI, hBM]
      rw [hBI, hBM] at hJ
      obtain ⟨JA, f, hJA, hJAM⟩ := hJ
      set IA := f '' I with hIA
      have : IA ⊆ JA := by
        rw [hIA, ← BijOn.image_eq hJAM.left]
        apply image_mono hIJ
      refine ⟨IA, f, Matroid.Indep.subset hJA this,
        ⟨mapsTo_image f I, InjOn.mono hIJ (BijOn.injOn hJAM.left), surjOn_image f I⟩,
        fun v hv ↦  hJAM.right v (hIJ hv)⟩
      )

    (indep_aug := by
      refine fun I J hI hJ hIJ ↦ ?_
      obtain ⟨f, g, IA, JA, hIAM, hIAI, hJAM, hJAI, h⟩ := exist_max_overlapping_matching hI hJ
      have hIJ : IA.encard < JA.encard := by
        rw [← BijOn.image_eq hJAM.left, ← BijOn.image_eq hIAM.left,
          InjOn.encard_image (BijOn.injOn hJAM.left), InjOn.encard_image (BijOn.injOn hIAM.left),
          ← Finite.cast_ncard_eq <| finite_of_finite_univ I,
          ← Finite.cast_ncard_eq <| finite_of_finite_univ J]
        apply Nat.strictMono_cast hIJ
      obtain ⟨eA, heA, heAI⟩ := Matroid.Indep.augment hIAI hJAI hIJ
      obtain hg := (BijOn.image_eq hJAM.1) ▸ (mem_of_mem_diff heA)

      have : invFunOn g J eA ∈ J \ I := by
        contrapose! h
        simp only [mem_diff, not_and, Decidable.not_not] at h
        obtain h := h (Function.invFunOn_mem hg)
        have hG : G eA (invFunOn g J eA) := by
          nth_rw 1 [← (Function.invFunOn_eq hg)]
          exact (hJAM.2 (invFunOn g J eA) (Function.invFunOn_mem hg))
        have hne : eA ≠ f (invFunOn g J eA) := by
          obtain heA := not_mem_of_mem_diff heA
          contrapose! heA
          rw [← BijOn.image_eq hIAM.1, heA]
          exact mem_image_of_mem f h
        obtain ⟨f', hf', hf'M, heq⟩ :=
          bijOn_reassign_with_matching hIAM h (not_mem_of_mem_diff heA) hG
        refine ⟨f', g, (insert eA (IA \ {f (invFunOn g J eA)})), JA, ⟨hf'M, ?_, hJAM, hJAI⟩, ?_⟩
        exact (insert_diff_singleton_comm hne IA) ▸ Matroid.Indep.subset heAI diff_subset
        apply ncard_strictMono
        simp only [lt_eq_ssubset]
        refine ssubset_of_subset_not_subset (fun a ⟨haI, haJ⟩ ↦ ?_)
          (not_subset.mpr ⟨(invFunOn g J eA), ?_, ?_⟩)
        simp only [mem_inter_iff, mem_setOf_eq]
        refine ⟨⟨h, (Function.invFunOn_mem hg)⟩, ?_⟩
        nth_rw 1 [hf', (Function.invFunOn_eq hg)]
        contrapose! hne
        simp only [mem_inter_iff, sep_inter, mem_setOf_eq] at hne
        obtain hne := hne.1.2
        rw [hne, (Function.invFunOn_eq hg)]
        have : a ≠ (invFunOn g J eA) := by
          contrapose! hne
          rw [hne] at haJ
          rw [haJ, (Function.invFunOn_eq hg)]
        simp only [mem_setOf_eq]
        refine ⟨haI, ?_⟩
        exact haJ ▸Eq.symm (heq (mem_diff_of_mem haI.1 this))

      set f' := fun (x : β) ↦ if x = (invFunOn g J eA) then eA else f x with hf'
      refine ⟨invFunOn g J eA, this.1, this.2, ⟨insert eA IA, f', heAI, ?_⟩⟩

      have heq : EqOn f' f I := by
        rw [hf', EqOn]
        refine fun x hx ↦ ?_
        have : x ≠ invFunOn g J eA := by
          obtain this := this.2
          contrapose! this
          exact this ▸ hx
        simp only [this, ↓reduceIte]

      have hf : f' (invFunOn g J eA) = eA := by simp only [hf', ↓reduceIte]

      refine ⟨(bijOn_insert ((EqOn.bijOn_iff heq).mpr hIAM.1) this.2).mpr ⟨hf, heA.2⟩,
        fun v hx ↦ ?_⟩
      obtain h |h := hx
      · rw [h, hf]
        nth_rw 1 [← Function.invFunOn_eq hg]
        exact hJAM.2 (invFunOn g J eA) this.1
      · exact (heq h) ▸ hIAM.2 v h
    )

    (subset_ground := by
      refine fun I _ ↦ Set.subset_univ I
      )



-- def N (G : α → β → Prop) (X : Finset β) := { u | ∃ v ∈ X, G u v}

-- lemma N_union {G : α → β → Prop} {X Y: Finset β} : N G (X ∪ Y) = N G X ∪ N G Y := by
--   simp only [N, Finset.mem_union]
--   refine subset_antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)
--   · simp_all only [mem_setOf_eq, mem_union]
--     obtain ⟨y, ⟨h | h, right⟩⟩ := hx
--     · left
--       refine ⟨y, h, right⟩
--     · right
--       refine ⟨y, h, right⟩
--   · simp_all only [mem_setOf_eq, mem_union]
--     obtain ⟨v, hv, hG⟩ | ⟨v, hv, hG⟩ := hx
--     · refine ⟨v, Or.intro_left (v ∈ Y) hv, hG⟩
--     · refine ⟨v, Or.intro_right (v ∈ X) hv, hG⟩

-- lemma N_mono {G : α → β → Prop} {X Y: Finset β} (h : X ⊆ Y) : N G X ⊆ N G Y := by
--   simp only [N, setOf_subset_setOf, forall_exists_index, and_imp]
--   refine fun a x hx hG ↦ ⟨x, h hx, hG⟩



-- def Matroid_from_bipartite [Fintype α] [Fintype β] [Nonempty β] [Nonempty α] (MA: Matroid α)
--   (G : α → β → Prop) : Matroid β := by

--   set rB := fun (X : Finset β) ↦ sInf {MA.r (N G Y) + (X \ Y).card | Y ⊆ X} with hrB

--   have h_nonempty : ∀ (X : Finset β), {MA.r (N G Y) + (X \ Y).card | Y ⊆ X}.Nonempty := by
--     refine fun X ↦ ⟨X.card, mem_setOf_eq ▸ ⟨∅, Finset.empty_subset X , ?_⟩⟩
--     simp only [N, Finset.not_mem_empty, false_and, exists_const, setOf_false, Matroid.r_empty,
--       Finset.sdiff_empty, zero_add]

--   have h_rank_empty : rB ∅  = 0 := by
--     simp only [Finset.empty_sdiff, Finset.card_empty, add_zero, Nat.sInf_eq_zero, mem_setOf_eq,
--         rB]
--     left
--     refine ⟨∅, subset_rfl, ?_⟩
--     simp only [N, Finset.not_mem_empty, false_and, exists_const, setOf_false, Matroid.r_empty]

--   have h_rank_singleton : ∀ (e : β), rB {e} ≤ 1 := by
--     refine fun e ↦ ?_
--     simp only [Finset.subset_singleton_iff, exists_eq_or_imp, Finset.sdiff_empty,
--       Finset.card_singleton, exists_eq_left, sdiff_self, Finset.bot_eq_empty, Finset.card_empty,
--       add_zero, rB]
--     simp_rw [N]
--     simp only [Finset.not_mem_empty, false_and, exists_const, setOf_false, Matroid.r_empty,
--       zero_add, Finset.mem_singleton, exists_eq_left]
--     apply Nat.sInf_le
--     simp only [mem_setOf_eq, true_or]

--   have rank_zero : ∀ {e : β}, rB {e} = 0 → MA.r (N G {e}) = 0 := by
--     intro e he
--     simp only [rB, Nat.sInf_eq_zero] at he
--     obtain h | h := he
--     · simp only [Finset.subset_singleton_iff, exists_eq_or_imp, Finset.sdiff_empty,
--       Finset.card_singleton, exists_eq_left, sdiff_self, Finset.bot_eq_empty, Finset.card_empty,
--       add_zero, mem_setOf_eq, add_eq_zero, one_ne_zero, and_false, false_or] at h
--       exact h
--     · absurd h
--       push_neg
--       exact h_nonempty {e}

--   have rank_step : ∀ (A : Finset β) (x : β), rB (insert x A) ≤ rB A + 1 := by
--     intro A x
--     by_cases hx : x ∈ A
--     · rw [Finset.insert_eq_self.mpr hx]
--       linarith
--     · obtain ⟨S, hS, hSInf⟩ := mem_setOf_eq ▸ Nat.sInf_mem (h_nonempty A)
--       simp only [hrB, ← hSInf]
--       refine Nat.sInf_le (mem_setOf_eq ▸ ⟨S, subset_trans hS (Finset.subset_insert x A), ?_⟩)
--       rw [add_assoc (MA.r (N G S)) (A \ S).card 1, add_left_cancel_iff,
--         Finset.insert_sdiff_of_not_mem, Finset.card_insert_of_not_mem]
--       contrapose! hx
--       exact (Finset.mem_sdiff.mp hx).left
--       contrapose! hx
--       exact hS hx

--   have rank_mono : ∀ (A : Finset β) (x : β), rB A ≤ rB (insert x A) := by
--     intro A x
--     by_cases hx : x ∈ A
--     · rw [Finset.insert_eq_self.mpr hx]
--     · obtain ⟨S, hS, hSInf⟩ := mem_setOf_eq ▸ Nat.sInf_mem (h_nonempty (insert x A))
--       simp only [hrB, ← hSInf]
--       have: MA.r (N G (S \ {x})) + (A \ (S \ {x})).card ≤ MA.r (N G S) + (insert x A \ S).card := by
--         rw [sdiff_sdiff_right, Finset.inf_eq_inter, Finset.inter_assoc, Finset.sup_eq_union]
--         refine add_le_add (MA.r_mono (N_mono Finset.sdiff_subset)) (Finset.card_mono ?_)
--         by_cases hxS : x ∈ S
--         · rw [Finset.inter_singleton_of_mem hxS, Finset.inter_singleton_of_not_mem hx,
--             Finset.union_empty (A \ S), Finset.insert_sdiff_of_mem A hxS]
--         · rw [Finset.inter_singleton_of_not_mem hxS, Finset.inter_empty, Finset.union_empty,
--             Finset.insert_sdiff_of_not_mem A hxS]
--           exact Finset.subset_insert x (A \ S)

--       refine le_trans  (Nat.sInf_le (mem_setOf_eq ▸ ⟨S \ {x},
--         (Finset.insert_sdiff_self_of_not_mem hx) ▸ Finset.sdiff_subset_sdiff hS subset_rfl, rfl⟩))
--         this




--   exact Matroid.ofFinsetRankAxioms (E := univ) (r := rB)
--     (rank_empty := h_rank_empty)


--     (rank_singleton := h_rank_singleton)

--     (submodularity := by
--       intro A x y

--       have zero : ∀ {x y : β}, rB ∅ + rB (∅ ∪ {x, y}) ≤ rB (insert x ∅) +rB (insert y ∅) := by
--         intro x y
--         simp only [h_rank_empty, zero_add, Finset.empty_sdiff, Finset.card_empty, add_zero,
--           Finset.union_insert, Finset.empty_union, Finset.insert_empty]

--         by_cases hx : rB {x} = 0
--         · rw [hx, zero_add]
--           by_cases hy : rB {y} = 0
--           · rw [hy, hrB]
--             refine Nat.sInf_le (mem_setOf_eq ▸ ⟨{x, y}, subset_rfl,
--               (Finset.sdiff_self {x, y} ▸ Finset.pair_eq_union ▸ N_union ▸ ?_)⟩)
--             rw [Finset.card_empty, add_zero]
--             refine le_antisymm ?_ (Nat.cast_nonneg (MA.r (N G {x} ∪ N G {y})))
--             exact le_of_add_le_of_nonneg_right (rank_zero hy ▸ zero_add (MA.r (N G {y})) ▸
--               rank_zero hx ▸ (MA.r_submod (N G {x}) (N G {y})))
--               (Nat.cast_nonneg (MA.r (N G {x} ∩ N G {y})))
--           · have : rB {y} = 1 := le_antisymm (h_rank_singleton y) (Nat.one_le_iff_ne_zero.mpr hy)
--             rw [this, hrB]
--             have : x ≠ y := by
--               contrapose! this
--               rw [← this, hx]
--               linarith
--             refine Nat.sInf_le (mem_setOf_eq ▸ ⟨{x}, Finset.subset_pair_left,  rank_zero hx ▸ ?_⟩)
--             rw [Finset.pair_diff_left this, zero_add, Finset.card_singleton]

--         · have : rB {x} = 1 := le_antisymm (h_rank_singleton x) (Nat.one_le_iff_ne_zero.mpr hx)
--           rw [this]
--           by_cases hy : rB {y} = 0
--           · rw [hy, hrB, add_zero]
--             have : x ≠ y := by
--               contrapose! this
--               rw [this, hy]
--               linarith
--             refine Nat.sInf_le (mem_setOf_eq ▸ ⟨{y}, Finset.subset_pair_right,  rank_zero hy ▸ ?_⟩)
--             rw [Finset.pair_diff_right this, zero_add, Finset.card_singleton]
--           · have : rB {y} = 1 := le_antisymm (h_rank_singleton y) (Nat.one_le_iff_ne_zero.mpr hy)
--             rw [this, one_add_one_eq_two, hrB]
--             by_cases hxy : x = y
--             · refine le_trans (Nat.sInf_le (mem_setOf_eq ▸ ⟨∅, Finset.empty_subset {x, y}, ?_⟩))
--                 one_le_two
--               simp only [N, Finset.not_mem_empty, false_and, exists_const, setOf_false,
--                 Matroid.r_empty, hxy, Finset.mem_singleton, Finset.insert_eq_of_mem,
--                 Finset.sdiff_empty, Finset.card_singleton, zero_add]
--             · refine Nat.sInf_le (mem_setOf_eq ▸ ⟨∅, Finset.empty_subset {x, y}, ?_⟩)
--               simp only [N, Finset.not_mem_empty, false_and, exists_const, setOf_false,
--                 Matroid.r_empty, Finset.sdiff_empty, zero_add, Finset.card_pair hxy]

--       have h_insert : ∀ ⦃z : β⦄ {A : Finset β}, z ∉ A → (∀ (x y : β),
--         rB A + rB (A ∪ {x, y}) ≤ rB (insert x A) + rB (insert y A)) → (∀ (x y : β),
--         rB (insert z A) + rB ((insert z A) ∪ {x, y}) ≤
--         rB (insert x (insert z A)) + rB (insert y (insert z A))) := by
--         intro z A hzA hsub x y
--         rw [Finset.insert_eq x (insert z A), Finset.insert_eq z, Finset.insert_eq y]






--       sorry

--       )
--     (rank_singleton_of_not_mem_ground := sorry)
