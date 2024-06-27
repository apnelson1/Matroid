import Mathlib.Data.Matroid.Basic
import Mathlib.Data.Fintype.Basic
import Matroid.Rank
import Matroid.Constructions.RankAxioms

open Set Function Classical

variable {α β : Type*}

def matching (G : α → β → Prop) (I :Set α) (J : Set β) (f : β → α) :=
  BijOn f J I ∧ (∀ v ∈ J, G (f v) v)

def N (G : α → β → Prop) (X : Set β) := { u | ∃ v ∈ X, G u v}



def Matroid_from_bipartite [Fintype α] [Fintype β] [Nonempty β] [Nonempty α] (MA: Matroid α)
  (G : α → β → Prop) : IndepMatroid β := by

  set rB := fun (X : Set β) ↦ sInf {MA.r (N G Y) + (X \ Y).ncard | Y ⊆ X}


  exact IndepMatroid.ofFiniteRankAxioms (E := univ) (r := rB)
    (rank_le_encard := by
      intro X
      simp only [← Finite.cast_ncard_eq (Finite.subset finite_univ (subset_univ X)), Nat.cast_le,
        rB]
      have : X.ncard ∈ {x | ∃ Y ⊆ X, MA.r (N G Y) + (X \ Y).ncard = x} := by
        simp only [mem_setOf_eq]
        refine ⟨∅, empty_subset X, ?_⟩
        simp only [N, mem_empty_iff_false, false_and, exists_const, setOf_false, Matroid.r_empty,
          diff_empty, zero_add]

      have h : {x | ∃ Y ⊆ X, MA.r (N G Y) + (X \ Y).ncard = x}.Nonempty := ⟨X.ncard, this⟩
      simp only [Nat.sInf_def h]

      exact Nat.find_min' ⟨X.ncard, this⟩ this
      )
    (monotonicity := sorry)
    (submodularity := sorry) (rank_inter_ground := sorry)

-- import Mathlib.Data.Matroid.Basic
-- import Mathlib.Data.Fintype.Basic
-- import Matroid.Rank

-- open Set Function Classical

-- variable {α β : Type*}

-- def matching (G : α → β → Prop) (I :Set α) (J : Set β) (f : β → α) :=
--   BijOn f J I ∧ (∀ v ∈ J, G (f v) v)

-- def path (G : α → β → Prop) (I : Set β) (J : Set α) (f : β → α) (g : α → β) (e : β) (init : Set β)
--   [Fintype β] :=
--   if h : e ∉ I ∨ f e ∈ J then {e} ∪ init else path G (I \ {e}) J f g (g (f e)) ({e} ∪ init)
-- termination_by I.ncard
-- decreasing_by
--   push_neg at h
--   simp_wf
--   apply ncard_lt_ncard
--   apply ssubset_of_subset_not_subset diff_subset
--   apply nonempty_diff.mp
--   simp only [sdiff_sdiff_right_self, inf_eq_inter, inter_singleton_nonempty, h]
--   exact Finite.subset finite_univ (subset_univ I)





-- lemma invFunOn_subset_mem {A : Set β} {B : Set β} {f : β → α} {e : α} (hB : BijOn f B  (f '' B))
--   (hs : A ⊆ B) (he : e ∈ f '' A) [Nonempty β]: invFunOn f B e ∈ A := by
--   have : invFunOn f B e = invFunOn f A e := by
--     have : f (invFunOn f B e) = f (invFunOn f A e) := by
--       rw [invFunOn_eq (BijOn.surjOn hB ((monotone_image hs) he))]
--       rw [invFunOn_eq (surjOn_image f A he)]
--     apply BijOn.injOn hB (invFunOn_mem (BijOn.surjOn hB ((monotone_image hs) he))) (hs (invFunOn_mem (surjOn_image f A he))) this
--   rw [this]
--   apply invFunOn_mem (surjOn_image f A he)

-- lemma invFunOn_subset_image_subset {A : Set β} {B : Set β} {f : β → α} (hB : BijOn f B  (f '' B))
--    (hs : A ⊆ B) [Nonempty β]: invFunOn f B '' (f '' A) ⊆ A := by
--   refine fun e he ↦ ?_
--   obtain ⟨a, ha, ha'⟩ := he
--   rw [← ha']
--   apply invFunOn_subset_mem hB hs ha

-- lemma not_in_singleton {a : α} {b : α} : a ∉ ({b} : Set α) → a ≠ b := by
--   refine fun h ↦ ?_
--   contrapose! h
--   exact mem_singleton_of_eq h


-- lemma bijOn_insert {f : β → α} {s : Set β} {t : Set α} {x : β} {y : α} (h : BijOn f s t)
--   (hx : x ∉ s) :
--   BijOn f (insert x s) (insert y t) ↔ f x = y ∧ y ∉ t := by
--     refine iff_def.mpr ⟨fun hb ↦ ?_ , fun ⟨hx', hy⟩ ↦ ⟨?_, ?_, ?_⟩⟩
--     have h' : y ∉ t := by
--       contrapose! hx
--       rw [insert_eq_self.mpr hx] at hb
--       obtain d := (InjOn.image_eq_image_iff (BijOn.injOn hb) (subset_insert x s) subset_rfl).mp
--       rw [BijOn.image_eq h, BijOn.image_eq hb] at d
--       exact insert_eq_self.mp (Eq.symm (d rfl))
--     · refine ⟨((insert_inj h').mp (BijOn.image_eq h▸ image_insert_eq▸ BijOn.image_eq hb).symm).symm
--         , h'⟩
--     · rw [mapsTo', image_insert_eq, hx', BijOn.image_eq h]
--     · exact (injOn_insert hx).mpr ⟨BijOn.injOn h, (BijOn.image_eq h) ▸ hx' ▸ hy⟩
--     · rw [SurjOn, image_insert_eq, hx', BijOn.image_eq h]


-- lemma uhmmm {G : α → β → Prop} {I J : Set β} {IA JA : Set α} {f g : β → α} {eA : α} {e e': β}
--   [Fintype α] [Fintype β] [Nonempty β] [Nonempty α] (hIAM : matching G IA I f)
--   (hJAM : matching G JA J g) (he : g e = eA) (heA : eA ∈ JA \ IA)
--   (hpath : e' ∈ (J \ I) ∩ (path G I (IA \ JA) f (invFunOn g J) e ∅)) :
--     ∃ f', matching G (insert eA IA) (insert e' I) f' := by
--   by_cases h : e ∈ J \ I
--   · set f' := fun (x : β) ↦ if x = e then eA else f x with hf'

--     have heq : EqOn f' f I := by
--       refine fun x hx ↦ ?_
--       have: x ≠ e := by
--         obtain h' := ((mem_diff e).mp h).right
--         contrapose! h'
--         exact h' ▸ hx
--       simp only [hf', this, ↓reduceIte]
--     sorry
--     -- refine ⟨f', (bijOn_insert ((EqOn.bijOn_iff heq).mpr hIAM.left)
--     --   ((mem_diff eA).mp heA).right).mpr ?_, ?_⟩



--   · set p := path G I (IA \ JA) f (invFunOn g J) e ∅ with hp
--     set f' := fun (x : β) ↦ if x ∈ p then g x else f x with hf'

--     have : p ⊆ insert e' (I ∩ J) := by
--       refine fun x hx ↦ ?_
--       simp only [mem_insert_iff, mem_inter_iff]
--       by_cases he' : x = e'
--       · left
--         exact he'
--       · simp [hp] at hx



--     have : Disjoint (f' '' p) (f' '' ((insert e' I) \ p)) := by
--       rw [disjoint_left]
--       intro a ha ha'
--       simp only [hf', mem_image, mem_diff] at ha ha'
--       obtain ⟨x, hx, hx'⟩ := ha
--       obtain ⟨y,  hy, hy'⟩ := ha'
--       simp only [hx, ↓reduceIte] at hx'
--       simp only [hy.right, ↓reduceIte] at hy'
--       sorry

--     have : InjOn f' (insert e' I) := by
--       intro x hx y hy hxy



-- -- lemma clstuff (M : Matroid α) {I J : Set α} {e : α} (hI : M.Indep I) (hIJ : J ⊆ I) (he : e ∈ I \ J):
-- --   e ∉ M.cl J := by
-- --   have: insert e J ⊆ I := insert_subset ((mem_diff e).mp he).left hIJ
-- --   have: M.Indep (insert e J) := Matroid.Indep.subset hI this
-- --   rw [← Set.insert_diff_self_of_not_mem he.right]
-- --   apply (M.indep_iff_not_mem_cl_diff_forall (Matroid.Indep.subset_ground this)).mp this
-- --   simp [mem_insert_iff, true_or]


-- def Matroid_from_bipartite [Fintype α] [Fintype β] [Nonempty β] [Nonempty α] (MA: Matroid α)
--   (G : α → β → Prop) : IndepMatroid β := by
--   set Bmatch := fun (I : Set α) (J : Set β)(f : β → α) ↦ matching G I J f with hBM
--   set BIndep := fun (J : Set β) ↦ ∃ I : Set α , ∃ f : β → α,
--     MA.Indep I ∧ Bmatch I J f with hBI

--   have h_indep_empty : BIndep ∅ := by
--     rw [hBI, hBM]
--     simp only [exists_and_left]
--     refine ⟨∅, MA.empty_indep, ?_⟩
--     simp_rw [matching]
--     simp only [mem_empty_iff_false, false_implies, implies_true, and_true]
--     refine ⟨fun _ ↦ Classical.arbitrary α , bijOn_empty_iff_left.mpr rfl⟩

--   exact IndepMatroid.ofFinite
--     Set.finite_univ
--     (Indep := fun I => BIndep I)
--     (indep_empty := h_indep_empty)
--     (indep_subset := by
--       refine fun I J hJ hIJ ↦ ?_
--       rw [hBI, hBM]
--       rw [hBI, hBM] at hJ
--       obtain ⟨JA, f, hJA, hJAM⟩ := hJ
--       set IA := f '' I with hIA
--       have : IA ⊆ JA := by
--         rw [hIA, ← BijOn.image_eq hJAM.left]
--         apply image_mono hIJ
--       refine ⟨IA, f, Matroid.Indep.subset hJA this,
--         ⟨mapsTo_image f I, InjOn.mono hIJ (BijOn.injOn hJAM.left), surjOn_image f I⟩,
--         fun v hv ↦  hJAM.right v (hIJ hv)⟩
--       )


--     (indep_aug := by
--       refine fun I J hI hJ hIJ ↦ ?_

--       have (n : ℕ) : ∀ IA JA f g, n = (IA \ JA).ncard → MA.Indep IA → MA.Indep JA →
--           Bmatch IA I f → Bmatch JA J g → ∃ e ∈ J, e ∉ I ∧ BIndep (insert e I) := by
--         obtain ⟨IA, f, hIAI, hIAM⟩ := hI
--         obtain ⟨JA, g, hJAI, hJAM⟩ := hJ

--         have easy_case {IA JA JA' : Set α} {f g : β → α} (hIAI : MA.Indep IA) (hJAI : MA.Indep JA)
--           (hIAM : Bmatch IA I f) (hJAM : Bmatch JA J g) (hset : JA' = JA \ (IA ∪ g '' (I ∩ J)))
--           (hcl: ¬JA' ⊆ MA.cl IA) : ∃ e ∈ J, e ∉ I ∧ BIndep (insert e I) := by
--           obtain ⟨eA, heA, heA'⟩ := not_subset.mp hcl

--           have h'': invFunOn g J '' (g '' (J \ I)) ⊆ J \ I := invFunOn_subset_image_subset
--             (InjOn.bijOn_image (BijOn.injOn hJAM.left)) diff_subset

--           have hIJ : IA.encard < JA.encard := by
--             rw [← BijOn.image_eq hJAM.left, ← BijOn.image_eq hIAM.left,
--              InjOn.encard_image (BijOn.injOn hJAM.left), InjOn.encard_image (BijOn.injOn hIAM.left),
--              ← Finite.cast_ncard_eq (Finite.subset finite_univ (subset_univ I)),
--              ← Finite.cast_ncard_eq (Finite.subset finite_univ (subset_univ J))]
--             apply Nat.strictMono_cast hIJ

--           have hJA' : JA'.Nonempty := by
--             contrapose! hcl
--             exact hcl ▸ empty_subset (MA.cl IA)

--           have h': JA' ⊆ g '' (J \ I) := by
--             rw [← diff_self_inter, hset]
--             apply subset_trans _ (subset_image_diff g J (J ∩ I))
--             rw [BijOn.image_eq hJAM.left]
--             apply diff_subset_diff subset_rfl
--             rw [inter_comm]
--             apply subset_union_right

--           have h'': invFunOn g J '' (g '' (J \ I)) ⊆ J \ I := invFunOn_subset_image_subset
--             (InjOn.bijOn_image (BijOn.injOn hJAM.left)) diff_subset

--           have hdis {x : β}: x ∈ I → x ≠ invFunOn g J eA := by
--             contrapose!
--             refine fun h ↦ ?_
--             rw [h]
--             apply ((mem_diff (invFunOn g J eA)).mp
--             (h'' (mem_image_of_mem (invFunOn g J) (h' heA)))).right

--           have heAI: invFunOn g J eA ∉ I := by
--             exact fun a ↦ hdis a rfl

--           have h''' : eA ∈ g '' J := by
--             rw [BijOn.image_eq hJAM.left]
--             exact ((mem_diff eA).mp (hset ▸ heA)).left

--           refine ⟨invFunOn g J eA, invFunOn_mem h''', ?_, ?_⟩
--           apply ((mem_diff (invFunOn g J eA)).mp
--             (h'' (mem_image_of_mem (invFunOn g J) (h' heA)))).right

--           rw [hBI, hBM]
--           simp only [exists_and_left]

--           have : MA.Indep (insert eA IA) := ((Matroid.Indep.not_mem_cl_iff hIAI
--             ((Matroid.Indep.subset_ground hJAI) ((mem_diff eA).mp (hset ▸ heA)).left)).mp heA').left

--           refine ⟨(insert eA IA), this, ?_⟩
--           set h  := fun (x : β) ↦ if x = (invFunOn g J eA) then eA else f x with hh

--           have hheA : h (invFunOn g J eA) = eA := by
--             simp only [hh, ↓reduceIte]

--           have heAIA : eA ∉ IA := by
--                 obtain ht := ((mem_diff eA).mp ((subset_of_eq hset) heA)).right
--                 contrapose! ht
--                 apply (mem_union eA IA (g '' (I ∩ J))).mpr (Or.intro_left _ ht)

--           have heAB : EqOn f h I := by
--             rw [hh, EqOn]
--             refine fun x hx ↦ ?_
--             simp only [hdis hx, ↓reduceIte]

--           refine ⟨h, (bijOn_insert ((EqOn.bijOn_iff heAB).mp hIAM.left) heAI).mpr ⟨hheA, heAIA⟩, ?_⟩
--           · simp only [mem_insert_iff, forall_eq_or_imp]
--             refine ⟨?_, ?_⟩
--             · simp only [hh, ↓reduceIte]
--               nth_rw 1 [← (invFunOn_eq h''')]
--               apply hJAM.right (invFunOn g J eA) (invFunOn_mem h''')
--             · refine fun a ha ↦ ?_
--               simp only [hh, hdis ha, ↓reduceIte]
--               apply hIAM.right a ha

--         have annoying_case {IA JA JA' : Set α} {f g : β → α} (hIAI : MA.Indep IA) (hJAI : MA.Indep JA)
--           (hIAM : Bmatch IA I f) (hJAM : Bmatch JA J g) (hset : JA' = JA \ (IA ∪ g '' (I ∩ J)))
--           (hcl: JA' ⊆ MA.cl IA) : ∃ IA' f', MA.Indep IA' ∧ f' = 1 := by sorry

--         induction' n with n ih
--         · intro IA JA f g hn hIAI hJAI hIAM hJAM

--           set JA' := JA \ (IA ∪ g '' (I ∩ J)) with hset

--           have : IA ⊆ JA :=
--               diff_eq_empty.mp
--               ((ncard_eq_zero (Finite.subset finite_univ (subset_univ (IA \ JA)))).mp (Eq.symm hn))


--           by_cases hJA' : JA'.Nonempty
--           · obtain ⟨eA, heA⟩ := hJA'
--             rw [hset] at heA

--             have heIA: eA ∉ IA := by
--               obtain heA := ((mem_diff eA).mp heA).right
--               contrapose! heA
--               exact subset_union_left heA

--             have : eA ∉ MA.cl IA := (Matroid.Indep.not_mem_cl_iff hIAI
--               (Matroid.Indep.subset_ground hJAI ((mem_diff eA).mp heA).left)).mpr
--                 ⟨(Matroid.Indep.subset hJAI (insert_subset ((mem_diff eA).mp heA).left this)), heIA⟩

--             exact easy_case hIAI hJAI hIAM hJAM hset (not_subset.mpr ⟨eA, heA, this⟩)
--           ·  sorry

--         · intro IA JA f g hn hIAI hJAI hIAM hJAM
--           set JA' := JA \ (IA ∪ g '' (I ∩ J)) with hset

--           by_cases hcl : JA' ⊆ MA.cl IA
--           · have hIJ : IA.encard < JA.encard := by
--               rw [← BijOn.image_eq hJAM.left, ← BijOn.image_eq hIAM.left,
--               InjOn.encard_image (BijOn.injOn hJAM.left), InjOn.encard_image (BijOn.injOn hIAM.left),
--               ← Finite.cast_ncard_eq (Finite.subset finite_univ (subset_univ I)),
--               ← Finite.cast_ncard_eq (Finite.subset finite_univ (subset_univ J))]
--               apply Nat.strictMono_cast hIJ
--             have : ¬JA ⊆ MA.cl IA := by
--               obtain h := (Matroid.indep_iff_er_eq_card (Matroid.Indep.subset_ground hIAI)).mp hIAI
--               obtain h₁ := MA.er_cl_eq IA
--               obtain h₂ := (Matroid.indep_iff_er_eq_card (Matroid.Indep.subset_ground hJAI)).mp hJAI
--               contrapose! hIJ
--               rw [← h₂, ← h, ← h₁]
--               exact MA.er_mono hIJ
--             obtain ⟨eA, heA, heAI⟩ := Matroid.Indep.augment hIAI hJAI hIJ

--             have heAg : eA ∈ g '' (I ∩ J) := by
--               have : eA ∉ IA ∪ JA' := by
--                 obtain h := (Matroid.Indep.not_mem_cl_iff_of_not_mem hIAI
--                   ((mem_diff eA).mp heA).right (Matroid.Indep.subset_ground hJAI
--                     ((mem_diff eA).mp heA).left)).mpr heAI
--                 contrapose! h
--                 exact union_subset (MA.subset_cl IA (Matroid.Indep.subset_ground hIAI)) hcl h
--               contrapose! this
--               simp only [hset, mem_union, mem_diff, not_or]
--               right
--               exact ⟨((mem_diff eA).mp heA).left, ((mem_diff eA).mp heA).right, this⟩

--             set a := f (invFunOn g J eA) with ha
--             set IA' := insert eA (IA \ {a}) with hIA'
--             set f' := fun (x : β) ↦ if x = (invFunOn g J eA) then eA else f x with hf'

--             have heq : EqOn f' f (I \ {invFunOn g J eA}) := by
--               rw [hf', EqOn]
--               refine fun x hx ↦ ?_
--               simp only [not_in_singleton ((mem_diff x).mp hx).right, ↓reduceIte]

--             have hinv : invFunOn g J eA ∉ I \ {invFunOn g J eA} := by
--               simp only [mem_diff, mem_singleton_iff, not_true_eq_false, and_false,
--                 not_false_eq_true]

--             have hf'eA: f' (invFunOn g J eA) = eA := by
--               simp only [hf', ↓reduceIte]

--             have heAIA : eA ∉ IA \ {a} := by
--               obtain h := ((mem_diff eA).mp heA).right
--               simp [mem_diff, mem_singleton_iff, not_and, Decidable.not_not, imp_iff_not_or, h]

--             obtain h' := invFunOn_subset_mem
--                 (InjOn.bijOn_image (BijOn.injOn hJAM.left)) (@inter_subset_right β I J) heAg

--             have heAa : eA ≠ a:= by
--               obtain h := ((mem_diff eA).mp heA).right
--               contrapose! h
--               rw [h, ← BijOn.image_eq hIAM.left, ha]
--               exact mem_image_of_mem f (inter_subset_left h')

--             have heAIA' : eA ∉ f '' (I \ {(invFunOn g J eA)}) := by
--               contrapose! heAIA
--               simp [← BijOn.image_eq hIAM.left]
--               refine ⟨((mem_diff eA).mp
--                 (subset_of_eq (InjOn.image_diff (BijOn.injOn hIAM.left)) heAIA)).left, heAa⟩

--             have hIA'I: MA.Indep IA' := Matroid.Indep.subset heAI (subset_trans (subset_of_eq hIA')
--                 ((insert_diff_singleton_comm heAa IA).symm ▸ diff_subset))

--             have h₁ : insert (invFunOn g J eA) (I \ {(invFunOn g J eA)}) = I := by
--               simp only [insert_diff_singleton, insert_eq_self, h'.left]

--             have h₂ : f '' (I \ {invFunOn g J eA}) = IA \ {a} := by
--               simp [InjOn.image_diff_subset (BijOn.injOn hIAM.left)
--                 (singleton_subset_iff.mpr h'.left), ha, BijOn.image_eq hIAM.left]

--             have hIA'M: Bmatch IA' I f' := by
--               refine ⟨h₁ ▸ hIA' ▸ h₂ ▸ (bijOn_insert
--                 ((EqOn.bijOn_iff heq).mpr (InjOn.bijOn_image
--                   (InjOn.mono diff_subset (BijOn.injOn hIAM.left)))) hinv).mpr ⟨hf'eA, heAIA'⟩ , ?_⟩
--               · intro v hv
--                 rw [hf']
--                 by_cases hc : v = invFunOn g J eA
--                 · simp [hc]
--                   have : g v = eA := by
--                     rw [hc]
--                     exact invFunOn_eq ((BijOn.surjOn hJAM.left) ((mem_diff eA).mp heA).left)
--                   rw [← hc, ← this]
--                   have : v ∈ I ∩ J := by
--                     rw [hc]
--                     exact invFunOn_subset_mem (InjOn.bijOn_image (BijOn.injOn hJAM.left))
--                       inter_subset_right heAg
--                   exact hJAM.right v (inter_subset_right this)
--                 · simp [hc]
--                   exact hIAM.right v hv

--             have : n = (IA' \ JA).ncard := by sorry

--             exact ih IA' JA f' g this hIA'I hJAI hIA'M hJAM

--           · exact easy_case hIAI hJAI hIAM hJAM hset hcl
--       sorry
--     )

--     (subset_ground := by
--       refine fun I _ ↦ Set.subset_univ I
--       )
