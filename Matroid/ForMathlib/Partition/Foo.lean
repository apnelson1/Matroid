import Matroid.ForMathlib.Partition.Induce

variable {α : Type*} {S T : Set α} {a b c : α}

namespace Partition

lemma not_disjoint_of_le_le [PartialOrder α] [OrderBot α] (hab : a ≤ b) (hac : a ≤ c) (ha : a ≠ ⊥) :
    ¬ Disjoint b c := by
  contrapose! ha
  exact le_bot_iff.mp (ha hab hac)

lemma not_disjoint_of_le [PartialOrder α] [OrderBot α] (hab : a ≤ b) (habot : a ≠ ⊥) :
    ¬ Disjoint a b := not_disjoint_of_le_le le_rfl hab habot

lemma exists_mem_not_disjoint_of_not_disjoint_sSup [Order.Frame α] (h : ¬ Disjoint a (sSup S)) :
    ∃ b ∈ S, ¬ Disjoint a b := by
  rw [disjoint_sSup_iff] at h
  exact Set.not_subset.mp h

section CompleteLattice

variable [CompleteLattice α] {P Q R : Partition α}

noncomputable def leFun (hPQ : P ≤ Q) : P.parts → Q.parts :=
  fun x ↦ ⟨(hPQ x x.prop).choose, (hPQ x x.prop).choose_spec.left⟩

lemma le_leFun (hPQ : P ≤ Q) (p : P.parts) : p.val ≤ leFun hPQ p :=
  (hPQ p p.prop).choose_spec.right

lemma eq_leFun_val_iff (hPQ : P ≤ Q) {p : P.parts} : a = leFun hPQ p ↔ a ∈ Q ∧ p.val ≤ a := by
  refine ⟨?_, fun h => ?_⟩
  · rintro rfl
    use Subtype.coe_prop (P.leFun hPQ p), le_leFun hPQ p
  · obtain ⟨q, hqQ, heqq⟩ := Partition.exists_unique_of_mem_le hPQ p.prop
    obtain rfl := heqq a h
    exact (heqq (P.leFun hPQ p) ⟨(P.leFun hPQ p).coe_prop, le_leFun hPQ p⟩).symm

lemma eq_leFun_iff (hPQ : P ≤ Q) {p : P.parts} {q : Q.parts} :
    q = leFun hPQ p ↔ p.val ≤ q.val := by
  rw [Subtype.ext_iff, eq_leFun_val_iff hPQ]
  simp

lemma leFun_comp (hPQ : P ≤ Q) (hQR : Q ≤ R) : leFun hQR ∘ leFun hPQ = leFun (hPQ.trans hQR) := by
  ext p
  rw [Function.comp_apply]
  apply R.eq_of_not_disjoint (Subtype.prop _) (Subtype.prop _) <| not_disjoint_of_le_le
    ((le_leFun _ _).trans <| le_leFun _ _) (le_leFun _ _) (P.ne_bot_of_mem p.prop)



def fuzzyRel (P : Partition α) (r : α → α → Prop) : α → α → Prop :=
  fun a b ↦ a ∈ P ∧ b ∈ P ∧ ∃ x y, r x y ∧ x ≤ a ∧ y ≤ b

namespace fuzzyRel

variable {r s : α → α → Prop}

lemma left_mem (h : P.fuzzyRel r a b) : a ∈ P := h.1
lemma right_mem (h : P.fuzzyRel r a b) : b ∈ P := h.2.1
lemma exists_rel (h : P.fuzzyRel r a b) : ∃ x y, r x y ∧ x ≤ a ∧ y ≤ b := h.2.2

lemma symmetric (hr : Symmetric r) : Symmetric (P.fuzzyRel r) := by
  rintro a b ⟨haP, hbP, ⟨x, y, hrxy, hx, hy⟩⟩
  exact ⟨hbP, haP, ⟨y, x, hr hrxy, hy, hx⟩⟩
instance [Std.Symm α r] : Std.Symm α (P.fuzzyRel r) where
  symm := symmetric Std.Symm.symm

lemma eq_self : P.fuzzyRel r = r ↔ ∀ a b, r a b → a ∈ P ∧ b ∈ P := by
  refine ⟨fun hr a b hab ↦ ?_, fun h => ?_⟩
  · obtain ⟨ha, hb, -⟩ := hr ▸ hab
    exact ⟨ha, hb⟩
  ext a b
  simp +contextual only [fuzzyRel, iff_def, and_imp, forall_exists_index, h a b, true_and]
  refine ⟨fun ha hb u v huv hua hvb => ?_, fun h => by use a, b⟩
  obtain ⟨hu, hv⟩ := h u v huv
  obtain rfl := P.eq_of_not_disjoint hu ha (not_disjoint_of_le hua (P.ne_bot_of_mem hu))
  obtain rfl := P.eq_of_not_disjoint hv hb (not_disjoint_of_le hvb (P.ne_bot_of_mem hv))
  exact huv

lemma idem : P.fuzzyRel (P.fuzzyRel r) = P.fuzzyRel r :=
  eq_self.mpr fun _ _ h => ⟨h.1, h.2.1⟩

lemma mono_right (hrs : r ≤ s) : P.fuzzyRel r ≤ P.fuzzyRel s :=
  fun _ _ ⟨haP, hbP, ⟨x, y, hrxy, hx, hy⟩⟩ ↦ ⟨haP, hbP, ⟨x, y, hrs _ _ hrxy, hx, hy⟩⟩

lemma stuff (hPQ : P ≤ Q) (hrP : ∀ a b, r a b → a ∈ P ∧ b ∈ P) :
    (∃ a b, r a b) ↔ ∃ a b, Q.fuzzyRel r a b := by
  refine ⟨fun ⟨a, b, hr⟩ => ?_, fun ⟨a, b, ⟨haP, hbP, ⟨x, y, hrxy, hx, hy⟩⟩⟩ => by use x, y⟩
  obtain ⟨haP, hbP⟩ := hrP a b hr
  obtain ⟨a', ha'Q, haa'⟩ := hPQ a haP
  obtain ⟨b', hb'Q, hbb'⟩ := hPQ b hbP
  use a', b', ha'Q, hb'Q, a, b

@[simp]
lemma bot_left : (⊥ : Partition α).fuzzyRel r = ⊥ := by
  ext x y
  simp [fuzzyRel]

@[simp]
lemma bot_right : P.fuzzyRel ⊥ = ⊥ := by
  ext x y
  simp [fuzzyRel]

lemma fuzzyRel₂_le : Q.fuzzyRel (P.fuzzyRel r) ≤ Q.fuzzyRel r := by
  rintro xq yq
  simp only [fuzzyRel, le_Prop_eq, and_imp, forall_exists_index]
  exact fun hxQ hyQ xp yp hxP hyP x y hxy hxp hyp hxpq hypq =>
    ⟨hxQ, hyQ, x, y, hxy, hxp.trans hxpq, hyp.trans hypq⟩

lemma fuzzyRel₃_eq_fuzzyRel₂_of_le_le (hPQ : P ≤ Q) (hQR : Q ≤ R) :
    R.fuzzyRel (Q.fuzzyRel (P.fuzzyRel r)) = R.fuzzyRel (P.fuzzyRel r) := by
  ext xr yr
  simp only [fuzzyRel, and_congr_right_iff]
  refine fun hxR hyR => ⟨fun ⟨xq, yq, ⟨hxQ, hyQ, xp, yp, hxy, hxpq, hypq⟩, hxqr, hyqr⟩ =>
    ⟨xp, yp, hxy, hxpq.trans hxqr, hypq.trans hyqr⟩,
    fun ⟨xp, yp, ⟨hxP, hyP, hxy⟩, hxpr, hypr⟩ => ?_⟩
  let f := P.leFun hPQ; let g := Q.leFun hQR
  obtain hxr : xr = (g ∘ f) ⟨xp, hxP⟩  :=
    leFun_comp hPQ hQR ▸ (eq_leFun_val_iff (p := ⟨xp, hxP⟩) (hPQ.trans hQR)).mpr ⟨hxR, hxpr⟩
  obtain hyr : yr = (g ∘ f) ⟨yp, hyP⟩  :=
    leFun_comp hPQ hQR ▸ (eq_leFun_val_iff (p := ⟨yp, hyP⟩) (hPQ.trans hQR)).mpr ⟨hyR, hypr⟩
  exact ⟨f ⟨xp, hxP⟩, f ⟨yp, hyP⟩, ⟨Subtype.prop _, Subtype.prop _, xp, yp, ⟨hxP, hyP, hxy⟩,
    le_leFun hPQ ⟨xp, hxP⟩, le_leFun hPQ ⟨yp, hyP⟩⟩, hxr ▸ le_leFun hQR _, hyr ▸ le_leFun hQR _⟩

@[simp]
lemma or :
    P.fuzzyRel (fun x y => r x y ∨ s x y) a b ↔ P.fuzzyRel r a b ∨ P.fuzzyRel s a b := by
  refine ⟨fun ⟨ha, hb, x, y, hxy, hxa, hyb⟩ => ?_, fun h => ?_⟩
  · apply hxy.imp <;> exact (⟨ha, hb, x, y, ·, hxa, hyb⟩)
  apply h.elim <;> exact fun ⟨ha, hb, x, y, h, hxa, hyb⟩ => ⟨ha, hb, x, y, by simp [h], hxa, hyb⟩

lemma sup_right : P.fuzzyRel (r ⊔ s) = P.fuzzyRel r ⊔ P.fuzzyRel s := by
  ext x y
  exact or

lemma and (h : P.fuzzyRel (fun x y => r x y ∧ s x y) a b) :
    P.fuzzyRel r a b ∧ P.fuzzyRel s a b := by
  obtain ⟨ha, hb, x, y, hxy, hxa, hyb⟩ := h
  apply hxy.imp <;> exact (⟨ha, hb, x, y, ·, hxa, hyb⟩)

lemma inf_right_le : P.fuzzyRel (r ⊓ s) ≤ P.fuzzyRel r ⊓ P.fuzzyRel s :=
  fun _ _ => and

@[simp]
lemma and_const {p : Prop} : P.fuzzyRel (fun x y => r x y ∧ p) a b ↔ P.fuzzyRel r a b ∧ p := by
  unfold fuzzyRel
  tauto

@[simp]
lemma const_and {p : Prop} : P.fuzzyRel (fun x y => p ∧ r x y) a b ↔ p ∧ P.fuzzyRel r a b := by
  rw [and_comm, ← and_const]
  simp only [and_comm]

end fuzzyRel

def foo (P : Partition α) (a : α) : α := P.cover a |>.supp

@[simp]
lemma foo_bot : foo P ⊥ = ⊥ := by
  simp [foo]

@[simp]
lemma foo_le_supp : foo P a ≤ P.supp := by
  simp only [foo, Partition.cover_supp, Partition.mem_parts, sSup_le_iff, Set.mem_setOf_eq, and_imp]
  exact fun _ hbP _ ↦ P.le_supp_of_mem hbP

lemma foo_le_of_le_of_mem (haPb : a ⊓ P.supp ≤ b) (hbP : b ∈ P) : foo P a ≤ b := by
  simp only [foo, cover_supp, mem_parts, sSup_le_iff, Set.mem_setOf_eq, and_imp]
  refine fun x hxP hdj ↦ (P.eq_of_not_disjoint hxP hbP ?_).le
  contrapose! hdj
  refine disjoint_iff_inf_le.mpr <| hdj inf_le_right (le_trans ?_ haPb)
  exact inf_le_inf_left a <| le_supp_of_mem hxP

lemma le_foo_of_not_disjoint (hbP : b ∈ P) (hndj : ¬ Disjoint a b) : b ≤ foo P a := by
  simp only [foo, cover_supp, mem_parts]
  exact le_sSup ⟨hbP, hndj⟩

lemma foo_eq_of_inter_subset (hndj : ¬ Disjoint a P.supp) (haPb : a ⊓ P.supp ≤ b) (hbP : b ∈ P) :
    foo P a = b := by
  refine le_antisymm (foo_le_of_le_of_mem haPb hbP) <| le_foo_of_not_disjoint hbP ?_
  contrapose! hndj
  rw [disjoint_iff_inf_le]
  exact hndj inf_le_left haPb

@[simp]
lemma foo_eq_of_indiscrete' : (indiscrete' a).foo a = a := by
  by_cases h : a = ⊥
  · subst a
    simp [foo]
  simp only [foo, ne_eq, h, not_false_eq_true, indiscrete'_eq_of_ne_bot, cover_supp,
    indiscrete_parts, Set.mem_singleton_iff]
  suffices {s | s = a ∧ ¬Disjoint a s} = {a} by simp [this]
  ext s
  simp +contextual [iff_def, h]

end CompleteLattice

section Frame

variable [Order.Frame α] {P Q R : Partition α}

lemma foo_le_iff_of_mem (hbP : b ∈ P) : P.foo a ≤ b ↔ a ⊓ P.supp ≤ b := by
  refine ⟨fun h => ?_, (foo_le_of_le_of_mem · hbP)⟩
  simp only [foo, cover_supp, mem_parts, sSup_le_iff, Set.mem_setOf_eq, and_imp] at h
  simp_rw [supp, inf_sSup_eq, iSup_le_iff]
  rintro p hpP
  by_cases hap : Disjoint a p
  · rw [hap.eq_bot]
    exact bot_le
  exact inf_le_right.trans <| h p hpP hap

lemma le_foo_iff_of_mem (hbP : b ∈ P) : b ≤ foo P a ↔ ¬ Disjoint a b := by
  refine ⟨fun h => ?_, le_foo_of_not_disjoint hbP⟩
  simp only [foo, cover_supp, mem_parts] at h
  obtain ⟨p, ⟨hpP, hap⟩, hbp⟩ := exists_mem_not_disjoint_of_not_disjoint_sSup
    <| not_disjoint_of_le h (P.ne_bot_of_mem hbP)
  obtain rfl := P.eq_of_not_disjoint hbP hpP hbp
  exact hap

lemma foo_eq_iff_of_mem (hbP : b ∈ P) : P.foo a = b ↔ a ⊓ P.supp ≤ b ∧ ¬ Disjoint a b := by
  rw [le_antisymm_iff, le_foo_iff_of_mem hbP, foo_le_iff_of_mem hbP]

@[simp]
lemma foo_eq_self_of_mem (haP : a ∈ P) : P.foo a = a := by
  rw [foo_eq_iff_of_mem haP]
  simp [P.ne_bot_of_mem haP]

@[simp]
lemma foo_eq_bot_iff : P.foo a = ⊥ ↔ Disjoint a P.supp := by
  simp only [foo, supp, cover_parts, sSup_eq_bot, Set.mem_setOf_eq, and_imp, disjoint_sSup_iff,
    mem_parts]
  refine forall₂_congr fun p hpP => ?_
  simp_all [P.ne_bot_of_mem hpP]

lemma inf_foo_eq_inf_supp : a ⊓ P.foo a = a ⊓ P.supp := by
  refine le_antisymm (inf_le_inf le_rfl foo_le_supp) ?_
  simp only [supp, inf_sSup_eq, mem_parts, foo, cover_parts, Set.mem_setOf_eq, iSup_le_iff]
  rintro p hpP
  by_cases hap : Disjoint a p
  · rw [hap.eq_bot]
    exact bot_le
  exact le_biSup (min a) ⟨hpP, hap⟩

lemma self_le_foo_iff : a ≤ P.foo a ↔ a ≤ P.supp := by
  refine ⟨(le_trans · foo_le_supp), fun h => ?_⟩
  have : a = a ⊓ P.supp := left_eq_inf.mpr h
  nth_rw 1 [this, ← inf_foo_eq_inf_supp]
  exact inf_le_right

lemma foo_mem_iff : P.foo a ∈ P ↔ ¬ Disjoint a P.supp ∧ ∃ T ∈ P, a ⊓ P.supp ≤ T := by
  refine ⟨fun h => ⟨?_, P.foo a, h, ?_⟩,
    fun ⟨hS, T, hTP, hST⟩ => foo_eq_of_inter_subset hS hST hTP ▸ hTP⟩
  · by_contra! hS
    rw [← foo_eq_bot_iff] at hS
    simpa [hS] using P.ne_bot_of_mem h
  rw [← inf_foo_eq_inf_supp]
  exact inf_le_right

lemma foo_left_mono (hPQ : P ≤ Q) : P.foo a ≤ Q.foo a :=
  supp_le_of_le <| cover_le_of_le hPQ

lemma foo_right_mono (hab : a ≤ b) : P.foo a ≤ P.foo b := by
  simp_rw [foo, supp]
  refine sSup_le_sSup ?_
  simp only [cover_parts, Set.setOf_subset_setOf, and_imp]
  rintro p hpP hap
  use hpP
  contrapose! hap
  exact hap.mono_left hab

lemma foo_mono (hPQ : P ≤ Q) (hab : a ≤ b) : P.foo a ≤ Q.foo b :=
  (foo_left_mono hPQ).trans (foo_right_mono hab)

lemma self_le_foo_of_le_of_mem (hPQ : P ≤ Q) (ha : a ∈ P) : a ≤ foo Q a := by
  nth_rw 1 [← foo_eq_self_of_mem ha]
  exact foo_left_mono hPQ

lemma foo_mem_of_le (hPQ : P ≤ Q) (haP : a ∈ P) : foo Q a ∈ Q := by
  rw [foo_mem_iff]
  have := (le_supp_of_mem haP).trans (supp_le_of_le hPQ)
  use not_disjoint_of_le this (P.ne_bot_of_mem haP)
  simp only [inf_eq_left.mpr this, hPQ a haP]

-- lemma foo_eq_self_of_le (haQ : a ∈ Q) (hPQ : P ≤ Q) (haP : a ≤ P.supp) : foo P a = a := by

--   -- ext a
--   -- simp only [foo, sUnion_image, mem_iUnion, mem_partOf_iff, exists_prop]
--   -- exact ⟨fun ⟨b, hbS, hab⟩ => (Rel.forall (rel_le_of_le hPQ a b hab) hS).mpr hbS,
--   --   fun haS => ⟨a, haS, rel_self_iff_mem_supp.mpr (hSP haS)⟩⟩

-- lemma foo_eq_self_of_subset (hPQ : P ⊆ Q) (hS : S ∈ P) : foo Q S = S :=
--   Q.eq_of_mem_of_mem (foo_mem_of_le (le_of_subset hPQ) hS) (hPQ hS)
--     (self_subset_foo_iff.mpr ((P.subset_of_mem hS).trans <| supp_le_of_subset hPQ)
--       (P.nonempty_of_mem hS).some_mem) (P.nonempty_of_mem hS).some_mem

-- @[simp]
-- lemma foo_eq_self_of_mem (hS : S ∈ P) : foo P S = S :=
--   foo_eq_self_of_subset (subset_refl P) hS

-- lemma foo_subset_foo_foo (hPQ : P ≤ Q) : foo Q (foo P S) ⊆ foo Q S := by
--   intro a
--   simp only [foo, sUnion_image, mem_iUnion, mem_partOf_iff, exists_prop, iUnion_exists,
--     biUnion_and', forall_exists_index, and_imp]
--   exact fun b hbS c hPcb hQac ↦ ⟨b, hbS, hQac.trans (rel_le_of_le hPQ _ _ hPcb)⟩

-- lemma foo_foo_eq_foo (hPQ : P ≤ Q) (hS : S ⊆ P.supp) : foo Q (foo P S) = foo Q S := by
--   refine subset_antisymm (foo_subset_foo_foo hPQ) fun a ↦ ?_
--   simp only [foo, sUnion_image, mem_iUnion, mem_partOf_iff, exists_prop, iUnion_exists,
--     biUnion_and', forall_exists_index, and_imp]
--   intro b hbS hQab
--   use b, hbS, b, rel_self_of_mem_supp (hS hbS)

end Frame
