import Matroid.ForMathlib.Partition.Set

open Set Function Relation

variable {α β ι ι' : Type*} {r : α → α → Prop} {f : ι → α} {x y z : α}

namespace Partition

section Rep

variable {S T : Set α} {a b : α} {P : Partition (Set α)}

/-- Noncomputably choose a representative from an equivalence class-/
noncomputable def rep (P : Partition (Set α)) (ht : T ∈ P) : α := (P.nonempty_of_mem ht).some

@[simp] lemma rep_mem (ht : T ∈ P) : P.rep ht ∈ T :=
  (P.nonempty_of_mem ht).some_mem

@[simp] lemma rep_mem' (ht : T ∈ P) : P.rep ht ∈ P.supp :=
  P.subset_of_mem ht <| rep_mem ht

@[simp] lemma partOf_rep (ht : T ∈ P) : P.partOf (P.rep ht) = T :=
  (eq_partOf_of_mem ht (P.rep_mem ht)).symm

lemma finite_of_finite (P : Partition (Set α)) (hs : P.supp.Finite) : (P : Set (Set α)).Finite :=
  hs.finite_subsets.subset fun _ ↦ subset_of_mem

lemma rel_iff_partOf_eq_partOf (P : Partition (Set α)) (hx : x ∈ P.supp) (hy : y ∈ P.supp) :
    P x y ↔ P.partOf x = P.partOf y := by
  refine ⟨fun ⟨t, htP, hxt, hyt⟩ ↦ ?_, fun h ↦ ⟨P.partOf x, P.partOf_mem hx, P.mem_partOf hx, ?_⟩⟩
  · rw [eq_partOf_of_mem (P.partOf_mem hx)]
    rwa [← eq_partOf_of_mem htP hxt]
  rw [h]
  exact mem_partOf hy

lemma rel_iff_partOf_eq_partOf' (P : Partition (Set α)) :
    P x y ↔ ∃ (_ : x ∈ P.supp) (_ : y ∈ P.supp), P.partOf x = P.partOf y :=
  ⟨fun h ↦ ⟨h.left_mem, h.right_mem, (P.rel_iff_partOf_eq_partOf h.left_mem h.right_mem).1 h⟩,
    fun ⟨hx,hy,h⟩ ↦ (P.rel_iff_partOf_eq_partOf hx hy).2 h⟩

lemma rel_iff_forall : P x y ↔ x ∈ P.supp ∧ ∀ t ∈ P, x ∈ t ↔ y ∈ t := by
  refine ⟨fun h ↦ ⟨h.left_mem, fun _ ↦ h.forall⟩,
    fun ⟨hxs, h⟩ ↦ ⟨P.partOf x, P.partOf_mem hxs, P.mem_partOf hxs, ?_⟩⟩
  rw [← h _ (P.partOf_mem hxs)]
  exact P.mem_partOf hxs

lemma setOf_rel_self_eq (P : Partition (Set α)) : {x | P x x} = P.supp := by
  refine subset_antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · obtain ⟨t, ht, hxP, -⟩ := hx
    exact subset_of_mem ht hxP
  obtain ⟨t, ⟨ht, hxt⟩, -⟩ := P.exists_unique_of_mem_supp hx
  exact ⟨t, ht, hxt, hxt⟩

lemma rel_self_iff_mem : P x x ↔ x ∈ P.supp := by
  simp [← P.setOf_rel_self_eq]

lemma setOf_rel_eq (ht : T ∈ P) (hx : x ∈ T) : {y | P x y} = T :=
  Set.ext fun y ↦ ⟨fun ⟨t', ht', hx', hy'⟩ ↦ by rwa [P.eq_of_mem_of_mem ht ht' hx hx'],
    fun h ↦ ⟨T, ht, hx, h⟩⟩

lemma rep_rel (ht : T ∈ P) (hx : x ∈ T) : P x (P.rep ht) :=
  ⟨T, ht, hx, P.rep_mem ht⟩

@[simp] lemma rep_rel_self {P : Partition (Set α)} (ht : T ∈ P) : P (P.rep ht) (P.rep ht) :=
  rep_rel _ (P.rep_mem ht)

lemma setOf_rel_rep_eq (ht : T ∈ P) : {x | P (P.rep ht) x} = T :=
  setOf_rel_eq ht (P.rep_mem ht)

/-- The `partOf x` is the set of `y` related to `x`. True even if `x ∉ s`, since both are `∅`.-/
lemma setOf_rel_eq_partOf (P : Partition (Set α)) (x : α) : {y | P x y} = P.partOf x := by
  by_cases hx : x ∈ P.supp
  · rw [setOf_rel_eq (P.partOf_mem hx) (P.mem_partOf hx)]
  rw [partOf_eq_empty _ hx, eq_empty_iff_forall_notMem]
  exact fun y hxy ↦ hx <| Rel.left_mem hxy

lemma setOf_rel_mem (P : Partition (Set α)) (hx : x ∈ P.supp) : {y | P x y} ∈ P := by
  obtain ⟨t, ⟨ht,hp⟩, -⟩ := P.exists_unique_of_mem_supp hx
  rwa [setOf_rel_eq ht hp]

lemma discrete.rel_iff_eq_of_mem (ha : a ∈ P.supp) :
    (Partition.discrete P.supp) a b ↔ a = b := by
  rw [rel_discrete_iff, and_iff_left ha]

end Rep

section RepFun

variable {a b : α} {s : Set α} {P : Partition (Set α)}

structure RepFun (P : Partition (Set α)) where
  (toFun : α → α)
  (apply_eq_self_of_notMem : ∀ a ∉ P.supp, toFun a = a)
  (rel_apply_of_mem : ∀ a ∈ P.supp, P a (toFun a))
  (apply_eq_of_rel : ∀ a b, P a b → toFun a = toFun b)

instance : FunLike (RepFun P) α α where
  coe := RepFun.toFun
  coe_injective' f f' := by cases f; cases f'; simp

def RepFun.mk' (P : Partition (Set α)) (f : α → α) {p : α → Prop} (hP : ∀ {x}, x ∈ P.supp ↔ p x)
    (h₁ : ∀ a, ¬ p a → f a = a) (h₂ : ∀ a, p a → P a (f a))
    (h₃ : ∀ a b, P a b → f a = f b) : P.RepFun :=
  ⟨f, fun a ha ↦ h₁ a (hP.not.mp ha), fun a ha ↦ h₂ a (hP.mp ha), h₃⟩

@[simp]
lemma RepFun.mk_apply (P : Partition (Set α)) (f) (h₁ : ∀ a ∉ P.supp, f a = a)
  (h₂ : ∀ a ∈ P.supp, P a (f a)) (h₃) (x : α) : (RepFun.mk f h₁ h₂ h₃) x = f x := rfl

lemma RepFun.apply_of_notMem (f : P.RepFun) (ha : a ∉ P.supp) : f a = a :=
  f.apply_eq_self_of_notMem a ha

lemma RepFun.rel_apply (f : P.RepFun) (ha : a ∈ P.supp) : P a (f a) :=
  f.rel_apply_of_mem a ha

lemma RepFun.rel_apply' (f : P.RepFun) {p : α → Prop} (hP : ∀ {x}, x ∈ P.supp ↔ p x) (ha : p a) :
    P a (f a) := f.rel_apply <| hP.mpr ha

lemma RepFun.apply_mem (f : P.RepFun) (ha : a ∈ P.supp) : f a ∈ P.supp :=
  (f.rel_apply ha).right_mem

lemma RepFun.apply_mem' (f : P.RepFun) {p : α → Prop} (hP : ∀ {x}, x ∈ P.supp ↔ p x) (ha : p a) :
    p (f a) := hP.mp <| f.apply_mem <| hP.mpr ha

lemma RepFun.image_subset_self (f : P.RepFun) : f '' P.supp ⊆ P.supp := by
  rintro _ ⟨a, ha, rfl⟩
  exact f.apply_mem ha

lemma RepFun.mapsTo (f : P.RepFun) : Set.MapsTo f P.supp P.supp := by
  intro a ha
  exact f.apply_mem ha

@[simp]
lemma RepFun.apply_mem_iff (f : P.RepFun) : f a ∈ P.supp ↔ a ∈ P.supp := by
  refine ⟨fun h ↦ ?_, f.apply_mem⟩
  by_contra ha
  exact ha <| f.apply_of_notMem ha ▸ h

lemma RepFun.apply_eq_apply (f : P.RepFun) (hab : P a b) : f a = f b :=
  f.apply_eq_of_rel a b hab

lemma RepFun.rel_of_apply_eq_apply (f : P.RepFun) (ha : a ∈ P.supp) (hab : f a = f b) :
    P a b := by
  refine (f.rel_apply ha).trans ?_
  rw [hab, P.rel_comm]
  refine f.rel_apply <| by_contra fun hb ↦ ?_
  rw [f.apply_of_notMem hb] at hab; rw [← hab] at hb
  exact hb <| f.apply_mem ha

lemma RepFun.rel_of_ne_of_apply_eq_apply (f : P.RepFun) (hne : a ≠ b) (hab : f a = f b) :
    P a b := by
  obtain (ha | ha) := em (a ∈ P.supp); exact f.rel_of_apply_eq_apply ha hab
  obtain (hb | hb) := em (b ∈ P.supp); exact (f.rel_of_apply_eq_apply hb hab.symm).symm
  rw [f.apply_of_notMem ha, f.apply_of_notMem hb] at hab; contradiction

lemma RepFun.apply_eq_apply_iff_rel (f : P.RepFun) (ha : a ∈ P.supp) : f a = f b ↔ P a b :=
  ⟨f.rel_of_apply_eq_apply ha, f.apply_eq_apply⟩

lemma RepFun.apply_eq_apply_iff_rel_of_ne (f : P.RepFun) (hne : a ≠ b) : f a = f b ↔ P a b :=
  ⟨f.rel_of_ne_of_apply_eq_apply hne, f.apply_eq_apply⟩

@[simp]
lemma RepFun.idem (f : P.RepFun) (a : α) : f (f a) = f a := by
  obtain (ha | ha) := em (a ∈ P.supp)
  · rw [eq_comm, f.apply_eq_apply_iff_rel ha]
    exact f.rel_apply ha
  simp_rw [f.apply_of_notMem ha]

/-- Any partially defined `RepFun` extends to a complete one. -/
lemma exists_extend_partial_repFun (P : Partition (Set α)) {t : Set α} (f₀ : t → α)
    (h_notMem : ∀ x : t, x.1 ∉ P.supp → f₀ x = x) (h_mem : ∀ x : t, x.1 ∈ P.supp → P x (f₀ x))
    (h_eq : ∀ x y : t, P x y → f₀ x = f₀ y) : ∃ (f : P.RepFun), ∀ x : t, f x = f₀ x := by
  classical
  set f : α → α := fun a ↦ if ha : a ∈ P.supp then
    (if hb : ∃ b : t, P a b then f₀ hb.choose else P.rep (P.partOf_mem ha)) else a with hf
  refine ⟨RepFun.mk f (fun a ha ↦ by simp [hf, ha]) (fun a ha ↦ ?_) (fun a b hab ↦ ?_), fun a ↦ ?_⟩
  · simp only [hf, ha, ↓reduceDIte]
    split_ifs with h
    · exact h.choose_spec.trans <| h_mem h.choose h.choose_spec.right_mem
    push_neg at h
    exact P.rep_rel (P.partOf_mem ha) (P.mem_partOf ha)
  · simp_rw [hf, dif_pos hab.left_mem, dif_pos hab.right_mem]
    split_ifs with h₁ h₂ h₂
    · exact h_eq _ _ <| (hab.symm.trans h₁.choose_spec).symm.trans h₂.choose_spec
    · exact False.elim <| h₂ ⟨_, hab.symm.trans h₁.choose_spec⟩
    · exact False.elim <| h₁ ⟨_, hab.trans h₂.choose_spec⟩
    congr 1
    rwa [← rel_iff_partOf_eq_partOf _ hab.left_mem hab.right_mem]
  change f a = f₀ a
  obtain (ha | ha) := em (a.1 ∈ P.supp)
  · simp only [hf, ha, ↓reduceDIte]
    split_ifs with h
    · exact Eq.symm <| h_eq _ _ h.choose_spec
    exact False.elim <| h ⟨a, rel_self_iff_mem.2 ha⟩
  simp [hf, ha, h_notMem _ ha]

/-- For any set `t` containining no two distinct related elements, there is a `RepFun` equal to
the identity on `t`. -/
lemma exists_extend_partial_repFun' (P : Partition (Set α)) {t : Set α}
    (h : ∀ ⦃x y⦄, x ∈ t → y ∈ t → P x y → x = y) : ∃ (f : P.RepFun), EqOn f id t := by
  simpa using P.exists_extend_partial_repFun (fun x : t ↦ x) (by simp)
    (by simp [P.rel_self_iff_mem]) (fun x y ↦ h x.2 y.2)

lemma nonempty_repFun (P : Partition (Set α)) : Nonempty P.RepFun := by
  obtain ⟨f, -⟩ := P.exists_extend_partial_repFun' (t := ∅) (by simp)
  exact ⟨f⟩

@[simp]
theorem repFun_repFun (f f' : P.RepFun) (x : α) : f (f' x) = f x := by
  obtain (hx | hx) := em (x ∈ P.supp)
  · exact f.apply_eq_apply (f'.rel_apply hx).symm
  rw [f'.apply_of_notMem hx, f.apply_of_notMem hx]

@[simp]
lemma repFun_discrete_coeFun (s : Set α) (f : (Partition.discrete s).RepFun) :
    (f : α → α) = id := by
  ext x
  obtain (hx | hx) := em (x ∈ s)
  · have hx' := f.rel_apply (supp_discrete s ▸ hx)
    rw [rel_discrete_iff] at hx'
    exact hx'.1.symm
  rw [f.apply_of_notMem (supp_discrete s |>.symm ▸ hx), id]

lemma RepFun.coeFun_eq_id_of_eq_discrete  (f : P.RepFun) (hP : P = Partition.discrete s) :
    (f : α → α) = id := by
  subst hP; exact repFun_discrete_coeFun s f

end RepFun

/-! ### IsRepFun -/

section IsRepFun

variable {a b : α} {s : Set α} {P P' : Partition (Set α)} {f g : α → α} {p : α → Prop}

/-- A predicate characterizing when a function `f : α → α` is a representative function for a
partition `P`. A representative function maps each element to a canonical representative in its
equivalence class, is the identity outside the support, and maps related elements to the same
representative. -/
structure IsRepFun (P : Partition (Set α)) (f : α → α) : Prop where
  apply_of_notMem : ∀ ⦃a⦄, a ∉ P.supp → f a = a
  rel_apply : ∀ ⦃a⦄, a ∈ P.supp → P a (f a)
  apply_eq_apply : ∀ ⦃a b⦄, P a b → f a = f b

namespace IsRepFun

/-- Constructor for `IsRepFun` that uses a custom membership predicate. -/
lemma mk' (P : Partition (Set α)) (f : α → α) (hP : ∀ {x}, x ∈ P.supp ↔ p x)
    (h₁ : ∀ a, ¬ p a → f a = a) (h₂ : ∀ a, p a → P a (f a))
    (h₃ : ∀ a b, P a b → f a = f b) : IsRepFun P f :=
  ⟨fun a ha ↦ h₁ a (hP.not.mp ha), fun a ha ↦ h₂ a (hP.mp ha), h₃⟩

lemma rel_apply' (hf : IsRepFun P f) (hP : ∀ {x}, x ∈ P.supp ↔ p x) (ha : p a) :
    P a (f a) := hf.rel_apply <| hP.mpr ha

lemma apply_mem (hf : IsRepFun P f) (ha : a ∈ P.supp) : f a ∈ P.supp :=
  (hf.rel_apply ha).right_mem

lemma apply_mem' (hf : IsRepFun P f) (hP : ∀ {x}, x ∈ P.supp ↔ p x) (ha : p a) : p (f a) :=
  hP.mp <| hf.apply_mem <| hP.mpr ha

lemma image_subset_supp (hf : IsRepFun P f) : f '' P.supp ⊆ P.supp := by
  rintro _ ⟨a, ha, rfl⟩
  exact hf.apply_mem ha

lemma image_subset {S : Set α} (hf : IsRepFun P f) (hS : P.supp ⊆ S) : f '' S ⊆ S := by
  rintro _ ⟨a, haS, rfl⟩
  by_cases ha : a ∈ P.supp
  · exact hS <| hf.apply_mem ha
  · exact (hf.apply_of_notMem ha).symm ▸ haS

lemma mapsTo_supp (hf : IsRepFun P f) : Set.MapsTo f P.supp P.supp :=
  fun _ ↦ hf.apply_mem

lemma mapsTo {S : Set α} (hf : IsRepFun P f) (hS : P.supp ⊆ S) : Set.MapsTo f S S :=
  fun x h ↦ hf.image_subset hS ⟨x, h, rfl⟩

@[simp]
lemma apply_mem_iff (hf : IsRepFun P f) : f a ∈ P.supp ↔ a ∈ P.supp := by
  refine ⟨fun h ↦ ?_, hf.apply_mem⟩
  by_contra ha
  exact ha <| hf.apply_of_notMem ha ▸ h

lemma apply_mem_iff_of_subset {S} (hf : IsRepFun P f) (hS : P.supp ⊆ S) : f a ∈ S ↔ a ∈ S := by
  obtain haS | haS := em (a ∈ P.supp)
  · simp [hS haS, hS <| hf.apply_mem haS]
  rw [hf.apply_of_notMem haS]

lemma rel_of_apply_eq_apply (hf : IsRepFun P f) (ha : a ∈ P.supp) (hab : f a = f b) : P a b := by
  refine (hf.rel_apply ha).trans ?_
  rw [hab, P.rel_comm]
  refine hf.rel_apply <| by_contra fun hb ↦ ?_
  rw [hf.apply_of_notMem hb] at hab; rw [← hab] at hb
  exact hb <| hf.apply_mem ha

lemma rel_of_ne_of_apply_eq_apply (hf : IsRepFun P f) (hne : a ≠ b) (hab : f a = f b) : P a b := by
  obtain (ha | ha) := em (a ∈ P.supp); exact hf.rel_of_apply_eq_apply ha hab
  obtain (hb | hb) := em (b ∈ P.supp); exact (hf.rel_of_apply_eq_apply hb hab.symm).symm
  rw [hf.apply_of_notMem ha, hf.apply_of_notMem hb] at hab
  contradiction

lemma apply_eq_apply_iff_rel (hf : IsRepFun P f) (ha : a ∈ P.supp) : f a = f b ↔ P a b :=
  ⟨hf.rel_of_apply_eq_apply ha, (hf.apply_eq_apply ·)⟩

lemma apply_eq_apply_iff_rel_of_ne (hf : IsRepFun P f) (hne : a ≠ b) : f a = f b ↔ P a b :=
  ⟨hf.rel_of_ne_of_apply_eq_apply hne, (hf.apply_eq_apply ·)⟩

lemma apply_eq_apply_iff (hf : IsRepFun P f) : f a = f b ↔ a = b ∨ P a b := by
  simp only [or_iff_not_imp_left, ← ne_eq]
  refine ⟨fun hab hne ↦ hf.rel_of_ne_of_apply_eq_apply hne hab, fun h ↦ ?_⟩
  obtain rfl | hne := eq_or_ne a b
  · rfl
  exact hf.apply_eq_apply (h hne)

lemma forall_apply_eq_apply_iff (hf : IsRepFun P f) (a) :
    (∀ (x : α), f a = f x ↔ a = x) ∨ (∀ (x : α), f a = f x ↔ P a x) := by
  by_cases ha : a ∈ P.supp
  · right
    rintro b
    rw [hf.apply_eq_apply_iff_rel ha]
  left
  intro b
  rw [hf.apply_of_notMem ha]
  constructor <;> rintro rfl
  · rw [hf.apply_mem_iff] at ha
    exact hf.apply_of_notMem ha
  exact hf.apply_of_notMem ha |>.symm

lemma apply_eq_apply_iff' (hf : IsRepFun P f) :
    f a = f b ↔ (a = b ∧ ∀ c, f a = f c ↔ a = c) ∨ P a b := by
  obtain h1 | h2 := hf.forall_apply_eq_apply_iff a
  · refine ⟨by grind, ?_⟩
    rintro (h | h)
    · exact congrArg _ h.1
    exact hf.apply_eq_apply h
  grind

@[simp]
lemma idem (hf : IsRepFun P f) : f (f a) = f a := by
  obtain (ha | ha) := em (a ∈ P.supp)
  · rw [eq_comm, hf.apply_eq_apply_iff_rel ha]
    exact hf.rel_apply ha
  simp_rw [hf.apply_of_notMem ha]

/-- Any partially defined representative function extends to a complete one. -/
lemma exists_extend_partial (P : Partition (Set α)) {t : Set α} (f₀ : t → α)
    (h_notMem : ∀ x : t, x.1 ∉ P.supp → f₀ x = x) (h_mem : ∀ x : t, x.1 ∈ P.supp → P x (f₀ x))
    (h_eq : ∀ x y : t, P x y → f₀ x = f₀ y) : ∃ f, IsRepFun P f ∧ ∀ x : t, f x = f₀ x := by
  classical
  set f : α → α := fun a ↦ if ha : a ∈ P.supp then
    (if hb : ∃ b : t, P a b then f₀ hb.choose else P.rep (P.partOf_mem ha)) else a with hfdef
  refine ⟨f, ⟨fun a ha ↦ by simp [hfdef, ha], fun a ha ↦ ?_, fun a b hab ↦ ?_⟩, fun a ↦ ?_⟩
  · simp only [hfdef, ha, ↓reduceDIte]
    split_ifs with h
    · exact h.choose_spec.trans <| h_mem h.choose h.choose_spec.right_mem
    push_neg at h
    exact P.rep_rel (P.partOf_mem ha) (P.mem_partOf ha)
  · simp_rw [hfdef, dif_pos hab.left_mem, dif_pos hab.right_mem]
    split_ifs with h₁ h₂ h₂
    · exact h_eq _ _ <| (hab.symm.trans h₁.choose_spec).symm.trans h₂.choose_spec
    · exact False.elim <| h₂ ⟨_, hab.symm.trans h₁.choose_spec⟩
    · exact False.elim <| h₁ ⟨_, hab.trans h₂.choose_spec⟩
    congr 1
    rwa [← rel_iff_partOf_eq_partOf _ hab.left_mem hab.right_mem]
  obtain (ha | ha) := em (a.1 ∈ P.supp)
  · simp only [hfdef, ha, ↓reduceDIte]
    split_ifs with h
    · exact Eq.symm <| h_eq _ _ h.choose_spec
    exact False.elim <| h ⟨a, rel_self_iff_mem.2 ha⟩
  simp [hfdef, ha, h_notMem _ ha]

/-- For any set `t` containing no two distinct related elements, there is a representative function
equal to the identity on `t`. -/
lemma exists_extend_partial' (P : Partition (Set α)) {t : Set α}
    (h : ∀ ⦃x y⦄, x ∈ t → y ∈ t → P x y → x = y) : ∃ f, IsRepFun P f ∧ EqOn f id t := by
  simpa using exists_extend_partial P (fun x : t ↦ x) (by simp)
    (by simp [P.rel_self_iff_mem]) (fun x y ↦ h x.2 y.2)

lemma nonempty (P : Partition (Set α)) : ∃ f, IsRepFun P f := by
  obtain ⟨f, hf, -⟩ := exists_extend_partial' P (t := ∅) (by simp)
  exact ⟨f, hf⟩

@[simp]
theorem isRepFun_isRepFun (hf : IsRepFun P f) (hg : IsRepFun P g) (x : α) : f (g x) = f x := by
  obtain (hx | hx) := em (x ∈ P.supp)
  · exact hf.apply_eq_apply (hg.rel_apply hx).symm
  rw [hg.apply_of_notMem hx, hf.apply_of_notMem hx]

lemma eq_id_of_discrete (s : Set α) (hf : IsRepFun (Partition.discrete s) f) : f = id := by
  ext x
  obtain (hx | hx) := em (x ∈ s)
  · have hx' := hf.rel_apply (supp_discrete s ▸ hx)
    rw [rel_discrete_iff] at hx'
    exact hx'.1.symm
  rw [hf.apply_of_notMem (supp_discrete s |>.symm ▸ hx), id]

lemma eq_id_of_eq_discrete (hf : IsRepFun P f) (hP : P = Partition.discrete s) : f = id := by
  subst hP
  exact eq_id_of_discrete s hf

/-- Convert an `IsRepFun` proof to a `RepFun`. -/
def toRepFun (hf : IsRepFun P f) : P.RepFun where
  toFun := f
  apply_eq_self_of_notMem := hf.apply_of_notMem
  rel_apply_of_mem := hf.rel_apply
  apply_eq_of_rel := hf.apply_eq_apply

end IsRepFun

/-- Convert a `RepFun` to an `IsRepFun` proof. -/
lemma RepFun.isRepFun (rf : P.RepFun) : IsRepFun P rf where
  apply_of_notMem := rf.apply_eq_self_of_notMem
  rel_apply := rf.rel_apply_of_mem
  apply_eq_apply := rf.apply_eq_of_rel

end IsRepFun


-- lemma RepFun.image_eq_of_forall_rel_imp_eq (h : ∀ ⦃x y⦄, x ∈ s → y ∈ s → P x y → x = y)


-- /-- If `a ∈ s`, noncomputably choose an element in the same cell of `P` as some `a : α`.
-- If `a ∉ s`, is equal to `a`. -/
-- noncomputable def rep' (P : Partition (Set α)) (a : α) : α :=
--     if h : a ∈ s then P.rep (P.partOf_mem h) else a

-- lemma rep'_eq_rep (P : Partition (Set α)) (ha : a ∈ s) : P.rep' a = P.rep (P.partOf_mem ha) := by
--   rw [rep', dif_pos ha]

-- lemma rel_rep' (P : Partition (Set α)) (ha : a ∈ s) : P a (P.rep' a) := by
--   rw [P.rep'_eq_rep ha]
--   exact P.rep_rel (P.partOf_mem ha) (P.mem_partOf ha)

-- lemma rep'_eq_self_of_notMem (P : Partition (Set α)) (ha : a ∉ s) : P.rep' a = a := by
--   rw [rep', dif_neg ha]

-- lemma rel_iff_rep'_eq_rep' (ha : a ∈ s) (hb : b ∈ s) : P a b ↔ P.rep' a = P.rep' b := by
--   refine ⟨fun h ↦ ?_, fun h ↦ (P.rel_rep' ha).trans (h.symm ▸ P.rel_rep' hb).symm ⟩
--   rw [P.rel_iff_partOf_eq_partOf ha hb] at h
--   rw [P.rep'_eq_rep ha, P.rep'_eq_rep hb]
--   congr
