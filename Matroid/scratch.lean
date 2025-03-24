import Mathlib.Topology.UnitInterval
import Mathlib.Analysis.InnerProductSpace.PiL2

variable {α R K M : Type*} {n : ℕ} [Ring R] [Field K] [AddCommGroup M] [Module K M]

variable {x y z : EuclideanSpace ℝ (Fin n)}

section List

lemma List.reverse_sorted (R : α → α → Prop) (L : List α) :
    L.reverse.Sorted R ↔ L.Sorted (flip R) := by
  induction L with
  | nil => simp
  | cons head tail ih =>
  simp only [List.reverse_cons, List.sorted_cons, ← ih]
  simp [List.Sorted, List.pairwise_append, flip, and_comm]

lemma List.sorted_append (R : α → α → Prop) (L₁ L₂ : List α) :
    (L₁ ++ L₂).Sorted R ↔ L₁.Sorted R ∧ L₂.Sorted R ∧ ∀ a ∈ L₁, ∀ b ∈ L₂, R a b := by
  rw [Sorted, pairwise_append]

end List

open unitInterval


section ConvexComb


def convComb {M : Type*} [Add M] [SMul ℝ M] (a b : M) (t : unitInterval) : M :=
  (symm t).1 • a + t.1 • b

@[simp]
lemma convComb_symm {M : Type*} [AddCommMonoid M] [SMul ℝ M] (a b : M) (t : unitInterval) :
    convComb a b (σ t) = convComb b a t := by
  simp [convComb, add_comm]

end ConvexComb


noncomputable def unitInterval.half : I := ⟨1/2, by simp; linarith⟩

@[simp] lemma unitInterval.zero_lt_half : 0 < half := by
  simp [half, ← Subtype.coe_lt_coe]

@[simp] lemma unitInterval.half_lt_one : half < 1 := by
  simp only [half, one_div, ← Subtype.coe_lt_coe, Set.Icc.coe_one]
  linarith


def unitInterval.between (a b t : I) : I :=
  ⟨convComb a.1 b.1 t, by
    simp only [coe_symm_eq, smul_eq_mul, Set.mem_Icc, convComb]
    constructor
    · calc 0 = 0 * a.1 + 0 * b.1 := by simp
           _ ≤ _ := by gcongr <;> unit_interval
    calc _ ≤ (1 - t.1) * 1 + t.1 * 1 := by gcongr <;> unit_interval
         _ ≤ 1                       := by linarith ⟩

@[simp] lemma between_apply (a b t : I) :
    between a b t = (1 - t.1) * a.1 + t * b.1 := rfl

@[simp]
lemma unitInterval.symm_between (a b t : I) : σ (between a b t) = between (σ a) (σ b) t := by
  simp only [symm, between, convComb, smul_eq_mul, Subtype.mk.injEq]
  ring

lemma unitInterval.between_symm (a b t : I) : between a b (σ t) = between b a t := by
  simp only [symm, between, convComb, smul_eq_mul, Subtype.mk.injEq]
  ring

lemma unitInterval.between_strictMono {a b : I} (hab : a < b) : StrictMono (between a b) := by
  intro s t hst
  rw [← Subtype.coe_lt_coe]
  simp only [between_apply]
  suffices a.1 + s.1 * (b.1 - a.1) < a.1 + t.1 * (b.1 - a.1) by linarith
  simp only [add_lt_add_iff_left]
  gcongr
  simpa

@[simp]
lemma unitInterval.between_one (a b : I) : between a b 1 = b := by
  simp [← Subtype.val_inj]

@[simp]
lemma unitInterval.between_zero (a b : I) : between a b 0 = a := by
  simp [← Subtype.val_inj]

lemma unitInterval.left_le_between {a b : I} (hab : a < b) (t : I) : a ≤ between a b t := by
  nth_rw 1 [← between_zero a b]
  exact (between_strictMono hab).monotone <| nonneg t

lemma unitInterval.between_le_right {a b : I} (hab : a < b) (t : I) : between a b t ≤ b := by
  nth_rw 2 [← between_one a b]
  exact (between_strictMono hab).monotone <| le_one t

lemma convComb_convComb (a b : M) (s t r : I) :
    convComb (convComb a b s) (convComb a b t) r = convComb a b (between s t r)

lemma unitInterval.between_between (a b s t r : I) :
    between (between a b s) (between a b t) r = between a b (between s t r) := by
  simp [← Subtype.coe_inj, between_apply]
  ring

structure PolygonParam' {x y : EuclideanSpace ℝ (Fin n)} (P : Path x y) where
  length : ℕ
  c : Fin (length + 1) → I
  strictMono : StrictMono c
  piecewiseLinear : ∀ (i : Fin length) (t : I),
    P (between (c i.castSucc) (c i.succ) t) = convComb (P (c i.castSucc)) (P (c i.succ)) t


structure PolygonParam (P : Path x y) where
  corners : List I
  ne_nil : corners ≠ []
  head_eq : List.head corners ne_nil = 0
  last_eq : List.getLast corners ne_nil = 1
  sorted : List.Sorted (· ≤ ·) corners
  piecewiseLinear :
    corners.Chain' (fun c₁ c₂ ↦ ∀ t : I, P (between c₁ c₂ t) = convComb (P c₁) (P c₂) t)

  -- ∀ {c} (t : I),
  --   c ∈ corners.zip corners.tail →
  --   P (between c.1 c.2 t) = convComb (P c.1) (P c.2) t

def PolygonParam.symm {P : Path x y} (lP : PolygonParam P) : PolygonParam P.symm where
  corners := (lP.corners.map unitInterval.symm).reverse
  sorted := by
    rw [List.reverse_sorted, Function.flip_def, strictAnti_symm.sorted_ge_listMap]
    exact lP.sorted
  ne_nil := by simp [lP.ne_nil]
  head_eq := by simp [lP.last_eq]
  last_eq := by simp [lP.head_eq]
  piecewiseLinear := by
    simp only [Path.symm_apply, Function.comp_apply, Set.mem_Icc]
    rw [List.chain'_reverse, List.chain'_map]
    simp only [flip, symm_symm, symm_between]
    convert lP.piecewiseLinear using 3 with a b
    apply symmHomeomorph.toEquiv.forall_congr
    simp only [Homeomorph.coe_toEquiv, symmHomeomorph_apply, between_symm, convComb_symm,
      implies_true]

noncomputable def PolygonParam.trans {x y z : EuclideanSpace ℝ (Fin n)} {P : Path x y}
    {Q : Path y z} (lP : PolygonParam P) (lQ : PolygonParam Q) : PolygonParam (P.trans Q) where
  corners := (lP.corners.map (between 0 half)) ++ (lQ.corners.map (between half 1))
  ne_nil := by simp [lP.ne_nil]
  head_eq := by simp [List.head_append, lP.ne_nil, lP.head_eq, between, convComb]


  last_eq := by simp [List.getLast_append, lQ.ne_nil, between, convComb, lQ.last_eq]
  sorted := by
    rw [List.sorted_append, (between_strictMono zero_lt_half).sorted_le_listMap,
      (between_strictMono half_lt_one).sorted_le_listMap, and_iff_right lP.sorted,
      and_iff_right lQ.sorted]
    simp only [one_div, List.mem_map,  forall_exists_index, and_imp, Subtype.mk_le_mk]
    rintro a t ht rfl b s hs rfl
    exact (between_le_right (by simp) _).trans (left_le_between (by simp) _)


  piecewiseLinear := by
    simp_rw [List.chain'_append, List.chain'_map]
    simp only [List.getLast?_map, Option.mem_def, Option.map_eq_some', List.head?_map,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, between_between]


  -- c : Fin (length + 1) → unitInterval
  -- strictMono : StrictMono c
  -- piecewiseLinear : ∀ (i : Fin length) (t : unitInterval),
  --   P (between (c i.castSucc) (c i.succ) t) = convComb (P (c i.castSucc)) (P (c i.succ)) t

-- def IsPolygonal {x y : EuclideanSpace ℝ (Fin n)} (P : Path x y) : Prop :=
--     ∃ (k : ℕ) (c : Fin (k + 1) → unitInterval), ∀ (i : Fin k) (t : unitInterval),
--       P (between (c i.castSucc) (c i.succ) t) = convComb (P (c i.castSucc)) (P (c i.succ)) t
