import Matroid.Graph.Planarity.Realization.Basic

open Set Function TopologicalSpace Topology Relation UniformSpace Sum Path WList Classical ENNReal
open scoped unitInterval

private lemma norm_le_one_iff_fin_1 (x : Fin 1 → ℝ) : ‖x‖ ≤ 1 ↔ ‖x 0‖ ≤ 1 := by simp [Pi.norm_def]
private lemma norm_lt_one_iff_fin_1 (x : Fin 1 → ℝ) : ‖x‖ < 1 ↔ ‖x 0‖ < 1 := by simp [Pi.norm_def]
private lemma norm_eq_one_iff_fin_1 (x : Fin 1 → ℝ) : ‖x‖ = 1 ↔ ‖x 0‖ = 1 := by simp [Pi.norm_def]

private lemma metric_sphere_fin_one_eq : Metric.sphere (0 : Fin 1 → ℝ) 1 = {-1, 1} := by
  ext f
  simp only [mem_sphere_iff_norm, sub_zero, mem_insert_iff, mem_singleton_iff,
    norm_eq_one_iff_fin_1, Real.norm_eq_abs]
  refine ⟨fun hf ↦ ((abs_eq (zero_le_one' ℝ)).1 hf).symm.imp ?_ ?_, by rintro (rfl | rfl) <;> simp⟩
  <;>
  · intro h0
    ext i
    fin_cases i
    simp [h0]

namespace Graph

universe u v

variable {α : Type u} {β : Type v} {G : Graph α β} {e : E(G)} {t₁ t₂ : I}

def Realization.cell (G : Graph α β) : ℕ → Type (max u v)
  | 0 => ULift.{v, u} V(G)
  | 1 => ULift.{u, v} E(G)
  | _ + 2 => ULift.{max u v, 0} Empty

@[simps]
def partialEquivVertexMk (v : V(G)) : PartialEquiv (Fin 0 → ℝ) G.Realization where
  toFun x := vertexMk v
  invFun v := 0
  source := Metric.ball 0 1
  target := {vertexMk v}
  map_source' _ _ := rfl
  map_target' := by simp
  left_inv' _ _ := Subsingleton.elim _ _
  right_inv' _ hx := hx.symm

@[simps]
noncomputable def partialEquivEdgeMk (e' : E(G)) : PartialEquiv (Fin 1 → ℝ) G.Realization where
  toFun f := edgePath e' ⟨max 0 (min 1 ((f 0 + 1) / 2)), by simp [zero_le_one]⟩
  invFun x :=
    if h : x ∈ edgePath e' '' Ioo 0 1 then
      fun _ ↦ 2 * (Classical.choose h).val - 1
    else 0
  source := Metric.ball 0 1
  target := edgePath e' '' Ioo 0 1
  map_source' x hx := by
    simp only [Metric.mem_ball, dist_zero_right, norm_lt_one_iff_fin_1, Fin.isValue,
      Real.norm_eq_abs, abs_lt] at hx
    refine ⟨⟨_, by simp [zero_le_one]⟩, ?_, rfl⟩
    change (0 : ℝ) < _ ∧ _ < (1 : ℝ)
    simp only [Fin.isValue, left_lt_sup, inf_le_iff, not_or, not_le, zero_lt_one, Nat.ofNat_pos,
      div_pos_iff_of_pos_right, true_and, sup_lt_iff, inf_lt_left]
    constructor <;> linarith
  map_target' x hx := by
    simp only [hx, ↓reduceDIte, Metric.mem_ball, dist_zero_right, norm_lt_one_iff_fin_1,
      Real.norm_eq_abs]
    obtain ⟨⟨(ht1 : (0 : ℝ) < _), (ht2 : _ < (1 : ℝ))⟩, ht_eq⟩ := Classical.choose_spec hx
    refine abs_lt.mpr ⟨?_, ?_⟩ <;> linarith
  left_inv' := fun x hx ↦ by
    simp only [Metric.mem_ball, dist_zero_right, norm_lt_one_iff_fin_1, Real.norm_eq_abs,
      abs_lt] at hx
    have h_mem : edgePath e' ⟨max 0 (min 1 ((x 0 + 1) / 2)), by simp [zero_le_one]⟩ ∈
        edgePath e' '' Ioo 0 1 := by
      refine ⟨⟨_, by simp [zero_le_one]⟩, (?_ : (0 : ℝ) < _ ∧ _ < (1 : ℝ)), rfl⟩
      clear t₁ t₂ e; grind
    simp only [h_mem, ↓reduceDIte]
    ext i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    obtain ⟨⟨(ht1 : (0 : ℝ) < _), (ht2 : _ < (1 : ℝ))⟩, ht_eq⟩ := Classical.choose_spec h_mem
    clear t₁ t₂ e; grind [edgePath_inj_on_Ioo ⟨ht1, ht2⟩ ht_eq]
  right_inv' x' hx' := by
    simp only [hx', ↓reduceDIte]
    obtain ⟨⟨(ht1 : (0 : ℝ) < _), (ht2 : _ < (1 : ℝ))⟩, _⟩ := Classical.choose_spec hx'
    clear t₁ t₂ e; grind

noncomputable def Realization.map (G : Graph α β) :
    ∀ n, Realization.cell G n → PartialEquiv (Fin n → ℝ) G.Realization
  | 0, ⟨v⟩ => partialEquivVertexMk v
  | 1, ⟨e⟩ => partialEquivEdgeMk e
  | _ + 2, ⟨i⟩ => Empty.elim i

lemma continuous_partialEquivEdgeMk (e : E(G)) : Continuous (partialEquivEdgeMk e) :=
  (edgePath e).continuous.comp <| (continuous_const.max <| continuous_const.min
  <| continuous_apply 0 |>.add continuous_const |>.div_const _).subtype_mk _

lemma continuousOn_quotient {Y : Type*} [TopologicalSpace Y] (U : Set G.Realization) (hU : IsOpen U)
    (f : G.Realization → Y) (hf : ContinuousOn (f ∘ Quotient.mk') (Quotient.mk' ⁻¹' U)) :
    ContinuousOn f U := by
  rw [continuousOn_open_iff hU]
  exact (continuousOn_open_iff (hU.preimage continuous_quotient_mk')).mp hf

lemma image_map_closedBall (e : E(G)) :
    Realization.map G 1 ⟨e⟩ '' Metric.closedBall 0 1 = range (edgePath e) := by
  ext x
  simp only [Realization.map, mem_image, Metric.mem_closedBall, dist_zero_right,
    partialEquivEdgeMk_apply]
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨⟨max 0 (min 1 ((f 0 + 1) / 2)), by simp [zero_le_one]⟩, rfl⟩
  rintro ⟨⟨t, ht1, ht2⟩, rfl⟩
  use fun _ ↦ 2 * t - 1, ?_, by simp [ht1, ht2]
  rw [norm_le_one_iff_fin_1, Real.norm_eq_abs, abs_le]
  grind

noncomputable instance : Topology.CWComplex (univ : Set G.Realization) where
  cell := Realization.cell G
  map := Realization.map G
  source_eq n i := match n, i with
  | 0, ⟨_⟩ => rfl
  | 1, ⟨_⟩ => rfl
  | _ + 2, ⟨i⟩ => Empty.elim i
  continuousOn n i := match n, i with
  | 0, ⟨_⟩ => continuous_const.continuousOn
  | 1, ⟨e⟩ => (continuous_partialEquivEdgeMk ..).continuousOn
  | _ + 2, ⟨i⟩ => Empty.elim i
  continuousOn_symm n i := match n, i with
  | 0, ⟨_⟩ => continuous_const.continuousOn
  | 1, ⟨e⟩ => by
    change ContinuousOn (partialEquivEdgeMk e).invFun (edgePath e '' Ioo (0 : I) (1 : I))
    refine continuousOn_quotient _ ?_ _ ?_
    · rw [isOpen_edgePath_image e (by simp) (by simp)]
      exact isOpen_Ioo
    rw [edgePath_preimage_image e (by simp) (by simp)]
    let f_pre : G.PreRealization → Fin 1 → ℝ := fun x ↦ match x with
    | Sum.inl _ => 0
    | Sum.inr ⟨e', t'⟩ => fun _ ↦ 2 * t' - 1
    have h_f_pre_cont : Continuous f_pre := by
      refine continuous_sum_dom.mpr ⟨continuous_of_discreteTopology, continuous_pi fun i ↦ ?_⟩
      exact (continuous_const.mul <| continuous_subtype_val.comp Sigma.continuous_snd).sub
        continuous_const
    refine ContinuousOn.congr h_f_pre_cont.continuousOn fun x hx ↦ ?_
    ext i
    simp only [mem_image, Sigma.exists, Sigma.mk.injEq, heq_eq_eq, exists_eq_right_right] at hx
    obtain ⟨e', t', ⟨ht', rfl⟩, rfl⟩ := hx
    have h_mem : Quotient.mk' _ ∈ edgePath e '' Ioo (0 : I) (1 : I) := ⟨t', ht', rfl⟩
    simp only [h_mem, ↓reduceDIte, comp_apply, partialEquivEdgeMk, f_pre,
      ← edgePath_inj_on_Ioo ht' h_mem.choose_spec.2.symm]
  | _ + 2, ⟨i⟩ => Empty.elim i
  pairwiseDisjoint' := by
    rintro ⟨n₁, i₁⟩ _ ⟨n₂, i₂⟩ _ hne
    have he : ∀ e : E(G), _ '' (Metric.ball 0 1 : Set <| Fin 1 → ℝ) = edgePath e '' Ioo 0 1 :=
      (partialEquivEdgeMk · |>.image_source_eq_target)
    have hv : ∀ v : V(G), _ '' (Metric.ball 0 1 : Set <| Fin 0 → ℝ) = {vertexMk v} :=
      (partialEquivVertexMk · |>.image_source_eq_target)
    match n₁, i₁, n₂, i₂ with
    | 0, ⟨v₁⟩, 0, ⟨v₂⟩ =>
      replace hne : v₁ ≠ v₂ := by tauto
      simpa [Realization.map, Function.onFun, hv]
    | 0, ⟨v₁⟩, 1, ⟨e₂⟩ =>
      simp only [Realization.map, Function.onFun, he, hv, disjoint_singleton_left]
      exact vertexMk_notMem_edgePath_Ioo v₁ e₂
    | 1, ⟨e₁⟩, 0, ⟨v₂⟩ =>
      simp only [Realization.map, Function.onFun, he, hv, disjoint_singleton_right]
      exact vertexMk_notMem_edgePath_Ioo v₂ e₁
    | 1, ⟨e₁⟩, 1, ⟨e₂⟩ =>
      replace hne : e₁ ≠ e₂ := by tauto
      simpa only [Realization.map, Function.onFun, he, edgePath_Ioo_disjoint_iff_ne]
    | n₁ + 2, ⟨i₁⟩, _, _ => exact Empty.elim i₁
    | _, _, n₂ + 2, ⟨i₂⟩ => exact Empty.elim i₂
  mapsTo' n i :=
    match n, i with
    | 0, ⟨v⟩ => by
      refine ⟨fun _ ↦ ∅, fun _ ↦ ?_⟩
      simp [mem_sphere_iff_norm, norm_eq_zero_of_subsingleton]
    | 1, ⟨e⟩ => by
      refine ⟨fun m ↦ match m with | 0 => {⟨src e⟩, ⟨tgt e⟩} | _ => ∅, fun x hx ↦ ?_⟩
      simp only [mem_sphere_iff_norm, sub_zero, norm_eq_one_iff_fin_1, Fin.isValue,
        Real.norm_eq_abs, zero_le_one, abs_eq] at hx
      obtain hx | hx := hx <;> simp [hx, Realization.map]
    | n + 2, ⟨i⟩ => Empty.elim i
  closed' A _ h := by
    rw [isClosed_coinduced, isClosed_sum_iff, isClosed_sigma_iff]
    refine ⟨isClosed_discrete _, fun e ↦ ?_⟩
    simpa [image_map_closedBall] using (h 1 ⟨e⟩).preimage (edgePath e).continuous
  union' := by
    ext x
    simp only [mem_iUnion, mem_univ, iff_true]
    refine Quotient.inductionOn x fun x ↦ ?_
    match x with
    | inl v => exact ⟨0, ⟨v⟩, by simp [Realization.map, vertexMk, Quotient.mk']⟩
    | inr ⟨e, t⟩ =>
      refine ⟨1, ⟨e⟩, ?_⟩
      rw [image_map_closedBall, mem_range]
      exact ⟨t, rfl⟩

end Graph
