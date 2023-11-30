import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Logic.Equiv.LocalEquiv
import Matroid.ForMathlib.LocalEquiv
import Mathlib.Data.Nat.Digits

#find (ℕ ≃ Finset ℕ)

open Set SimpleGraph Function LocalEquiv BigOperators

variable {V V W : Type*} {s : Set V} {t : Set W} {G : SimpleGraph V} {H : SimpleGraph W}

@[simp] theorem SimpleGraph.Iso.coe_symm (e : G ≃g H) : e.toEquiv.symm = e.symm.toEquiv := rfl

section PartialIso

/-- A `PartialIso G H s t` is an isomorphism between some induced subgraph of `G` containing `s`,
  and an induced subgraph of `H` containing `t`. Implemented as a `LocalEquiv`. -/
structure PartialIso (G : SimpleGraph V) (H : SimpleGraph W) (s : Set V) (t : Set W) where
  (φ : LocalEquiv V W)
  (hs : s ⊆ φ.source)
  (ht : t ⊆ φ.target)
  (finite : φ.source.Finite)
  (adj_iff : ∀ {i j}, i ∈ φ.source → j ∈ φ.source → (G.Adj i j ↔ H.Adj (φ i) (φ j)))

/-- Reversing a `PartialIso G H s t` gives a `PartialIso H G t s`. -/
def PartialIso.symm (e : PartialIso G H s t) : PartialIso H G t s where
  φ := e.φ.symm
  hs := e.ht
  ht := e.hs
  finite := by
    rw [e.φ.symm_source, ← e.φ.image_source_eq_target]
    exact e.finite.image _
  adj_iff := by
    rintro i j (hi : i ∈ e.φ.target) (hj : j ∈ e.φ.target)
    rw [e.adj_iff (e.φ.map_target hi) (e.φ.map_target hj), e.φ.right_inv hi, e.φ.right_inv hj]

end PartialIso

section ExtensionProperty

def ExtensionProperty (G : SimpleGraph V) : Prop :=
  ∀ A B : Finset V, Disjoint A B →
    ∃ x, x ∉ A ∧ x ∉ B ∧ ((∀ v ∈ A, G.Adj v x) ∧ (∀ v ∈ B, ¬ G.Adj v x))

theorem ExtensionProperty.infinite {G : SimpleGraph V} (hG : ExtensionProperty G) : Infinite V := by
  rw [← infinite_univ_iff]
  intro hfin
  obtain ⟨x, hx, -⟩ := hG hfin.toFinset ∅ (by simp)
  simp at hx

theorem ExtensionProperty.map_iso (hG : ExtensionProperty G) (e : G ≃g H) :
    ExtensionProperty H := by
  intro A B hAB
  obtain ⟨x, hx⟩ := hG (A.map e.symm.1.toEmbedding) (B.map e.symm.1.toEmbedding)
    (by simpa using hAB)
  use e x
  simp only [Iso.symm, RelIso.symm, Finset.mem_map_equiv, Equiv.symm_symm, RelIso.coe_toEquiv] at hx
  refine ⟨hx.1, hx.2.1, fun v hvA ↦ ?_, fun v hvB ↦ ?_⟩
  · rw [← e.symm.map_adj_iff]
    simpa using hx.2.2.1 (e.symm v) (by simpa)
  rw [← e.symm.map_adj_iff]
  simpa using hx.2.2.2 (e.symm v) (by simpa)

theorem ExtensionProperty.extend_partialIso (hH : ExtensionProperty H) (e : PartialIso G H s t)
    (a : V) : ∃ (e' : PartialIso G H (insert a s) t), e.φ ≤ e'.φ := by
  classical
  by_cases ha : a ∈ e.φ.source
  · refine ⟨⟨e.φ, insert_subset ha e.hs, e.ht, e.finite, e.adj_iff⟩, ⟨rfl.le,by simp⟩⟩
  specialize hH ((e.finite.inter_of_left {i | G.Adj a i}).image e.φ).toFinset
      ((e.finite.inter_of_left {i | ¬ G.Adj a i}).image e.φ).toFinset ?_
  · simp only [Finite.disjoint_toFinset, disjoint_iff_forall_ne, mem_image, mem_inter_iff,
      mem_setOf_eq, forall_exists_index, and_imp]
    rintro _ x hx h rfl _ y hy h' rfl h_eq
    obtain rfl := e.φ.injOn hx hy h_eq
    exact h' h
  simp only [Finite.mem_toFinset, mem_image, mem_inter_iff, mem_setOf_eq, not_exists, not_and,
    and_imp, forall_exists_index] at hH
  obtain ⟨b, hbA, hbB, hb⟩ := hH
  have hbt : b ∉ e.φ.target
  · exact fun hb ↦
      by_cases (hbA _ (e.φ.map_target hb)) (hbB _ (e.φ.map_target hb)) (e.φ.right_inv hb)
  refine ⟨⟨e.φ.insert ha hbt, insert_subset_insert e.hs, e.ht.trans (subset_insert _ _), ?_, ?_⟩,?_⟩
  · simp [e.finite.insert _]
  · simp only [LocalEquiv.insert_source, mem_insert_iff]
    rintro i j (rfl | hi)
    · rw [e.φ.insert_apply, update_same]
      rintro (rfl | hj)
      · simp
      rw [e.φ.insert_apply_mem _ _ hj]
      exact ⟨fun h ↦ (hb.1 _ _ hj h rfl).symm, fun h ↦ by_contra fun h' ↦ hb.2 _ _ hj h' rfl h.symm⟩
    rintro (rfl | hj)
    · rw [e.φ.insert_apply_mem _ _ hi, e.φ.insert_apply, update_same]
      refine ⟨fun h ↦ hb.1 _ _ hi h.symm rfl, fun h ↦ by_contra fun h' ↦ (hb.2 _ _ hi ?_ rfl) h⟩
      exact fun h'' ↦ h' h''.symm
    rw [e.φ.insert_apply_mem _ _ hi, e.φ.insert_apply_mem _ _ hj, e.adj_iff hi hj]
  simp only
  exact (e.φ.lt_insert _ _).le

theorem ExtensionProperty.extend_extend {G H : SimpleGraph ℕ}
    (hG : ExtensionProperty G) (hH : ExtensionProperty H)
    (n : ℕ) (e : PartialIso G H (Iio n) (Iio n)) :
    ∃ (e' : PartialIso G H (Iio (n+1)) (Iio (n+1))), e.φ ≤ e'.φ := by
  obtain ⟨e1, he1⟩ := hH.extend_partialIso e n
  obtain ⟨e2, he2⟩ := hG.extend_partialIso e1.symm n
  refine ⟨⟨e2.φ.symm, ?_, ?_, e2.symm.finite, fun hi hj ↦ e2.symm.adj_iff hi hj⟩, ?_⟩
  · convert e2.ht using 1; ext; simp [Nat.lt_add_one_iff]
  · convert e2.hs using 1; ext; simp [Nat.lt_add_one_iff]
  simp only
  rw [← symm_le_symm_iff_le, symm_symm]
  exact (symm_le_symm_of_le he1).trans he2

theorem toSeq (W : ℕ → Type*) (P : ∀ {i}, W i → W (i+1) → Prop) (b0 : W 0)
    (h : ∀ i (b : W i), ∃ (b' : W (i+1)), P b b') :
    ∃ (bs : ∀ n, W n), bs 0 = b0 ∧ ∀ i, P (bs i) (bs (i+1)) := by
  choose f hf using h; exact ⟨fun t ↦ @Nat.recOn W t b0 f, rfl, fun i ↦ hf _ _⟩

/-- Any partial isomorphism of two graphs with the extension property extends to an isomorphism. -/
theorem ExtensionProperty.exists_extend_iso_nat {G H : SimpleGraph ℕ} (hG : ExtensionProperty G)
    (hH : ExtensionProperty H) (e0 : PartialIso G H ∅ ∅) :
    ∃ (e : G ≃g H), ∀ i ∈ e0.1.source, e i = e0.1 i := by
  have h0 : (Iio 0 : Set ℕ) = ∅ := by ext; simp
  set e0' : PartialIso G H (Iio 0) (Iio 0) :=
    ⟨e0.φ, by simp [h0], by simp [h0], e0.finite, e0.adj_iff⟩
  obtain ⟨es, he0, hes⟩ := toSeq
    (fun n ↦ PartialIso G H (Iio n) (Iio n)) _ e0' (extend_extend hG hH)
  have h_strong' : ∀ {i j}, i ≤ j → (es i).φ ≤ (es j).φ
  · intro i j hij
    obtain ⟨d,rfl⟩ := exists_add_of_le hij
    induction' d with d IH
    · simp
    rw [Nat.succ_eq_add_one, ← add_assoc]
    exact (IH (by simp)).trans (hes _)
  have h_le : ∀ {i j : ℕ}, i ≤ j → (es (i+1)).1 i = (es (j+1)).1 i := fun {i j} hij ↦ by
    rw [eq_of_mem_source (h_strong' (add_le_add_right hij 1)) ((es (i+1)).hs (by simp))]

  set f := fun i ↦ (es (i+1)).1 i
  have hf_def : ∀ i, f i = (es (i+1)).1 i := fun _ ↦ rfl

  refine ⟨⟨Equiv.ofBijective f ⟨fun i j hij ↦ ?_, fun j ↦ ?_⟩, ?_⟩, ?_⟩
  · rw [hf_def, h_le (le_max_left i j), hf_def, h_le (le_max_right i j)] at hij
    exact (es (max i j + 1)).1.injOn ((es (max i j +1)).hs (by simp [Nat.lt_add_one_iff]))
      ((es (max i j +1)).hs (by simp [Nat.lt_add_one_iff])) hij
  · use (es (j+1)).1.symm j
    rw [hf_def, h_le (le_max_right j ((es (j+1)).φ.symm j)),
      LocalEquiv.eq_of_mem_source (h_strong' (add_le_add_right (le_max_left _ _) 1)),
      LocalEquiv.right_inv _ ((es (j+1)).ht (by simp))]
    exact (es (j+1)).φ.map_target ((es (j+1)).ht (by simp))
  · simp only [Equiv.ofBijective_apply]
    intro a b
    rw [h_le (le_max_left a b), h_le (le_max_right a b), (es (max a b + 1)).adj_iff]
    <;> apply (es (max a b +1)).hs (by simp [Nat.lt_add_one_iff])
  intro i hi
  simp only [RelIso.coe_fn_mk, Equiv.ofBijective_apply]
  rw [eq_of_mem_source (h_strong' (zero_le (i+1))) (by simpa [he0]), he0]

theorem ExtensionProperty.exists_extend_iso [Countable V] [Countable W] (hG : ExtensionProperty G)
    (hH : ExtensionProperty H) (e0 : PartialIso G H ∅ ∅) :
    ∃ (e : G ≃g H), ∀ i ∈ e0.1.source, e i = e0.1 i := by
  have _ := hG.infinite
  have _ := hH.infinite
  obtain ⟨eV⟩ := nonempty_equiv_of_countable (α := V) (β := ℕ)
  obtain ⟨eW⟩ := nonempty_equiv_of_countable (α := W) (β := ℕ)
  set eG' := SimpleGraph.Iso.map eV G
  set eH' := SimpleGraph.Iso.map eW H
  set G' := G.map eV.toEmbedding
  set H' := H.map eW.toEmbedding
  set φ := ((e0.φ.transEquiv eH'.toEquiv).symm.transEquiv eG'.toEquiv).symm
  have hfin : φ.source.Finite
  · rw [symm_source, ← image_source_eq_target, transEquiv_source, symm_source,
      ← image_source_eq_target, transEquiv_source]
    apply Finite.image _ (Finite.image _ e0.finite)
  have h_adj : ∀ {i j}, i ∈ φ.source → j ∈ φ.source → (Adj G' i j ↔ Adj H' (φ i) (φ j))
  · intro i j hi hj
    simp only [symm_source, transEquiv_target, Iso.coe_symm, RelIso.coe_toEquiv, symm_target,
      transEquiv_source, mem_preimage] at hi hj
    rw [← eH'.symm.map_adj_iff, ← eG'.symm.map_adj_iff, e0.adj_iff hi hj]
    simp
  obtain ⟨(e' : G' ≃g H'), he'⟩ := exists_extend_iso_nat (hG.map_iso eG') (hH.map_iso eH')
    ⟨φ, by simp, by simp, hfin, h_adj⟩
  refine ⟨(eG'.trans e').trans eH'.symm, fun i hi ↦ ?_⟩
  simp only [symm_source, transEquiv_target, symm_target, transEquiv_source, mem_preimage,
    transEquiv_symm_apply, symm_symm, transEquiv_apply, RelIso.coe_toEquiv] at he'
  simp [he' (eG' i) (by simpa)]

theorem ExtensionProperty.iso_of_countable [Countable V] [Countable W] (hG : ExtensionProperty G)
    (hH : ExtensionProperty H) : Nonempty (G ≃g H) := by
  have _ := hG.infinite
  have _ := hH.infinite
  have e0 : PartialIso G H ∅ ∅ :=
    ⟨(injOn_empty (fun _ : V ↦ Classical.arbitrary W)).toLocalEquiv,
      by simp, by simp, by simp, by simp⟩
  obtain ⟨e,-⟩ := hG.exists_extend_iso hH e0
  exact ⟨e⟩

-- theorem ExtensionProperty.exists_of_finite_partition {n : ℕ} (hG : ExtensionProperty G)
--     (f : V → Fin n) : ∃ i, ExtensionProperty (G.induce (f ⁻¹' {i})) := by
--   simp_rw [ExtensionProperty]
--   by_contra' h
--   choose As Bs hdj hABs using h



end ExtensionProperty
