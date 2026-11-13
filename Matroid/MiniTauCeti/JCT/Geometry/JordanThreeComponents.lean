module

public import Matroid.MiniTauCeti.JCT.Geometry.PrimitiveLinkTripod
public import Matroid.MiniTauCeti.JCT.Topology.Circuit.CompactParametrization
public import Matroid.MiniTauCeti.JCT.Topology.ConnectedComponent
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Three complementary components and a bipartite configuration
-/

@[expose] public section

open Set Topology Function
open scoped unitInterval

namespace JordanConfigurations

private theorem exists_open_interval_target {x : ℂ} {P : Path x x}
    (hP : P.IsSimpleLoop) {s t : I} (hs : 0 < s) (ht : t < 1) :
    ∃ O : Set ℂ, IsOpen O ∧ O ∩ range P = P '' Ioo s t := by
  let f : Ioo (0 : I) 1 → range P := fun u ↦ ⟨P u, mem_range_self (u : I)⟩
  have hf := hP.isPrimitive.isOpenEmbedding_interior
  let A : Set (Ioo (0 : I) 1) := Subtype.val ⁻¹' Ioo s t
  have hA : IsOpen A := isOpen_Ioo.preimage continuous_subtype_val
  obtain ⟨O, hO, heq⟩ := isOpen_induced_iff.mp (hf.isOpenMap A hA)
  refine ⟨O, hO, ?_⟩
  ext z
  constructor
  · rintro ⟨hzO, hzP⟩
    have hz : (⟨z, hzP⟩ : range P) ∈ f '' A := heq ▸ hzO
    obtain ⟨u, hu, hzu⟩ := hz
    exact ⟨u, hu, congrArg Subtype.val hzu⟩
  · rintro ⟨u, hu, rfl⟩
    have hu01 : u ∈ Ioo (0 : I) 1 := ⟨hs.trans hu.1, hu.2.trans ht⟩
    have : (⟨P u, mem_range_self u⟩ : range P) ∈ f '' A := ⟨⟨u, hu01⟩, hu, rfl⟩
    refine ⟨?_, mem_range_self u⟩
    change (⟨P u, mem_range_self u⟩ : range P) ∈ Subtype.val ⁻¹' O
    rwa [heq]

private theorem three_interval_inter {t : Fin 3 → I} (ht : StrictMono t)
    {i j : Fin 3} (hij : i ≠ j) : uIcc (t i) (t 1) ∩ uIcc (t j) (t 1) = {t 1} := by
  have h01 := ht (show (0 : Fin 3) < 1 by decide)
  have h12 := ht (show (1 : Fin 3) < 2 by decide)
  ext u
  simp only [mem_inter_iff, mem_uIcc, mem_singleton_iff]
  fin_cases i <;> fin_cases j <;> grind

private theorem three_interval_endpoint {t : Fin 3 → I} (ht : StrictMono t)
    {i j : Fin 3} (hi : t i ∈ uIcc (t j) (t 1)) : i = j ∨ i = 1 := by
  have h01 := ht (show (0 : Fin 3) < 1 by decide)
  have h12 := ht (show (1 : Fin 3) < 2 by decide)
  fin_cases i <;> fin_cases j <;> simp_all only [mem_uIcc] <;> grind

private theorem grid_interval_subset {t : Fin 3 → Fin 3 → I}
    (ht : ∀ j, StrictMono (fun i ↦ t i j)) (i j : Fin 3) :
    uIcc (t i j) (t 1 j) ⊆ Icc (t 0 j) (t 2 j) := by
  apply uIcc_subset_Icc
  · exact ⟨(ht j).monotone (Fin.zero_le i), (ht j).monotone (by omega)⟩
  · exact ⟨(ht j).monotone (by decide), (ht j).monotone (by decide)⟩

private theorem grid_column_eq {t : Fin 3 → Fin 3 → I}
    (hcol : ∀ j k, j < k → ∀ i l, t i j < t l k)
    {j k : Fin 3} {u : I} (hj : u ∈ Icc (t 0 j) (t 2 j))
    (hk : u ∈ Icc (t 0 k) (t 2 k)) : j = k := by
  rcases lt_trichotomy j k with hjk | rfl | hkj
  · exact ((hcol j k hjk 2 0).not_ge (hk.1.trans hj.2)).elim
  · rfl
  · exact ((hcol k j hkj 2 0).not_ge (hj.1.trans hk.2)).elim

private theorem assemble_tripods {X : Type*} [TopologicalSpace X]
    {C : Set X} (U : Fin 3 → Set X) (hUC : ∀ i, Disjoint (U i) C)
    (hUU : Pairwise (fun i j ↦ Disjoint (U i) (U j)))
    (a : Fin 3 × Fin 3 → X) (ha : Injective a) (haC : ∀ e, a e ∈ C)
    (b m : Fin 3 → X) (hb : ∀ i, b i ∈ U i) (hm : Injective m)
    (hmC : ∀ j, m j ∈ C) (M N : Fin 3 × Fin 3 → Set X)
    (hM : ∀ e, IsPrimitiveLink (M e) (b e.1) (a e))
    (hMU : ∀ e, M e \ {a e} ⊆ U e.1)
    (hMM : ∀ i, Pairwise (fun j k ↦ M (i, j) ∩ M (i, k) = {b i}))
    (hN : ∀ e, a e ≠ m e.2 → IsPrimitiveLink (N e) (a e) (m e.2))
    (hNsame : ∀ e, a e = m e.2 → N e = {a e})
    (hNC : ∀ e, N e ⊆ C)
    (hNN : Pairwise (fun e f ↦ N e ∩ N f ⊆ range m))
    (hAN : ∀ e f, a e ∈ N f → e = f ∨ a e ∈ range m)
    (hNm : ∀ e j, m j ∈ N e → j = e.2) :
    ∃ (v : Fin 3 ⊕ Fin 3 → X) (L : Fin 3 × Fin 3 → Set X),
      Injective v ∧
      (∀ e, IsPrimitiveLink (L e) (v (.inl e.1)) (v (.inr e.2))) ∧
      (∀ e, L e ∩ range v ⊆ {v (.inl e.1), v (.inr e.2)}) ∧
      Pairwise (fun e f ↦ L e ∩ L f ⊆ range v) := by
  classical
  let v : Fin 3 ⊕ Fin 3 → X := Sum.elim b m
  have hbC (i) : b i ∉ C := (hUC i).notMem_of_mem_left (hb i)
  have hbne (i j) (hij : i ≠ j) : b i ≠ b j := fun heq ↦
    (hUU hij).notMem_of_mem_left (hb i) (heq ▸ hb j)
  have hv : Injective v := by
    rintro (i | i) (j | j) heq
    · exact congrArg Sum.inl (not_imp_not.mp (hbne i j) heq)
    · change b i = m j at heq
      exact (hbC i (heq ▸ hmC j)).elim
    · change m i = b j at heq
      exact (hbC j (heq.symm ▸ hmC i)).elim
    · exact congrArg Sum.inr (hm heq)
  have hMC (e) : M e ∩ C ⊆ {a e} := by
    rintro z ⟨hz, hzC⟩
    by_contra hne
    exact (hUC e.1).notMem_of_mem_left (hMU e ⟨hz, hne⟩) hzC
  have hMb (e) (i) (hi : b i ∈ M e) : i = e.1 := by
    by_contra hne
    exact (hUU hne).notMem_of_mem_left (hb i)
      (hMU e ⟨hi, fun heq ↦ hbC i (heq ▸ haC e)⟩)
  have hMcross {e f : Fin 3 × Fin 3} (hef : e ≠ f) :
      M e ∩ M f ⊆ range b := by
    rintro z ⟨hze, hzf⟩
    by_cases hi : e.1 = f.1
    · have hj : e.2 ≠ f.2 := fun hj ↦ hef (Prod.ext hi hj)
      have heq : z = b e.1 := (hMM e.1 hj).subset ⟨hze, by simpa only [hi] using hzf⟩
      exact ⟨e.1, heq.symm⟩
    · by_cases hza : z = a e
      · have hzC : z ∈ C := hza ▸ haC e
        have hzf' : z = a f := hMC f ⟨hzf, hzC⟩
        exact (hef (ha (hza.symm.trans hzf'))).elim
      · have hzU := hMU e ⟨hze, hza⟩
        have hzf' : z ≠ a f := fun heq ↦
          (hUC e.1).notMem_of_mem_left hzU (heq ▸ haC f)
        exact ((hUU hi).notMem_of_mem_left hzU (hMU f ⟨hzf, hzf'⟩)).elim
  refine ⟨v, fun e ↦ M e ∪ N e, hv, ?_, ?_, ?_⟩
  · intro e
    by_cases heq : a e = m e.2
    · have hsame : M e ∪ N e = M e := by
        rw [hNsame e heq]
        exact union_eq_left.mpr (singleton_subset_iff.mpr (hM e).right_mem)
      change IsPrimitiveLink (M e ∪ N e) (b e.1) (m e.2)
      rw [hsame]
      exact heq ▸ hM e
    · exact (hM e).union (hN e heq) (fun h ↦ hbC e.1 (h ▸ haC e)) heq
        (fun z hz ↦ hMC e ⟨hz.1, hNC e hz.2⟩)
  · rintro e z ⟨hzM | hzN, ⟨i | j, rfl⟩⟩
    · exact Or.inl (congrArg b (hMb e i hzM))
    · have heq : m j = a e := hMC e ⟨hzM, hmC j⟩
      have hmem : m j ∈ N e := by
        by_cases h : a e = m e.2
        · simpa only [hNsame e h, mem_singleton_iff] using heq
        · exact heq ▸ (hN e h).left_mem
      exact Or.inr (congrArg m (hNm e j hmem))
    · exact (hbC i (hNC e hzN)).elim
    · exact Or.inr (congrArg m (hNm e j hzN))
  · intro e f hef z hz
    have hbv : range b ⊆ range v := fun z ⟨i, hi⟩ ↦ ⟨.inl i, hi⟩
    have hmv : range m ⊆ range v := fun z ⟨i, hi⟩ ↦ ⟨.inr i, hi⟩
    rcases hz with ⟨hze | hze, hzf | hzf⟩
    · exact hbv (hMcross hef ⟨hze, hzf⟩)
    · have heq : z = a e := hMC e ⟨hze, hNC f hzf⟩
      exact hmv ((hAN e f (heq ▸ hzf)).resolve_left hef) |> (heq ▸ ·)
    · have heq : z = a f := hMC f ⟨hzf, hNC e hze⟩
      exact hmv ((hAN f e (heq ▸ hze)).resolve_left hef.symm) |> (heq ▸ ·)
    · exact hmv (hNN hef ⟨hze, hzf⟩)

private theorem assemble_loop_tripods {x : ℂ} {P : Path x x} (hP : P.IsSimpleLoop)
    (t : Fin 3 → Fin 3 → I) (ht : ∀ i j, t i j ∈ Ioo (0 : I) 1)
    (hrow : ∀ j, StrictMono (fun i ↦ t i j))
    (hcol : ∀ j k, j < k → ∀ i l, t i j < t l k)
    (U : Fin 3 → Set ℂ) (hUC : ∀ i, Disjoint (U i) (range P))
    (hUU : Pairwise (fun i j ↦ Disjoint (U i) (U j)))
    (b : Fin 3 → ℂ) (hb : ∀ i, b i ∈ U i) (M : Fin 3 × Fin 3 → Set ℂ)
    (hM : ∀ e, IsPrimitiveLink (M e) (b e.1) (P (t e.1 e.2)))
    (hMU : ∀ e, M e \ {P (t e.1 e.2)} ⊆ U e.1)
    (hMM : ∀ i, Pairwise (fun j k ↦ M (i, j) ∩ M (i, k) = {b i})) :
    ∃ (v : Fin 3 ⊕ Fin 3 → ℂ) (L : Fin 3 × Fin 3 → Set ℂ),
      Injective v ∧
      (∀ e, IsPrimitiveLink (L e) (v (.inl e.1)) (v (.inr e.2))) ∧
      (∀ e, L e ∩ range v ⊆ {v (.inl e.1), v (.inr e.2)}) ∧
      Pairwise (fun e f ↦ L e ∩ L f ⊆ range v) := by
  let a (e : Fin 3 × Fin 3) := P (t e.1 e.2)
  let m (j : Fin 3) := P (t 1 j)
  let J (e : Fin 3 × Fin 3) := uIcc (t e.1 e.2) (t 1 e.2)
  let N (e : Fin 3 × Fin 3) := P '' J e
  have hJ (e) : J e ⊆ Ioo (0 : I) 1 := by
    intro u hu
    have hu' := grid_interval_subset hrow e.1 e.2 hu
    exact ⟨(ht 0 e.2).1.trans_le hu'.1, hu'.2.trans_lt (ht 2 e.2).2⟩
  have hJcol {e f : Fin 3 × Fin 3} {u : I} (he : u ∈ J e) (hf : u ∈ J f) :
      e.2 = f.2 := grid_column_eq hcol
    (grid_interval_subset hrow e.1 e.2 he) (grid_interval_subset hrow f.1 f.2 hf)
  have hti : Injective (fun e : Fin 3 × Fin 3 ↦ t e.1 e.2) := by
    intro e f hef
    change t e.1 e.2 = t f.1 f.2 at hef
    have hj : e.2 = f.2 := hJcol (e := e) (f := f) left_mem_uIcc
      (hef ▸ left_mem_uIcc)
    apply Prod.ext _ hj
    exact (hrow f.2).injective (by simpa only [hj] using hef)
  have ha : Injective a := fun e f hef ↦
    hti (hP.isPrimitive.injOn_Ioo (ht e.1 e.2) (ht f.1 f.2) hef)
  have hm : Injective m := fun j k hjk ↦ congrArg Prod.snd (ha (a₁ := (1, j))
    (a₂ := (1, k)) hjk)
  apply assemble_tripods U hUC hUU a ha (fun e ↦ mem_range_self _) b m hb hm
    (fun j ↦ mem_range_self _) M N hM hMU hMM
  · intro e hne
    change IsPrimitiveLink (P '' uIcc (t e.1 e.2) (t 1 e.2)) _ _
    rw [← P.range_subpath]
    exact (hP.isPrimitive.subpath (fun heq ↦ hne (congrArg P heq))).isPrimitiveLink
  · intro e heq
    have hteq := hP.isPrimitive.injOn_Ioo (ht e.1 e.2) (ht 1 e.2) heq
    simp only [N, J, hteq, uIcc_self, image_singleton, a]
  · exact fun e ↦ image_subset_range ..
  · intro e f hef z hz
    obtain ⟨⟨u, hu, huz⟩, v, hv, hvz⟩ := hz
    have huv : u = v := hP.isPrimitive.injOn_Ioo (hJ e hu) (hJ f hv) (huz.trans hvz.symm)
    subst v
    have hj := hJcol hu hv
    have hi : e.1 ≠ f.1 := fun hi ↦ hef (Prod.ext hi hj)
    have hmid : u = t 1 e.2 := (three_interval_inter (hrow e.2) hi).subset
      ⟨hu, by simpa only [J, hj] using hv⟩
    exact ⟨e.2, (congrArg P hmid).symm.trans huz⟩
  · intro e f hef
    obtain ⟨u, hu, hua⟩ := hef
    have hteq : t e.1 e.2 = u :=
      hP.isPrimitive.injOn_Ioo (ht e.1 e.2) (hJ f hu) hua.symm
    have hj := hJcol (e := e) (f := f) left_mem_uIcc (hteq ▸ hu)
    have hin : t e.1 e.2 ∈ uIcc (t f.1 e.2) (t 1 e.2) := by
      simpa only [J, ← hj, ← hteq] using hu
    obtain hi | hi := three_interval_endpoint (hrow e.2) hin
    · exact Or.inl (Prod.ext hi hj)
    · exact Or.inr ⟨e.2, by simp only [a, m, hi]⟩
  · intro e j hj
    obtain ⟨u, hu, hum⟩ := hj
    have hteq : t 1 j = u := hP.isPrimitive.injOn_Ioo (ht 1 j) (hJ e hu) hum.symm
    exact hJcol (e := (1, j)) (f := e) left_mem_uIcc (hteq ▸ hu)

private theorem ordered_accesses {x : ℂ} {P : Path x x} (hP : P.IsSimpleLoop)
    (p : Fin 3 → ℂ) (U : Fin 3 → Set ℂ)
    (haccess : ∀ i, ∀ O : Set ℂ, IsOpen O → (O ∩ range P).Nonempty →
      ∃ q ∈ O ∩ range P, ∃ L : Set ℂ, IsPrimitiveLink L (p i) q ∧ IsSegmentFigure L ∧
        L \ {q} ⊆ U i) :
    ∃ t : Fin 3 → Fin 3 → I,
      (∀ i j, t i j ∈ Ioo (0 : I) 1) ∧
      (∀ j, StrictMono (fun i ↦ t i j)) ∧
      (∀ j k, j < k → ∀ i l, t i j < t l k) ∧
      ∃ L : Fin 3 → Fin 3 → Set ℂ,
        (∀ i j, IsPrimitiveLink (L i j) (p i) (P (t i j))) ∧
        (∀ i j, IsSegmentFigure (L i j)) ∧
        (∀ i j, L i j \ {P (t i j)} ⊆ U i) := by
  let lo (i j : Fin 3) : I := ⟨(6 * (j : ℝ) + 2 * (i : ℝ) + 1) / 20, by
    fin_cases i <;> fin_cases j <;> norm_num⟩
  let hi (i j : Fin 3) : I := ⟨(6 * (j : ℝ) + 2 * (i : ℝ) + 2) / 20, by
    fin_cases i <;> fin_cases j <;> norm_num⟩
  have hslots (i j : Fin 3) : 0 < lo i j ∧ lo i j < hi i j ∧ hi i j < 1 := by
    change (0 : ℝ) < (lo i j).val ∧ (lo i j).val < (hi i j).val ∧ (hi i j).val < 1
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg _
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    have hi2 : (i : ℝ) ≤ 2 := by exact_mod_cast (show (i : ℕ) ≤ 2 by omega)
    have hj2 : (j : ℝ) ≤ 2 := by exact_mod_cast (show (j : ℕ) ≤ 2 by omega)
    dsimp only [lo, hi]
    constructor
    · positivity
    constructor <;> linarith
  choose O hO heq using fun i j ↦
    exists_open_interval_target hP (hslots i j).1 (hslots i j).2.2
  have hnon (i j) : (O i j ∩ range P).Nonempty := by
    rw [heq i j]
    exact ((nonempty_Ioo.mpr (hslots i j).2.1).image P)
  choose q hq L hL hpoly hLU using fun i j ↦ haccess i (O i j) (hO i j) (hnon i j)
  choose t ht hqt using fun i j ↦ (heq i j ▸ hq i j : q i j ∈ P '' Ioo (lo i j) (hi i j))
  refine ⟨t, ?_, ?_, ?_, L, ?_, hpoly, ?_⟩
  · intro i j
    exact ⟨(hslots i j).1.trans (ht i j).1, (ht i j).2.trans (hslots i j).2.2⟩
  · intro j i k hik
    have hsep : hi i j ≤ lo k j := by
      change (6 * (j : ℝ) + 2 * (i : ℝ) + 2) / 20 ≤
        (6 * (j : ℝ) + 2 * (k : ℝ) + 1) / 20
      have hik' : (i : ℝ) + 1 ≤ (k : ℝ) := by
        exact_mod_cast (show (i : ℕ) + 1 ≤ (k : ℕ) from hik)
      linarith
    exact (ht i j).2.trans_le (hsep.trans (ht k j).1.le)
  · intro j k hjk i l
    have hsep : hi i j ≤ lo l k := by
      change (6 * (j : ℝ) + 2 * (i : ℝ) + 2) / 20 ≤
        (6 * (k : ℝ) + 2 * (l : ℝ) + 1) / 20
      have hjk' : (j : ℝ) + 1 ≤ (k : ℝ) := by
        exact_mod_cast (show (j : ℕ) + 1 ≤ (k : ℕ) from hjk)
      have hi2 : (i : ℝ) ≤ 2 := by exact_mod_cast (show (i : ℕ) ≤ 2 by omega)
      have hl0 : (0 : ℝ) ≤ (l : ℝ) := by positivity
      linarith
    exact (ht i j).2.trans_le (hsep.trans (ht l k).1.le)
  · intro i j
    simpa only [hqt i j] using hL i j
  · intro i j
    simpa only [hqt i j] using hLU i j

/-- Three distinct components of a compact circuit's complement, with polygonal access to
every relative open part of the circuit, yield a subdivision of the complete bipartite graph
with three vertices in each part. -/
theorem of_three_components {C : Set ℂ}
    (hC : IsCircuit C) (hcompact : IsCompact C) (p : Fin 3 → ℂ) (hp : ∀ i, p i ∉ C)
    (hdistinct : Pairwise fun i j ↦
      connectedComponentIn Cᶜ (p i) ≠ connectedComponentIn Cᶜ (p j))
    (haccess : ∀ i, ∀ O : Set ℂ, IsOpen O → (O ∩ C).Nonempty →
      ∃ q ∈ O ∩ C, ∃ L : Set ℂ, IsPrimitiveLink L (p i) q ∧ IsSegmentFigure L ∧
        L \ {q} ⊆ connectedComponentIn Cᶜ (p i)) :
    ∃ (v : Fin 3 ⊕ Fin 3 → ℂ) (L : Fin 3 × Fin 3 → Set ℂ),
      Injective v ∧
      (∀ e, IsPrimitiveLink (L e) (v (.inl e.1)) (v (.inr e.2))) ∧
      (∀ e, L e ∩ range v ⊆ {v (.inl e.1), v (.inr e.2)}) ∧
      Pairwise (fun e f ↦ L e ∩ L f ⊆ range v) := by
  classical
  obtain ⟨x, hx⟩ := hC.nonempty
  obtain ⟨P, hP, hPC⟩ := hC.exists_isSimpleLoop hcompact hx
  let U i := connectedComponentIn Cᶜ (p i)
  have hU (i) : IsOpen (U i) := hcompact.isClosed.isOpen_compl.connectedComponentIn
  have hpU (i) : p i ∈ U i := mem_connectedComponentIn (hp i)
  have hUc (i) : IsPathConnected (U i) := (hU i).isConnected_iff_isPathConnected.mp
    (isConnected_connectedComponentIn_iff.mpr (hp i))
  have hUC (i) : Disjoint (U i) (range P) := by
    rw [hPC]
    exact disjoint_compl_left.mono_left (connectedComponentIn_subset ..)
  have hUU : Pairwise (fun i j ↦ Disjoint (U i) (U j)) :=
    fun i j hij ↦ disjoint_connectedComponentIn_of_ne (hdistinct hij)
  obtain ⟨t, ht, hrow, hcol, L, hL, hpoly, hLU⟩ := ordered_accesses hP p U (by
    simpa only [hPC] using haccess)
  have hat (i) : Injective (fun j ↦ P (t i j)) := by
    intro j k heq
    have heqt : t i j = t i k := hP.isPrimitive.injOn_Ioo (ht i j) (ht i k) heq
    rcases lt_trichotomy j k with hjk | rfl | hkj
    · exact ((hcol j k hjk i i).ne heqt).elim
    · rfl
    · exact ((hcol k j hkj i i).ne heqt.symm).elim
  have haU (i j) : P (t i j) ∉ U i :=
    fun h ↦ (hUC i).notMem_of_mem_left h (mem_range_self _)
  choose b hb M hM hMpoly hMU hMM using fun i ↦
    (hU i).exists_primitiveLink_tripod (hUc i) (hpU i) (fun j ↦ P (t i j))
      (hat i) (haU i) (L i) (hL i) (hpoly i) (hLU i)
  exact assemble_loop_tripods hP t ht hrow hcol U hUC hUU b hb
    (fun e ↦ M e.1 e.2) (fun e ↦ hM e.1 e.2) (fun e ↦ hMU e.1 e.2) hMM

end JordanConfigurations
