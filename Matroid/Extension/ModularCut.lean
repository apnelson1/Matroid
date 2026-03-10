import Matroid.ForMathlib.Matroid.Basic
import Matroid.ForMathlib.Matroid.Map
import Matroid.Closure
import Matroid.Modular.Basic
import Matroid.Minor.Contract
import Matroid.ForMathlib.Data.Set.Finite

/-

# Extensions

If `M` is a matroid and `e` is an element outside the ground set of `M`,
a single-element extension of `M` by `e` is a matroid `M'` for which
`M'.E = M.E ∪ {e}` and `M' ＼ e = M`.

In 1965, Crapo proved that the single-element extensions of a finite matroid `M` are
described precisely by the 'modular cuts' of `M`; a modular cut is an upper ideal in the
lattice of flats of `M` that is closed under taking intersections of modular pairs.
(in a finite matroid, `A,B` is  modular pair if `rk A + rk B = rk (A ∪ B) + rk (A ∩ B)`).
Given a modular cut `U`, the flats of `M` spanning the new element `e` in the extension `M'` are
precisely those in `U`. See [Oxley 7.2].

For infinite matroids, this condition fails to correctly parametrize matroid extensions;
for instance, if `M` is a free matroid on an infinite ground set,
and `U` is the collection of all sets of `M` with finite complement,
then `U` is clearly a modular cut (it is closed under taking intersections of any two elements),
but `U` doesn't correspond to any single-element extension; in such an extension `M'`,
`e` would be spanned by every hyperplane of `M` and would therefore be spanned by the
rank-zero flat of `M`, which isn't in `U`.

To correctly describe single-element extensions of infinite matroids, we need to modify
the definition of a modular cut. Instead of insisting that a modular cut `U` be closed
under taking intersections of modular pairs, we instead require that it is closed under
intersections of arbitrary 'modular families'. Modular families are collections of sets
with a common basis; they are defined in `Matroid.Modular`.

In this file, we define modular cuts, show that they parametrize single-element extensions
of arbitrary matroids, and that they specialize to Crapo's modular cuts in the finite-rank case.
We also define the 'projection' of `M` associated with each modular cut `U` of `M`; this is the
matroid obtained from `M` by extending using `U`, then contracting the new element.

# Main Definitions.

* `Matroid.ModularCut` : a collection of flats in a matroid closed under taking superflats and
    under taking intersections of modular families.

* `ModularCut.principal M X` : the modular cut of `M` comprising all the flats containing `X`

* `ModularCut.restrict` : the restriction of a modular cut to a restriction of `M`.

* `ModularCut.ofDeleteElem` : the modular cut of `M ＼ e` corresponding to the extension `M`
    of `M ＼ e`.

* `ModularCut.ofForallIsModularPairChainInter` : to define a modular cut, it suffices to
  verify that the collection is closed under intersections of modular pairs
  and infinite modular chains, rather than general modular families.

* `ModularCut.ofForallIsModularPairInter` : in the finite-rank case,
  a modular cut in the classical sense gives a modular cut in the more general sense.

* `Matroid.extendBy e U` : add an element `e` to a matroid `M` using a modular cut `U`.

* `Matroid.extensionEquiv` : the equivalence between single-element extensions of `M`
    and modular cuts of `M`.

* `Matroid.projectBy e U` : add and then contract a new element in a matroid `M`
  using a modular cut `U`.

* `Matroid.truncate` : add a new element freely spanned by `M.E`, then contract it.

# TODO

The modular cuts of a matroid form a lattice.

-/

universe u

open Set Function Set.Notation Option

variable {α : Type*} {M : Matroid α} {I J B F₀ F F' X Y : Set α} {e f : α}

namespace Matroid

/-- A `ModularCut M` is a collection of flats of `M` that is closed under taking superflats and
under intersections of modular families. These parametrize the extensions of `M` by a single
element outside `M` and hence also the projections of `M`; see `Matroid.extendBy` and
`Matroid.projectBy`.  -/
structure ModularCut (M : Matroid α) where
  (carrier : Set (Set α))
  (forall_isFlat : ∀ F ∈ carrier, M.IsFlat F)
  (forall_superset : ∀ F F', F ∈ carrier → M.IsFlat F' → F ⊆ F' → F' ∈ carrier)
  (forall_inter : ∀ Fs ⊆ carrier,
    Fs.Nonempty → M.IsModularFamily (fun x : Fs ↦ x) → ⋂₀ Fs ∈ carrier)

variable {U : M.ModularCut}

namespace ModularCut

instance (M : Matroid α) : SetLike (ModularCut M) (Set α) where
  coe := ModularCut.carrier
  coe_injective' U U' := by cases U; cases U'; simp

@[simp]
lemma mem_carrier_iff {U : M.ModularCut} : F ∈ U.carrier ↔ F ∈ U := Iff.rfl

lemma isFlat_of_mem (U : M.ModularCut) (hF : F ∈ U) : M.IsFlat F :=
  U.forall_isFlat F hF

-- Add aesop incantation
lemma subset_ground (U : M.ModularCut) (hF : F ∈ U) : F ⊆ M.E :=
    (U.isFlat_of_mem hF).subset_ground

lemma superset_mem (U : M.ModularCut) (hF : F ∈ U) (hF' : M.IsFlat F') (hFF' : F ⊆ F') :
    F' ∈ U :=
  U.forall_superset F F' hF hF' hFF'

@[ext]
protected lemma ext {U U' : M.ModularCut} (h : ∀ F, M.IsFlat F → (F ∈ U ↔ F ∈ U')) : U = U' := by
  suffices h_eq : U.carrier = U'.carrier by
    cases U with | mk carrier forall_isFlat forall_superset forall_inter =>
    · simp only at h_eq
      simp [h_eq]
  ext F
  by_cases hFlat : M.IsFlat F
  · exact h F hFlat
  exact iff_of_false (fun hF ↦ hFlat (U.forall_isFlat F hF))
    (fun hF ↦ hFlat (U'.forall_isFlat F hF))

/-- Transfer a `ModularCut` across a matroid equality. -/
protected def copy {N : Matroid α} (U : M.ModularCut) (hNM : M = N) : N.ModularCut where
  carrier := U
  forall_isFlat := by obtain rfl := hNM; exact U.forall_isFlat
  forall_superset := by obtain rfl := hNM; exact U.forall_superset
  forall_inter := by obtain rfl := hNM; exact U.forall_inter

@[simp]
protected lemma mem_copy_iff {N : Matroid α} (U : M.ModularCut) {hNM : M = N} :
    F ∈ U.copy hNM ↔ F ∈ U := Iff.rfl

/-- Transfer a `ModularCut` along an injection -/
protected def map {β : Type*} (U : M.ModularCut) (f : α → β) (hf : M.E.InjOn f) :
    (M.map f hf).ModularCut where
  carrier := (image f) '' U
  forall_isFlat := by
    rintro _ ⟨F, hF, rfl⟩
    exact (U.forall_isFlat F hF).map hf
  forall_superset := by
    simp_rw [isFlat_map_iff]
    rintro _ F' ⟨F, hF, rfl⟩ ⟨F', hF', rfl⟩ hss
    refine ⟨F', U.forall_superset _ _ hF hF' ?_, rfl⟩
    rwa [← hf.image_subset_image_iff (U.forall_isFlat F hF).subset_ground hF'.subset_ground]
  forall_inter := by
    simp_rw [isModularFamily_map_iff, subset_image_iff]
    rintro _ ⟨Fs, hFs, rfl⟩ hne ⟨Ys, ⟨B, hB, hYs⟩, h_eq⟩
    have hFsE : ∀ F ∈ Fs, F ⊆ M.E := fun F hF ↦ (U.forall_isFlat F (hFs hF)).subset_ground
    have hwin := U.forall_inter Fs hFs (by simpa using hne) ⟨B, hB, ?_⟩
    · simp only [sInter_image, mem_image, SetLike.mem_coe]
      refine ⟨_, hwin, ?_⟩
      rw [← InjOn.image_biInter_eq (f := f) (by simpa using hne), sInter_eq_biInter]
      exact hf.mono <| by simpa only [iUnion_subset_iff]
    simp only [Subtype.forall]
    refine fun F hF ↦ ?_
    simp only [Subtype.forall, mem_image, forall_exists_index] at hYs h_eq
    specialize h_eq _ _ ⟨hF, rfl⟩
    specialize hYs _ _ ⟨hF, rfl⟩
    rw [hf.image_eq_image_iff (hFsE F hF) hYs.subset_ground] at h_eq
    rwa [← h_eq] at hYs

@[simp]
protected lemma mem_map_iff {β : Type*} (U : M.ModularCut) (f : α → β) (hf : M.E.InjOn f)
    {F : Set β} : F ∈ (U.map f hf) ↔ ∃ F₀ ∈ U, f '' F₀ = F := Iff.rfl

protected lemma image_mem_map_iff {β : Type*} (U : M.ModularCut) (f : α → β) (hf : M.E.InjOn f)
    {F : Set α} (hF : F ⊆ M.E) : f '' F ∈ U.map f hf ↔ F ∈ U := by
  rw [U.mem_map_iff]
  refine ⟨fun ⟨F', hF', heq⟩ ↦ ?_, fun h ↦ ⟨F, h, rfl⟩⟩
  rw [hf.image_eq_image_iff (U.subset_ground hF') hF] at heq
  rwa [← heq]

@[simp]
protected
lemma mem_mk_iff (S : Set (Set α)) (h₁) (h₂) (h₃) {X : Set α} :
  X ∈ ModularCut.mk (M := M) S h₁ h₂ h₃ ↔ X ∈ S := Iff.rfl

lemma closure_superset_mem (U : M.ModularCut) (hF : F ∈ U) (hFX : F ⊆ M.closure X) :
    M.closure X ∈ U :=
  U.superset_mem hF (M.closure_isFlat _) hFX

lemma closure_superset_mem' (U : M.ModularCut) (hX : M.closure X ∈ U) (hXY : X ⊆ Y) :
    M.closure Y ∈ U :=
  U.closure_superset_mem hX (M.closure_subset_closure hXY)

protected lemma sInter_mem (U : M.ModularCut) {Fs : Set (Set α)} (hne : Fs.Nonempty) (hFs : Fs ⊆ U)
    (hFs_mod : M.IsModularFamily (fun F : Fs ↦ F)) : ⋂₀ Fs ∈ U :=
  U.forall_inter Fs hFs hne hFs_mod

protected lemma iInter_mem (U : M.ModularCut) {ι : Type*} [Nonempty ι] (Fs : ι → Set α)
    (hFs : ∀ i, Fs i ∈ U) (hFs_mod : M.IsModularFamily Fs) : ⋂ i, Fs i ∈ U := by
  have hwin := U.sInter_mem (Fs := range Fs) (range_nonempty Fs) ?_ ?_
  · simpa using hwin
  · rintro _ ⟨i, hi, rfl⟩; exact hFs i
  obtain ⟨B, hB, hB'⟩ := hFs_mod
  exact ⟨B, hB, by simpa⟩

protected lemma inter_mem (U : M.ModularCut) (hF : F ∈ U) (hF' : F' ∈ U)
    (h : M.IsModularPair F F') : F ∩ F' ∈ U := by
  rw [inter_eq_iInter]
  apply U.iInter_mem _ _ h
  simp [hF, hF']

lemma closure_mem_of_mem (hF : F ∈ U) : M.closure F ∈ U := by
  rwa [(U.isFlat_of_mem hF).closure]

/-- The `ModularCut` of all flats containing `X` -/
@[simps]
def principal (M : Matroid α) (X : Set α) : M.ModularCut where
  carrier := {F | M.IsFlat F ∧ X ⊆ F}
  forall_superset _ _ hF hF' hFF' := ⟨hF', hF.2.trans hFF'⟩
  forall_isFlat _ h := h.1
  forall_inter _ hS hne _ := ⟨IsFlat.sInter hne fun _ h ↦ (hS h).1,
    subset_sInter fun _ h ↦ (hS h).2⟩

@[simp]
lemma mem_principal_iff : F ∈ principal M X ↔ M.IsFlat F ∧ X ⊆ F := Iff.rfl

/-- The empty modular cut -/
@[simps]
protected def empty (M : Matroid α) : M.ModularCut where
  carrier := ∅
  forall_isFlat := by simp
  forall_superset := by simp
  forall_inter := by simp

instance (M : Matroid α) : PartialOrder M.ModularCut where
  le U U' := (U : Set (Set α)) ⊆ U'
  le_refl _ := Subset.rfl
  le_trans _ _ _ := Subset.trans
  le_antisymm U U' h h' := by simpa using subset_antisymm h h'

protected lemma le_iff_subset {U U' : M.ModularCut} :
  U ≤ U' ↔ (U : Set (Set α)) ⊆ U' := Iff.rfl

instance (M : Matroid α) : BoundedOrder M.ModularCut where
  top := ModularCut.principal M ∅
  le_top U x h := by simpa using U.isFlat_of_mem h
  bot := ModularCut.empty M
  bot_le _ _ := by simp

@[simp]
protected lemma notMem_bot (X : Set α) : X ∉ (⊥ : M.ModularCut) :=
  notMem_empty X

@[simp]
protected lemma coe_bot (M : Matroid α) : ((⊥ : M.ModularCut) : Set (Set α)) = ∅ := rfl

lemma eq_bot_or_ground_mem (U : M.ModularCut) : U = ⊥ ∨ M.E ∈ U := by
  obtain (hU | ⟨F, hF⟩) := (U : Set (Set α)).eq_empty_or_nonempty
  · exact .inl <| SetLike.ext'_iff.2 <| by simp [hU]
  exact .inr <| U.superset_mem hF M.ground_isFlat (U.isFlat_of_mem hF).subset_ground

protected lemma eq_bot_iff (U : M.ModularCut) : U = ⊥ ↔ M.E ∉ U := by
  refine ⟨fun h hE ↦ ?_, fun h ↦ ?_⟩
  · obtain rfl := h
    simp at hE
  obtain hU | hU := U.eq_bot_or_ground_mem
  · assumption
  contradiction

protected lemma ne_bot_iff (U : M.ModularCut) : U ≠ ⊥ ↔ M.E ∈ U := by
  rw [Ne, U.eq_bot_iff, not_not]

lemma mem_top_of_isFlat (hF : M.IsFlat F) : F ∈ (⊤ : M.ModularCut) :=
  ⟨hF, empty_subset F⟩

@[simp]
protected lemma mem_top_iff : F ∈ (⊤ : M.ModularCut) ↔ M.IsFlat F :=
  ⟨fun h ↦ h.1, ModularCut.mem_top_of_isFlat⟩

protected lemma eq_top_iff : U = ⊤ ↔ M.loops ∈ U := by
  refine ⟨by rintro rfl; exact ⟨M.closure_isFlat ∅, empty_subset _⟩, fun h ↦ ?_⟩
  simp only [SetLike.ext_iff, ModularCut.mem_top_iff]
  exact fun F ↦ ⟨U.isFlat_of_mem, fun h' ↦ U.superset_mem h h' h'.loops_subset⟩

protected lemma top_ne_bot (M : Matroid α) : (⊤ : M.ModularCut) ≠ (⊥ : M.ModularCut) := by
  rw [Ne, eq_comm, ModularCut.eq_top_iff]; simp

@[simp]
protected lemma map_top {β : Type*} {f : α → β} (hf : InjOn f M.E) :
    (⊤ : M.ModularCut).map f hf = ⊤ := by
  ext F h
  simp only [ModularCut.mem_map_iff, ModularCut.mem_top_iff, h, iff_true]
  simp_rw [isFlat_map_iff, eq_comm (a := F)] at h
  assumption

@[simp]
protected lemma map_eq_top {β : Type*} {f : α → β } (hf) {U : M.ModularCut} :
    U.map f hf = ⊤ ↔ U = ⊤ := by
  simp +contextual only [ModularCut.ext_iff, isFlat_map_iff, ModularCut.mem_map_iff,
    ModularCut.mem_top_iff, iff_def, implies_true, forall_const, true_and, forall_exists_index,
    and_imp]
  refine ⟨fun h F hF ↦ ?_, ?_⟩
  · obtain ⟨F₀, hF₀U, hF₀F⟩ := h (f '' F) _ hF rfl
    rw [hf.image_eq_image_iff (U.subset_ground hF₀U) hF.subset_ground] at hF₀F
    rwa [← hF₀F]
  rintro h _ F hF rfl
  exact ⟨F, h F hF, rfl⟩

@[simp]
protected lemma map_bot {β : Type*} {f : α → β} (hf : InjOn f M.E) :
    (⊥ : M.ModularCut).map f hf = ⊥ := by
  ext; simp

@[simp]
protected lemma map_eq_bot {β : Type*} {f : α → β} {U : M.ModularCut} (hf : InjOn f M.E) :
    U.map f hf = ⊥ ↔ U = ⊥ := by
  refine ⟨fun h_eq ↦ ?_, by rintro rfl; simp⟩
  simp only [ModularCut.ext_iff, isFlat_map_iff, ModularCut.mem_map_iff, ModularCut.notMem_bot,
    iff_false, not_exists, not_and] at h_eq ⊢
  exact fun F hF hFU ↦ h_eq _ ⟨F, hF, rfl⟩ F hFU rfl

@[simp]
lemma principal_eq_top_iff : ModularCut.principal M F = ⊤ ↔ F ⊆ M.loops := by
  rw [ModularCut.eq_top_iff, mem_principal_iff, ← closure_empty, and_iff_right (M.isFlat_closure ∅)]

@[simp]
lemma principal_eq_bot_iff : ModularCut.principal M F = ⊥ ↔ ¬ (F ⊆ M.E) := by
  rw [ModularCut.eq_bot_iff, mem_principal_iff, and_iff_right M.ground_isFlat]

lemma principal_ground_ne_top (M : Matroid α) [RankPos M] : ModularCut.principal M M.E ≠ ⊤ := by
  simp only [ne_eq, principal_eq_top_iff, loops]
  obtain ⟨B, hB⟩ := M.exists_isBase
  obtain ⟨e, heB⟩ := hB.nonempty
  exact fun h ↦ (hB.indep.isNonloop_of_mem heB).not_isLoop <| h (hB.subset_ground heB)

lemma mem_of_ssubset_indep_of_forall_diff (U : M.ModularCut) (hI : M.Indep I)
    (hJI : J ⊂ I) (h : ∀ e ∈ I \ J, M.closure (I \ {e}) ∈ U) : M.closure J ∈ U := by
  set Is : ↑(I \ J) → Set α := fun e ↦ I \ {e.1} with hIs
  have hmod : M.IsModularFamily Is := hI.isModularFamily_of_subsets (by simp [hIs])
  have hne := nonempty_of_ssubset hJI
  have h_inter : ⋂ e, Is e = J := by
    rw [hIs, ← biInter_eq_iInter (t := fun x _ ↦ I \ {x}), biInter_diff_singleton_eq_diff _ hne,
      diff_diff_right, diff_self, empty_union, inter_eq_self_of_subset_right hJI.subset]
  have _ := hne.coe_sort
  rw [← h_inter, ← hmod.iInter_closure_eq_closure_iInter]
  exact U.iInter_mem _ (fun ⟨i, hi⟩ ↦ h _ (by simpa)) hmod.cls_isModularFamily

/-- If `X` spans a flat outside `U`, but `X ∪ {y}` spans a flat in `U` for all
`y ∈ Y \ M.closure X`, then `M.closure X` is covered by `M.closure Y`. -/
lemma covBy_of_maximal_closure (U : M.ModularCut) {X Y : Set α}
    (hXY : M.closure X ⊆ M.closure Y) (hYU : M.closure Y ∈ U) (hXU : M.closure X ∉ U)
    (hmax : ∀ x ∈ Y \ M.closure X, M.closure (insert x X) ∈ U) : M.closure X ⋖[M] M.closure Y := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_isBasis'_of_subset (hI.subset.trans subset_union_left)
  have hJ' := hJ.isBasis_closure_right
  rw [← closure_closure_union_closure_eq_closure_union, union_eq_self_of_subset_left hXY,
    closure_closure] at hJ'

  rw [← hI.closure_eq_closure, ← M.closure_closure Y, ← hJ'.closure_eq_closure]
  rw [← M.closure_closure Y, ← hJ'.closure_eq_closure] at hYU
  rw [← hI.closure_eq_closure] at hXU

  obtain (h | hnt) := (J \ I).subsingleton_or_nontrivial
  · obtain (he | ⟨e, he⟩) := h.eq_empty_or_singleton
    · rw [(diff_eq_empty.1 he).antisymm hIJ] at hYU; contradiction
    obtain rfl : J = insert e I := by rw [← union_diff_cancel hIJ, he, union_singleton]
    simpa [show e ∉ I from (he.symm.subset rfl).2] using hJ.indep.closure_diff_covBy (.inl rfl)

  obtain (rfl | hssu) := hIJ.eq_or_ssubset
  · simp at hnt

  refine by_contra fun _ ↦ hXU <| U.mem_of_ssubset_indep_of_forall_diff hJ.indep hssu fun x hx ↦ ?_
  obtain ⟨y, hy, hyx⟩ := hnt.exists_ne x
  have hyE : y ∈ M.E := hJ.indep.subset_ground hy.1
  have hyX : y ∉ M.closure X := by
    rw [← hI.closure_eq_closure, hI.indep.notMem_closure_iff_of_notMem hy.2 hyE]
    exact hJ.indep.subset (insert_subset hy.1 hIJ)
  have hyY : y ∈ Y :=
    Or.elim (hJ.subset hy.1) (False.elim ∘ (notMem_of_mem_diff_closure ⟨hyE, hyX⟩)) id

  specialize hmax y ⟨hyY, hyX⟩
  rw [← closure_insert_congr_right hI.closure_eq_closure] at hmax
  refine U.closure_superset_mem' hmax ?_
  simp [insert_subset_iff, subset_diff, hIJ, hy.1, hyx.symm, hx.2]
section restrict

/-- A `ModularCut` in `M` gives a `ModularCut` in `M ↾ R` for any `R ⊆ M.E`. -/
protected def restrict (U : M.ModularCut) (R : Set α) : (M ↾ R).ModularCut where
  carrier := {F | (M ↾ R).IsFlat F ∧ M.closure F ∈ U}
  forall_isFlat F h := h.1
  forall_superset F F' h hF' hFF' := ⟨hF', (U.closure_superset_mem' h.2 hFF')⟩
  forall_inter Xs hXs hne hmod := by
    refine ⟨IsFlat.sInter hne (fun F hF ↦ (hXs hF).1), ?_⟩
    have hmod' := hmod.ofRestrict'
    have := hne.coe_sort
    rw [← closure_inter_ground, sInter_distrib_inter hne]
    have hcl := hmod'.iInter_closure_eq_closure_iInter
    have hcl' := hmod'.cls_isModularFamily
    simp only [closure_inter_ground] at hcl'
    simp only [closure_inter_ground, iInter_coe_set] at hcl
    rw [← hcl]
    simpa using U.iInter_mem (fun i : Xs ↦ M.closure i) (fun i ↦ (hXs i.2).2) hcl'

@[simp]
lemma mem_restrict_iff (U : M.ModularCut) {R : Set α}  :
    F ∈ (U.restrict R) ↔ (M ↾ R).IsFlat F ∧ M.closure F ∈ U := Iff.rfl

/-- a `ModularCut` in `M` gives a `ModularCut` in `M ＼ D` for any `D`. -/
protected def delete (U : M.ModularCut) (D : Set α) : (M ＼ D).ModularCut :=
  U.restrict (M.E \ D)

@[simp]
lemma mem_delete_iff (U : M.ModularCut) {D : Set α}  :
    F ∈ (U.delete D) ↔ (M ＼ D).IsFlat F ∧ M.closure F ∈ U := Iff.rfl

lemma mem_delete_elem_iff :
    F ∈ U.delete {e} ↔ (e ∉ F) ∧ (F ∈ U ∨ (insert e F ∈ U ∧ e ∈ M.closure F)) := by
  simp only [mem_delete_iff, deleteElem_isFlat_iff]
  constructor
  rintro ⟨⟨heF, (hF | hF)⟩, hFU⟩
  · rw [hF.closure] at hFU
    exact ⟨heF, .inl hFU⟩
  · rw [← hF.closure]
    obtain (heF' | heF') := em (e ∈ M.closure F)
    · rw [← insert_eq_of_mem heF'] at hFU
      replace hFU := U.closure_mem_of_mem hFU
      rw [closure_insert_closure_eq_closure_insert] at hFU
      exact ⟨heF, .inr ⟨hFU, heF'⟩⟩
    have hF' : M.IsFlat F := by
      have hFE := ((subset_insert _ _).trans hF.subset_ground)
      rw [isFlat_iff_subset_closure_self]
      refine (subset_diff_singleton (M.closure_subset_closure (subset_insert e F)) heF').trans ?_
      simp [hF.closure]
    rw [hF'.closure] at hFU
    exact ⟨heF, .inl hFU⟩
  rintro ⟨heF, (hFU | hFU)⟩
  · simpa [(U.isFlat_of_mem hFU), heF, (U.isFlat_of_mem hFU).closure]
  have hfl := U.isFlat_of_mem hFU.1
  rw [← hfl.closure, ← closure_insert_closure_eq_closure_insert, insert_eq_of_mem hFU.2,
    closure_closure] at hFU
  exact ⟨⟨heF, .inr hfl⟩, hFU.1⟩

def comapOfSubsetRange {β : Type*} {M : Matroid β} (U : M.ModularCut) (f : α → β)
    (hf : M.E ⊆ range f) : (M.comap f).ModularCut where
  carrier := (preimage f) '' U
  forall_isFlat := by
    simp only [mem_image, SetLike.mem_coe, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
      isFlat_comap_iff_exists]
    exact fun F hF ↦ ⟨F, U.isFlat_of_mem hF, rfl⟩
  forall_superset := by
    simp [isFlat_comap_iff_exists]
    rintro _ _ F hF rfl F' hF' rfl hss
    have hF_flat := U.isFlat_of_mem hF
    rw [preimage_subset_preimage_iff (hF_flat.subset_ground.trans hf)] at hss
    exact ⟨F', U.superset_mem hF hF' hss, rfl⟩
  forall_inter := by
    simp only [mem_image, SetLike.mem_coe, forall_subset_image_iff, image_nonempty, sInter_image]
    intro Fs hFs hne hmod
    have hne : Nonempty (preimage f '' Fs) := by
      simp only [nonempty_subtype, mem_image]
      exact ⟨_, _, hne.some_mem, rfl⟩
    have hmod' := hmod.of_comap
    refine ⟨_, U.iInter_mem (ι := (preimage f '' Fs)) (fun i ↦ f '' i) ?_ hmod', ?_⟩
    · simp only [Subtype.forall, mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      exact fun F hF ↦ hFs <| by rwa [image_preimage_eq_inter_range,
        inter_eq_self_of_subset_left ((U.subset_ground (hFs hF)).trans hf)]
    simp only [iInter_coe_set, mem_image, iInter_exists, biInter_and', iInter_iInter_eq_right]
    refine subset_antisymm (subset_iInter₂ fun F hF ↦ preimage_mono ?_) ?_
    · exact iInter₂_subset_of_subset _ hF <| image_preimage_subset f F
    simp only [subset_def, mem_iInter, mem_preimage, mem_image]
    exact fun e he F hF ↦ ⟨e, he _ hF, rfl⟩

@[simp]
lemma mem_comapOfSubsetRange_iff {β : Type*} {M : Matroid β} (U : M.ModularCut)
    {f : α → β} {hf} : F ∈ U.comapOfSubsetRange f hf ↔ ∃ F₀ ∈ U, f ⁻¹' F₀ = F := Iff.rfl

protected def comap {β : Type*} {M : Matroid β} (U : M.ModularCut) (f : α → β) :
    (M.comap f).ModularCut :=
  ((U.restrict (range f ∩ M.E)).comapOfSubsetRange f inter_subset_left).copy <|
    M.comap_restrict_range_inter f

@[simp]
lemma mem_comap_iff {β : Type*} {M : Matroid β} (U : M.ModularCut) (f : α → β) :
    F ∈ U.comap f ↔ M.closure (f '' F) ∈ U ∧ F = f ⁻¹' (M.closure (f '' F)) := by
  simp [ModularCut.comap, comapOfSubsetRange, ModularCut.mem_mk_iff, mem_image,
    SetLike.mem_coe, mem_restrict_iff, isFlat_restrict_iff', diff_eq_empty.2 inter_subset_right]
  simp_rw [← inter_assoc, inter_right_comm,
    inter_eq_self_of_subset_left (M.closure_subset_ground _)]
  refine ⟨?_, fun ⟨h1, h2⟩ ↦ ?_⟩
  · rintro ⟨X, h1, rfl⟩
    rw [image_preimage_eq_of_subset (h1.1.subset.trans inter_subset_right), and_iff_right h1.2]
    nth_rw 1 [h1.1, preimage_inter_range]
  refine ⟨f '' F, ⟨?_, h1⟩, ?_⟩
  · nth_rw 1 [h2, image_preimage_eq_inter_range]
  nth_rw 1 [h2, preimage_image_preimage]
  rwa [eq_comm]

/-- Given an element `e` of a matroid `M`, the modular cut of `M ＼ e` corresponding to the
extension `M` of `M ＼ e`. Intended to apply when `e ∈ M.E`. -/
def ofDeleteElem (M : Matroid α) (e : α) : (M ＼ {e}).ModularCut where
  carrier := {F | (M ＼ {e}).IsFlat F ∧ e ∈ M.closure F}
  forall_isFlat _ h := h.1
  forall_superset := by
    simp_rw [isFlat_delete_iff]
    rintro _ _ ⟨⟨F, -, rfl⟩, he⟩ ⟨F', hF', rfl⟩ hFF'
    exact ⟨⟨F',hF', rfl⟩, M.closure_subset_closure hFF' he⟩
  forall_inter := by
    refine fun Fs hFs hFne hmod ↦ ⟨IsFlat.sInter hFne fun F hF ↦ (hFs hF).1, ?_⟩
    have := hFne.coe_sort
    rw [delete_eq_restrict] at hmod
    rw [sInter_eq_iInter, ← (hmod.ofRestrict diff_subset).iInter_closure_eq_closure_iInter,
      mem_iInter]
    exact fun ⟨F, hF⟩ ↦ (hFs hF).2

lemma mem_ofDeleteElem_iff :
    F ∈ ModularCut.ofDeleteElem M e ↔ e ∉ F ∧ M.closure F = insert e F := by
  change _ ∧ _ ↔ _
  rw [deleteElem_isFlat_iff, and_assoc, and_congr_right_iff]
  refine fun he ↦ ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨(hF | hF), heF⟩
    · rw [hF.closure] at heF; contradiction
    rw [← hF.closure, ← closure_insert_closure_eq_closure_insert, insert_eq_of_mem heF,
      closure_closure]
  rw [h, and_iff_left (.inl rfl), ← h]
  exact .inr (M.closure_isFlat F)

@[simp]
lemma mem_ofDeleteElem_iff' :
    F ∈ ModularCut.ofDeleteElem M e ↔ e ∈ M.closure F \ F ∧ M.IsFlat (insert e F) := by
  simp only [mem_ofDeleteElem_iff, mem_diff]
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨h.1.2, ?_⟩⟩
  · rw [← h.2, and_iff_left <| M.closure_isFlat F, and_iff_left h.1, h.2]
    exact mem_insert _ _
  rw [← h.2.closure, ← closure_insert_closure_eq_closure_insert, insert_eq_of_mem h.1.1,
    closure_closure]

end restrict

section finite

/-- The modular family condition can be replaced by a condition about modular pairs and
infinite chains. -/
def ofForallIsModularPairChainInter (M : Matroid α) (U : Set (Set α))
    (h_isFlat : ∀ F ∈ U, M.IsFlat F)
    (h_superset : ∀ ⦃F F'⦄, F ∈ U → M.IsFlat F' → F ⊆ F' → F' ∈ U)
    (h_pair : ∀ ⦃F F'⦄, F ∈ U → F' ∈ U → M.IsModularPair F F' → F ∩ F' ∈ U)
    (h_chain : ∀ Cs ⊆ U, Cs.Infinite → M.IsModularFamily (fun x : Cs ↦ x)
      → IsChain (· ⊆ ·) Cs → ⋂₀ Cs ∈ U) : M.ModularCut where
  carrier := U
  forall_isFlat := h_isFlat
  forall_superset := h_superset
  forall_inter := by
    rintro Fs hFs ⟨F₀, hF₀⟩ h
    obtain ⟨B, hB⟩ := h
    have hmodcl := hB.indep.isMutualBasis_powerset.isMutualBasis_cls
    have aux : Fs ⊆ M.closure '' 𝒫 B :=
      fun F hF ↦ ⟨F ∩ B, by simp [hB.closure_inter_eq ⟨F, hF⟩, (h_isFlat F (hFs hF)).closure]⟩
    have aux2 : ∀ F ∈ M.closure '' 𝒫 B, F = M.closure (F ∩ B) := by
      simp only [mem_image, mem_powerset_iff, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
      intro I hI
      rw [hB.indep.closure_inter_eq_self_of_subset hI]
    have hzorn := zorn_superset_nonempty (S := U ∩ M.closure '' B.powerset)
      fun D hD hDchain hDne ↦ ⟨⋂₀ D, ⟨?_, ?_⟩, ?_⟩
    · obtain ⟨F₁, -, hmin⟩ := hzorn F₀ ⟨hFs hF₀, aux hF₀⟩
      apply h_superset hmin.prop.1 (IsFlat.sInter ⟨F₀, hF₀⟩ fun F hF ↦ h_isFlat F (hFs hF))
      refine subset_sInter fun F hF ↦ inter_eq_right.1 ?_
      apply hmin.eq_of_subset ⟨h_pair (hFs hF) hmin.prop.1 ?_, ?_⟩ inter_subset_right
      · refine isModularPair_iff.2 ⟨B, hB.indep, hB.isBasis_inter ⟨_, hF⟩, ?_⟩
        nth_rewrite 2 [aux2 F₁ hmin.prop.2]
        exact (hB.indep.inter_left _).isBasis_closure
      rw [aux2 F (aux hF), aux2 F₁ hmin.prop.2, ← Indep.closure_inter_eq_inter_closure,
        ← inter_inter_distrib_right]
      · exact ⟨_, inter_subset_right, rfl⟩
      exact hB.indep.subset (by simp)
    · obtain hfin | hinf := D.finite_or_infinite
      · replace hDchain : IsChain (fun a b ↦ b ⊆ a) D := hDchain.symm
        exact (hD.trans inter_subset_left) <| hDchain.directedOn.iInf_mem hDne hfin
      apply h_chain _ (hD.trans inter_subset_left) hinf ⟨B, ?_⟩ hDchain
      convert hmodcl.comp (fun F : D ↦ ⟨F ∩ B, by simp⟩) using 2 with ⟨F, hF⟩
      simp [comp_apply, ← aux2 _ (hD hF).2]
    · refine ⟨⋂₀ D ∩ B, by simp, ?_⟩
      have := hDne.to_subtype
      have hrw : ⋂₀ D = ⋂ i ∈ D, M.closure (i ∩ B) := by
        rw [← iInter₂_congr (fun i hi ↦ aux2 i (hD hi).2), sInter_eq_biInter]
      convert (hmodcl.comp (fun F : D ↦ ⟨F ∩ B, by simp⟩)).isBasis_iInter.closure_eq_closure
      · simpa
      simp only [comp_apply, iInter_coe_set, ← hrw]
      rw [(IsFlat.sInter hDne fun F hF ↦ (h_isFlat F (hD hF).1)).closure]
    exact fun F hF ↦ sInter_subset_of_mem hF

@[simp]
lemma mem_ofForallIsModularPairChainInter_iff (M : Matroid α) (U : Set (Set α))
    (h_isFlat) (h_superset) (h_pair) (h_chain) {F : Set α} :
    F ∈ ModularCut.ofForallIsModularPairChainInter M U h_isFlat h_superset h_pair h_chain ↔ F ∈ U :=
  Iff.rfl

/-- For a finite-rank matroid, the intersection condition can be replaced with a condition about
modular pairs rather than families. -/
@[simps!]
def ofForallIsModularPairInter (M : Matroid α) [M.RankFinite] (U : Set (Set α))
    (h_isFlat : ∀ F ∈ U, M.IsFlat F)
    (h_superset : ∀ ⦃F F'⦄, F ∈ U → M.IsFlat F' → F ⊆ F' → F' ∈ U)
    (h_pair : ∀ ⦃F F'⦄, F ∈ U → F' ∈ U → M.IsModularPair F F' → F ∩ F' ∈ U) : M.ModularCut :=
  ofForallIsModularPairChainInter M U h_isFlat h_superset h_pair <|
    fun _ h hinf _ hCs ↦ False.elim <| hinf <|
    finite_of_isChain_of_forall_isFlat (fun _ hF ↦ h_isFlat _ (h hF)) hCs

@[simp]
lemma mem_ofForallIsModularPairInter_iff (M : Matroid α) [M.RankFinite] (U : Set (Set α))
    (h_isFlat) (h_superset) (h_pair) {F : Set α} :
    F ∈ ModularCut.ofForallIsModularPairInter M U h_isFlat h_superset h_pair ↔ F ∈ U :=
  Iff.rfl

end finite



section LinearClass

/-
TODO. I think linear classes only work for finite-rank matroids;
if `B` and `B'` are disjoint infinite
bases of `M`, the class of hyperplanes `H` with `B\H` finite ought not to be a linear class,
but I don't know what reasonable definition would forbid that.
-/

-- def LinearClass (M : Matroid α) where
--   carrier : Set (Set α)
--   forall_isHyperplane : ∀ H ∈ carrier, M.IsHyperplane H
--   forall_hyper' : ∀ H₁ H₂ ∈ carrier,

end LinearClass
