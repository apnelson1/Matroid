import Matroid.ForMathlib.Matroid.Basic
import Matroid.Modular.Basic

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

* `ModularCut.ofForallIsModularPairInter` : in the finite-rank case,
  a modular cut in the classical sense gives a modular cut in the more general sense.

* `Matroid.extendBy e U` : add an element `e` to a matroid `M` using a modular cut `U`.

* `Matroid.extensionEquiv` : the equivalence between single-element extensions of `M`
    and modular cuts of `M`.

* `Matroid.projectBy e U` : add and then contract a new element in a matroid `M`
  using a modular cut `U`.

* `Matroid.truncate` : add a new element freely spanned by `M.E`, then contract it.

-/

open Set Function Set.Notation Option

variable {α : Type*} {M : Matroid α} {I J B F₀ F F' X Y : Set α} {e f : α}

namespace Matroid

/-- A `ModularCut M` is a collection of flats of `M` that is closed under taking superflats and
under intersections of modular families. These parametrize the extensions of `M` by a single
element outside `M` and hence also the projections of `M`; see `Matroid.extendBy` and
`Matroid.projectBy`.  -/
@[ext] structure ModularCut (M : Matroid α) where
  (carrier : Set (Set α))
  (forall_isFlat : ∀ F ∈ carrier, M.IsFlat F)
  (forall_superset : ∀ F F', F ∈ carrier → M.IsFlat F' → F ⊆ F' → F' ∈ carrier)
  (forall_inter : ∀ Fs ⊆ carrier,
    Fs.Nonempty → M.IsModularFamily (fun x : Fs ↦ x) → ⋂₀ Fs ∈ carrier)

variable {U : M.ModularCut}

instance (M : Matroid α) : SetLike (ModularCut M) (Set α) where
  coe := ModularCut.carrier
  coe_injective' U U' := by cases U; cases U'; simp

/-- Transfer a `ModularCut` across a matroid equality. -/
def ModularCut.copy {N : Matroid α} (U : M.ModularCut) (hNM : M = N) : N.ModularCut where
  carrier := U
  forall_isFlat := by obtain rfl := hNM; exact U.forall_isFlat
  forall_superset := by obtain rfl := hNM; exact U.forall_superset
  forall_inter := by obtain rfl := hNM; exact U.forall_inter

@[simp] lemma ModularCut.mem_copy_iff {N : Matroid α} (U : M.ModularCut) {hNM : M = N} :
    F ∈ U.copy hNM ↔ F ∈ U := Iff.rfl

/-- Transfer a `ModularCut` along an injection -/
def ModularCut.map {β : Type*} (U : M.ModularCut) (f : α → β) (hf : M.E.InjOn f) :
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

@[simp] lemma ModularCut.mem_mk_iff (S : Set (Set α)) (h₁) (h₂) (h₃) {X : Set α} :
  X ∈ ModularCut.mk (M := M) S h₁ h₂ h₃ ↔ X ∈ S := Iff.rfl

lemma ModularCut.isFlat_of_mem (U : M.ModularCut) (hF : F ∈ U) : M.IsFlat F :=
  U.forall_isFlat F hF

lemma ModularCut.superset_mem (U : M.ModularCut) (hF : F ∈ U) (hF' : M.IsFlat F') (hFF' : F ⊆ F') :
    F' ∈ U :=
  U.forall_superset F F' hF hF' hFF'

lemma ModularCut.closure_superset_mem (U : M.ModularCut) (hF : F ∈ U) (hFX : F ⊆ M.closure X) :
    M.closure X ∈ U :=
  U.superset_mem hF (M.closure_isFlat _) hFX

lemma ModularCut.closure_superset_mem' (U : M.ModularCut) (hX : M.closure X ∈ U) (hXY : X ⊆ Y) :
    M.closure Y ∈ U :=
  U.closure_superset_mem hX (M.closure_subset_closure hXY)

lemma ModularCut.sInter_mem (U : M.ModularCut) {Fs : Set (Set α)} (hne : Fs.Nonempty) (hFs : Fs ⊆ U)
    (hFs_mod : M.IsModularFamily (fun F : Fs ↦ F)) : ⋂₀ Fs ∈ U :=
  U.forall_inter Fs hFs hne hFs_mod

lemma ModularCut.iInter_mem (U : M.ModularCut) {ι : Type*} [Nonempty ι] (Fs : ι → Set α)
    (hFs : ∀ i, Fs i ∈ U) (hFs_mod : M.IsModularFamily Fs) : ⋂ i, Fs i ∈ U := by
  have hwin := U.sInter_mem (Fs := range Fs) (range_nonempty Fs) ?_ ?_
  · simpa using hwin
  · rintro _ ⟨i, hi, rfl⟩; exact hFs i
  obtain ⟨B, hB, hB'⟩ := hFs_mod
  exact ⟨B, hB, by simpa⟩

lemma ModularCut.inter_mem (U : M.ModularCut) (hF : F ∈ U) (hF' : F' ∈ U)
    (h : M.IsModularPair F F') : F ∩ F' ∈ U := by
  rw [inter_eq_iInter]
  apply U.iInter_mem _ _ h
  simp [hF, hF']

lemma ModularCut.closure_mem_of_mem (hF : F ∈ U) : M.closure F ∈ U := by
  rwa [(U.isFlat_of_mem hF).closure]

/-- The `ModularCut` of all flats containing `X` -/
@[simps] def ModularCut.principal (M : Matroid α) (X : Set α) : M.ModularCut where
  carrier := {F | M.IsFlat F ∧ X ⊆ F}
  forall_isFlat _ h := h.1
  forall_superset _ _ hF hF' hFF' := ⟨hF', hF.2.trans hFF'⟩
  forall_inter _ hS hne _ := ⟨IsFlat.sInter hne fun _ h ↦ (hS h).1,
    subset_sInter fun _ h ↦ (hS h).2⟩

@[simp] lemma ModularCut.mem_principal_iff : F ∈ principal M X ↔ M.IsFlat F ∧ X ⊆ F := Iff.rfl

/-- The empty modular cut -/
@[simps] def ModularCut.empty (M : Matroid α) : M.ModularCut where
  carrier := ∅
  forall_isFlat := by simp
  forall_superset := by simp
  forall_inter := by simp

instance (M : Matroid α) : PartialOrder M.ModularCut where
  le U U' := (U : Set (Set α)) ⊆ U'
  le_refl _ := Subset.rfl
  le_trans _ _ _ := Subset.trans
  le_antisymm U U' h h' := by simpa using subset_antisymm h h'

lemma ModularCut.le_iff_subset {U U' : M.ModularCut} :
  U ≤ U' ↔ (U : Set (Set α)) ⊆ U' := Iff.rfl

instance (M : Matroid α) : BoundedOrder M.ModularCut where
  top := ModularCut.principal M ∅
  le_top U x h := by simpa using U.isFlat_of_mem h
  bot := ModularCut.empty M
  bot_le _ _ := by simp

@[simp] protected lemma ModularCut.not_mem_bot (X : Set α) : X ∉ (⊥ : M.ModularCut) :=
  not_mem_empty X

@[simp] lemma ModularCut.coe_bot (M : Matroid α) : ((⊥ : M.ModularCut) : Set (Set α)) = ∅ := rfl

lemma ModularCut.eq_bot_or_ground_mem (U : M.ModularCut) : U = ⊥ ∨ M.E ∈ U := by
  obtain (hU | ⟨F, hF⟩) := (U : Set (Set α)).eq_empty_or_nonempty
  · exact .inl <| SetLike.ext'_iff.2 <| by simp [hU]
  exact .inr <| U.superset_mem hF M.ground_isFlat (U.isFlat_of_mem hF).subset_ground

protected lemma ModularCut.mem_top_of_isFlat (hF : M.IsFlat F) : F ∈ (⊤ : M.ModularCut) :=
  ⟨hF, empty_subset F⟩

@[simp] lemma ModularCut.mem_top_iff : F ∈ (⊤ : M.ModularCut) ↔ M.IsFlat F :=
  ⟨fun h ↦ h.1, ModularCut.mem_top_of_isFlat⟩

lemma ModularCut.eq_top_iff : U = ⊤ ↔ M.loops ∈ U := by
  refine ⟨by rintro rfl; exact ⟨M.closure_isFlat ∅, empty_subset _⟩, fun h ↦ ?_⟩
  simp only [SetLike.ext_iff, mem_top_iff]
  exact fun F ↦ ⟨U.isFlat_of_mem, fun h' ↦ U.superset_mem h h' h'.loops_subset⟩

lemma top_ne_bot (M : Matroid α) : (⊤ : M.ModularCut) ≠ (⊥ : M.ModularCut) := by
  rw [Ne, eq_comm, ModularCut.eq_top_iff]; simp

lemma principal_ground_ne_top (M : Matroid α) [RankPos M] : ModularCut.principal M M.E ≠ ⊤ := by
  simp only [Ne, ModularCut.eq_top_iff, ModularCut.mem_principal_iff, closure_isFlat, true_and]
  obtain ⟨B, hB⟩ := M.exists_isBase
  obtain ⟨e, heB⟩ := hB.nonempty
  exact fun h ↦ (hB.indep.isNonloop_of_mem heB).not_isLoop <| h (hB.subset_ground heB)

lemma ModularCut.mem_of_ssubset_indep_of_forall_diff (U : M.ModularCut) (hI : M.Indep I)
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
lemma ModularCut.covBy_of_maximal_closure (U : M.ModularCut) {X Y : Set α}
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
    rw [← hI.closure_eq_closure, hI.indep.not_mem_closure_iff_of_not_mem hy.2 hyE]
    exact hJ.indep.subset (insert_subset hy.1 hIJ)
  have hyY : y ∈ Y :=
    Or.elim (hJ.subset hy.1) (False.elim ∘ (not_mem_of_mem_diff_closure ⟨hyE, hyX⟩)) id

  specialize hmax y ⟨hyY, hyX⟩
  rw [← closure_insert_congr_right hI.closure_eq_closure] at hmax
  refine U.closure_superset_mem' hmax ?_
  simp [insert_subset_iff, subset_diff, hIJ, hy.1, hyx.symm, hx.2]
section restrict

/-- A `ModularCut` in `M` gives a `ModularCut` in `M ↾ R` for any `R ⊆ M.E`. -/
def ModularCut.restrict (U : M.ModularCut) {R : Set α} (hR : R ⊆ M.E) : (M ↾ R).ModularCut where
  carrier := {F | (M ↾ R).IsFlat F ∧ M.closure F ∈ U}
  forall_isFlat F h := h.1
  forall_superset F F' h hF' hFF' := ⟨hF', (U.closure_superset_mem' h.2 hFF')⟩
  forall_inter Xs hXs hne hmod := by
    refine ⟨IsFlat.sInter hne (fun F hF ↦ (hXs hF).1), ?_⟩
    replace hmod := hmod.ofRestrict hR
    have _ := hne.coe_sort
    rw [sInter_eq_iInter, ← hmod.iInter_closure_eq_closure_iInter]
    exact U.iInter_mem _ (fun i ↦ (hXs i.2).2) hmod.cls_isModularFamily

/-- a `ModularCut` in `M` gives a `ModularCut` in `M ＼ D` for any `D`. -/
def ModularCut.delete (U : M.ModularCut) (D : Set α) : (M ＼ D).ModularCut :=
  U.restrict diff_subset

lemma ModularCut.mem_delete_elem_iff :
    F ∈ U.delete {e} ↔ (e ∉ F) ∧ (F ∈ U ∨ (insert e F ∈ U ∧ e ∈ M.closure F)) := by
  rw [ModularCut.delete, ModularCut.restrict, ModularCut.mem_mk_iff, mem_setOf_eq,
    ← delete_eq_restrict, ← deleteElem, isFlat_deleteElem_iff]
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

/-- Given an element `e` of a matroid `M`, the modular cut of `M ＼ e` corresponding to the
extension `M` of `M ＼ e`. Intended to apply when `e ∈ M.E`. -/
@[simps] def ModularCut.ofDeleteElem (M : Matroid α) (e : α) : (M ＼ e).ModularCut where
  carrier := {F | (M ＼ e).IsFlat F ∧ e ∈ M.closure F}
  forall_isFlat _ h := h.1
  forall_superset := by
    simp_rw [deleteElem, isFlat_delete_iff]
    rintro _ _ ⟨⟨F, -, rfl⟩, he⟩ ⟨F', hF', rfl⟩ hFF'
    exact ⟨⟨F',hF', rfl⟩, M.closure_subset_closure hFF' he⟩
  forall_inter := by
    refine fun Fs hFs hFne hmod ↦ ⟨IsFlat.sInter hFne fun F hF ↦ (hFs hF).1, ?_⟩
    have := hFne.coe_sort
    rw [deleteElem, delete_eq_restrict] at hmod
    rw [sInter_eq_iInter, ← (hmod.ofRestrict diff_subset).iInter_closure_eq_closure_iInter,
      mem_iInter]
    exact fun ⟨F, hF⟩ ↦ (hFs hF).2

lemma mem_ofDeleteElem_iff :
    F ∈ ModularCut.ofDeleteElem M e ↔ e ∉ F ∧ M.closure F = insert e F := by
  change _ ∧ _ ↔ _
  rw [isFlat_deleteElem_iff, and_assoc, and_congr_right_iff]
  refine fun he ↦ ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨(hF | hF), heF⟩
    · rw [hF.closure] at heF; contradiction
    rw [← hF.closure, ← closure_insert_closure_eq_closure_insert, insert_eq_of_mem heF,
      closure_closure]
  rw [h, and_iff_left (.inl rfl), ← h]
  exact .inr (M.closure_isFlat F)

@[simp] lemma mem_ofDeleteElem_iff' :
    F ∈ ModularCut.ofDeleteElem M e ↔ e ∈ M.closure F \ F ∧ M.IsFlat (insert e F) := by
  simp only [deleteElem, mem_ofDeleteElem_iff, mem_diff]
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨h.1.2, ?_⟩⟩
  · rw [← h.2, and_iff_left <| M.closure_isFlat F, and_iff_left h.1, h.2]
    exact mem_insert _ _
  rw [← h.2.closure, ← closure_insert_closure_eq_closure_insert, insert_eq_of_mem h.1.1,
    closure_closure]

end restrict

section finite

/-- For a finite-rank matroid, the intersection condition can be replaced with a condition about
modular pairs rather than families. -/
@[simps] def ModularCut.ofForallIsModularPairInter (M : Matroid α) [M.RankFinite] (U : Set (Set α))
    (h_isFlat : ∀ F ∈ U, M.IsFlat F)
    (h_superset : ∀ ⦃F F'⦄, F ∈ U → M.IsFlat F' → F ⊆ F' → F' ∈ U)
    (h_pair : ∀ ⦃F F'⦄, F ∈ U → F' ∈ U → M.IsModularPair F F' → F ∩ F' ∈ U) :
    M.ModularCut where
  carrier := U
  forall_isFlat := h_isFlat
  forall_superset := h_superset
  forall_inter := by
    suffices h : ∀ (S : Finset (Set α)),
        S.Nonempty → ↑S ⊆ U → M.IsModularFamily (fun (F : S) ↦ F) → ⋂₀ S ∈ U by
      intro Fs hFU hne hmod
      have hFs : Fs.Finite :=
        by simpa using hmod.finite_of_forall_isFlat fun F ↦ h_isFlat _ (hFU F.2)
      obtain ⟨S, rfl⟩ := hFs.exists_finset_coe
      exact h S (by simpa using hne) (by simpa) hmod
    apply Finset.Nonempty.cons_induction
    · simp +contextual
    simp only [Finset.coe_cons, insert_subset_iff, sInter_insert, and_imp]
    intro F S hFS hne IH hFU hSU hmod

    set incl : S → S.cons F hFS := fun X ↦ ⟨X, by simp⟩
    refine h_pair hFU (IH hSU (hmod.comp incl)) ?_
    have : Nontrivial (S.cons F hFS) := by
      obtain ⟨F', hF'⟩ := hne
      refine ⟨⟨F, by simp⟩, ⟨F', by simp [hF']⟩, ?_⟩
      simp only [ne_eq, Subtype.mk.injEq]
      rintro rfl; contradiction
    convert hmod.isModularPair_singleton_compl_biInter ⟨F, by simp⟩
    simp only [mem_compl_iff, mem_singleton_iff, iInter_subtype, sInter_eq_iInter]
    ext x
    simp only [Finset.mem_coe, mem_iInter, Finset.mem_cons, Subtype.mk.injEq,
      iInter_iInter_eq_or_left, not_true_eq_false, iInter_of_empty, univ_inter]
    exact ⟨fun h i his _ ↦ h i his, fun h i his ↦ h i his (by rintro rfl; contradiction)⟩


-- @[simps] def ModularCut.ofForallIsModularPairChainInter (M : Matroid α) (U : Set (Set α))
--     (h_isFlat : ∀ F ∈ U, M.IsFlat F)
--     (h_superset : ∀ ⦃F F'⦄, F ∈ U → M.IsFlat F' → F ⊆ F' → F' ∈ U)
--     (h_pair : ∀ ⦃F F'⦄, F ∈ U → F' ∈ U → M.IsModularPair F F' → F ∩ F' ∈ U)
--     (h_chain : ∀ Cs ⊆ U, Cs.Nonempty → M.IsModularFamily (fun x : Cs ↦ x)
--       → IsChain (· ⊆ ·) Cs → ⋂₀ Cs ∈ U) : M.ModularCut where
--   carrier := U
--   forall_isFlat := h_isFlat
--   forall_superset := h_superset
--   forall_inter := by
--     intro Fs hFs hne hmod
--     have := zorn_superset_nonempty (S := Fs) fun D hD hDchain hDne ↦ ⟨⋂₀ D, ?_, ?_⟩
--     · sorry
--     have := h_chain D (hD.trans hFs) hDne ?_ hDchain


end finite

/-- A modular cut `U` in a contraction `M ／ C` gives rise to a modular cut in `M`.
This corresponds to the freeest extension of `M` that contracts to the extension given by `U`. -/
@[simps] def ModularCut.ofContract {C : Set α} (U : (M ／ C).ModularCut) (hC : C ⊆ M.E) :
    M.ModularCut where
  carrier := (· ∪ C) '' U
  forall_isFlat := by
    simpa using fun F hF ↦ ((isFlat_contract_iff hC).1 (U.isFlat_of_mem hF)).1
  forall_superset := by
    simp only [mem_image, SetLike.mem_coe, forall_exists_index, and_imp]
    rintro _ F G hGU rfl hF hFF
    have h := (isFlat_contract_iff hC).1 <| U.isFlat_of_mem hGU
    rw [union_subset_iff] at hFF

    refine ⟨_,  U.superset_mem hGU (F' := F \ C) ?_ (by simp [subset_diff, h.2, hFF.1]),
      by simp [hFF.2]⟩
    rwa [isFlat_contract_iff, diff_union_of_subset hFF.2, and_iff_left disjoint_sdiff_left]
  forall_inter := by
    simp only [subset_def, mem_image, SetLike.mem_coe]
    intro Fs hFs hne hmod
    have h_inter := U.sInter_mem (Fs := (· \ C) '' Fs)
    simp only [image_nonempty, hne, subset_def, mem_image, SetLike.mem_coe, forall_exists_index,
      and_imp, forall_apply_eq_imp_iff₂, sInter_image, forall_const] at h_inter

    refine ⟨_, h_inter (fun F hF ↦ ?_) ?_, ?_⟩
    ·
      obtain ⟨F, hFU, rfl⟩ := hFs F hF
      have hFE := subset_diff.1 (U.isFlat_of_mem hFU).subset_ground
      simpa [hFE.2.symm.sdiff_eq_right]
    · have hcl : ∀ (F : ↑Fs), C ⊆ M.closure F
      · rintro ⟨F, hF⟩
        obtain ⟨F', hF', -, rfl⟩ := hFs F hF
        simp [M.subset_closure_of_subset' subset_union_right hC]
      have h' := hmod.contract (C := C) hcl
      have hφ : ∀ X ∈ ((· \ C) '' Fs), X ∪ C ∈ Fs
      · suffices ∀ F ∈ Fs, F ∪ C ∈ Fs by simpa
        refine fun F hF ↦ ?_
        obtain ⟨F', hF', -, rfl⟩ := hFs F hF
        simpa [union_assoc]
      set φ : ((· \ C) '' Fs) → Fs := fun ⟨X, hX⟩ ↦ ⟨X ∪ C, hφ X hX⟩ with hφ'
      convert h'.comp φ
      ext ⟨A, ⟨B, hB, rfl⟩⟩ e
      simp [hφ']


    simp_rw [diff_eq]
    rw [← biInter_distrib_inter _ hne, sInter_eq_biInter, ← diff_eq, diff_union_of_subset]
    simp only [subset_iInter_iff]
    refine fun F hF ↦ ?_
    obtain ⟨F, -, rfl⟩ := hFs F hF
    exact subset_union_right

@[simp] lemma mem_ofContract_iff {C : Set α} (U : (M ／ C).ModularCut) {hC : C ⊆ M.E} :
    F ∈ U.ofContract hC ↔ C ⊆ F ∧ F \ C ∈ U := by
  simp only [ModularCut.ofContract, ModularCut.mem_mk_iff, mem_image, SetLike.mem_coe]
  refine ⟨?_, fun h ↦ ⟨_, h.2, diff_union_of_subset h.1⟩⟩
  rintro ⟨F, hF, rfl⟩
  simpa [(subset_diff.1 (U.isFlat_of_mem hF).subset_ground).2.sdiff_eq_left]

section extensions

/-- `U.ExtIndep e I` means that `I` is independent in the matroid obtained from `M`
by adding an element `e` using `U`, so either `I` is independent not containing `e`,
or `I = insert e J` for some `M`-independent set `J` whose closure isn't in `U`. -/
def ModularCut.ExtIndep (U : M.ModularCut) (e : α) (I : Set α) : Prop :=
  (M.Indep I ∧ e ∉ I) ∨ (M.Indep (I \ {e}) ∧ M.closure (I \ {e}) ∉ U ∧ e ∈ I)

lemma ModularCut.extIndep_iff_of_not_mem (heI : e ∉ I) : U.ExtIndep e I ↔ M.Indep I := by
  simp [ExtIndep, heI]

lemma Indep.extIndep (hI : M.Indep I) (he : e ∉ M.E) : U.ExtIndep e I :=
  .inl ⟨hI, not_mem_subset hI.subset_ground he⟩

lemma ModularCut.extIndep_iff_of_mem (heI : e ∈ I) :
    U.ExtIndep e I ↔ M.Indep (I \ {e}) ∧ M.closure (I \ {e}) ∉ U := by
  simp [ExtIndep, heI]

lemma ModularCut.ExtIndep.diff_singleton_indep {U : M.ModularCut} (h : U.ExtIndep e I) :
    M.Indep (I \ {e}) := by
  obtain (h | h) := h; exact h.1.diff _; exact h.1

lemma ModularCut.ExtIndep.subset (h : U.ExtIndep e I) (hJI : J ⊆ I) : U.ExtIndep e J := by
  by_cases heJ : e ∈ J
  · rw [extIndep_iff_of_mem (hJI heJ)] at h
    rw [extIndep_iff_of_mem heJ, and_iff_right (h.1.subset (diff_subset_diff_left hJI))]
    exact fun hJU ↦ h.2 <| U.closure_superset_mem' hJU <| diff_subset_diff_left hJI
  rw [extIndep_iff_of_not_mem heJ]
  exact h.diff_singleton_indep.subset (subset_diff_singleton hJI heJ)

lemma ModularCut.ExtIndep.subset_insert_ground (h : U.ExtIndep e I) : I ⊆ insert e M.E :=
  diff_singleton_subset_iff.1 h.diff_singleton_indep.subset_ground

/-- This lemma gives the conditions under which `I` is a maximal `ExtIndep` subset of `X`;
it is essentially characterizing when `I` is a basis of `X` in the matroid
`M.extendBy e U` before `M.extendBy e U` has actually been shown to be a matroid.

We need the lemma here because it is invoked several times when defining `M.extendBy e U`,
but it should not be used elsewhere; good API versions should be stated in terms of
`(M.extendBy e U).IsBasis`, and have less of a dense mess of logic on the RHS. -/
private lemma ModularCut.maximal_extIndep_iff (hX : X ⊆ insert e M.E) (hI : U.ExtIndep e I)
    (hIX : I ⊆ X) : Maximal (fun J ↦ U.ExtIndep e J ∧ J ⊆ X) I ↔
        (M.closure (I \ {e}) = M.closure (X \ {e}) ∧ ((e ∈ I ↔ M.closure (X \ {e}) ∈ U) → e ∉ X))
      ∨ ((M.closure (I \ {e}) ⋖[M] M.closure (X \ {e})) ∧ e ∈ I ∧ M.closure (X \ {e}) ∈ U) := by

  have hss : I \ {e} ⊆ X \ {e} := diff_subset_diff_left hIX
  have hX' : X \ {e} ⊆ M.E := by simpa
  rw [maximal_iff_forall_insert (fun _ _ ht hst ↦ ⟨ht.1.subset hst, hst.trans ht.2⟩)]

  simp only [hI, hIX, and_self, insert_subset_iff, and_true, not_and, true_and, imp_not_comm]

  refine ⟨fun h ↦ ?_, fun h x hxI hi hind ↦ ?_⟩
  · simp only [ExtIndep, insert_subset_iff, hIX, and_true, imp_not_comm, not_or, not_and,
      not_not] at h

    obtain (heI | heI) := em (e ∈ I)
    · rw [extIndep_iff_of_mem heI] at hI
      obtain (hclosure | hclosure) := em (M.closure (X \ {e}) ∈ U)
      · simp only [heI, hclosure, not_true_eq_false, imp_false, and_self, and_true]
        refine .inr <| U.covBy_of_maximal_closure (M.closure_subset_closure hss)
          hclosure hI.2 fun x ⟨hx, hxclosure⟩ ↦ ?_
        specialize h x
        have hxI : x ∉ I := by simpa [hx.2] using not_mem_of_mem_diff_closure ⟨hX' hx, hxclosure⟩
        rw [← insert_diff_singleton_comm hx.2, hI.1.insert_indep_iff] at h
        exact (h hxI hx.1).2 (.inl ⟨hX' hx, hxclosure⟩) (.inr heI)

      simp only [heI, hclosure, iff_false, not_true_eq_false, not_false_eq_true, implies_true,
        and_true, and_false, or_false]
      refine (M.closure_subset_closure hss).antisymm
        (M.closure_subset_closure_of_subset_closure fun x hx ↦ by_contra fun hxcl ↦ hclosure ?_)
      have hxI : x ∉ I := by simpa [hx.2] using not_mem_of_mem_diff_closure ⟨(hX' hx), hxcl⟩

      replace h := show M.closure (insert x (I \ {e})) ∈ U by
        simpa [hxI, hx.1, heI, ← insert_diff_singleton_comm hx.2, hI.1.insert_indep_iff,
          hX' hx, hxcl] using h x

      exact U.closure_superset_mem' h (insert_subset hx hss)
    simp only [mem_insert_iff, heI, or_false] at h
    have hXI : M.closure (X \ {e}) = M.closure (I \ {e}) := by
      refine (M.closure_subset_closure hss).antisymm'
        (M.closure_subset_closure_of_subset_closure fun x hx ↦ ?_)
      rw [hI.diff_singleton_indep.mem_closure_iff', and_iff_right (hX' hx), mem_diff,
        and_iff_left hx.2, diff_singleton_eq_self heI]
      exact fun h' ↦ by_contra fun hxI ↦ by simp [(h x hxI hx.1).1 h'] at hx

    simp only [heI, not_false_eq_true, diff_singleton_eq_self, hXI, false_iff, not_imp_not,
      true_and, false_and, and_false, or_false]
    intro heX
    rw [extIndep_iff_of_not_mem heI] at hI
    simpa [heI, hI] using (h e heI heX).2

  by_cases heI : e ∈ I
  · have hxe : x ≠ e := by rintro rfl; contradiction
    rw [extIndep_iff_of_mem heI] at hI
    rw [extIndep_iff_of_mem (.inr heI), ← insert_diff_singleton_comm hxe,
      hI.1.insert_indep_iff_of_not_mem (by simp [hxI, hxe])] at hind
    simp only [hIX heI, heI, true_iff, true_implies, true_and] at h
    obtain (⟨h_eq, -⟩ | ⟨hcv, h⟩) := h
    · exact not_mem_of_mem_diff_closure (h_eq ▸ hind.1) <| by simp [hi, hxe]
    rw [hcv.eq_closure_insert_of_mem_diff ⟨M.mem_closure_of_mem ⟨hi, hxe⟩, hind.1.2⟩,
      closure_insert_closure_eq_closure_insert] at h
    exact hind.2 h

  simp only [heI, not_false_eq_true, diff_singleton_eq_self, false_iff, not_not, false_and,
    and_false, or_false] at h
  obtain (rfl | hne) := eq_or_ne e x
  · rw [extIndep_iff_of_mem (.inl rfl)] at hind
    simp only [mem_singleton_iff, insert_diff_of_mem, hxI, not_false_eq_true,
      diff_singleton_eq_self, h.1] at hind
    exact hind.2 <| h.2 hi

  rw [extIndep_iff_of_not_mem heI] at hI
  rw [extIndep_iff_of_not_mem (by simp [heI, hne]), hI.insert_indep_iff_of_not_mem hxI, h.1] at hind
  refine not_mem_of_mem_diff_closure hind ⟨hi, hne.symm⟩

/-- This lemma is true even when `e` *is* a coloop of `M`, but it is easier to prove this first and
then reduce the stronger version to this one; see `ModularCut.extIndep_aug`. -/
private lemma ModularCut.extIndep_aug_of_not_coloop (U : ModularCut M) (he : ¬ M.Coloop e)
    (hI : U.ExtIndep e I) (hInmax : ¬ Maximal (U.ExtIndep e) I) (hBmax : Maximal (U.ExtIndep e) B) :
    ∃ x ∈ B \ I, U.ExtIndep e (insert x I) := by
  rw [coisLoop_iff_diff_closure, not_not] at he
  by_contra! hcon

  have hB : U.ExtIndep e B := hBmax.1
  have hIeE := hI.diff_singleton_indep.subset_ground
  have hBeE := hB.diff_singleton_indep.subset_ground
  have hss : B \ {e} ⊆ (I ∪ B) \ {e} := diff_subset_diff_left subset_union_right

  have hIBe : I ∪ B ⊆ insert e M.E :=
    union_subset hI.subset_insert_ground hB.subset_insert_ground
  have hIBe' : (I ∪ B) \ {e} ⊆ M.E := by rwa [diff_singleton_subset_iff]

  have hImax : Maximal (fun J ↦ U.ExtIndep e J ∧ J ⊆ I ∪ B) I := by
    rw [maximal_iff_forall_insert (fun _ _ ht hst ↦ ⟨ht.1.subset hst, hst.trans ht.2⟩),
      and_iff_right hI, and_iff_right subset_union_left]
    intro x hxI h'
    rw [insert_subset_iff, mem_union, or_iff_right hxI] at h'
    exact hcon x ⟨h'.2.1, hxI⟩ h'.1

  have hrw : U.ExtIndep e = fun J ↦ U.ExtIndep e J ∧ J ⊆ insert e M.E := by
    ext x
    simp only [iff_self_and]
    exact ExtIndep.subset_insert_ground

  rw [hrw, U.maximal_extIndep_iff Subset.rfl hI hI.subset_insert_ground] at hInmax
  rw [hrw, U.maximal_extIndep_iff Subset.rfl hB hB.subset_insert_ground] at hBmax
  rw [U.maximal_extIndep_iff hIBe hI subset_union_left] at hImax

  obtain (rfl | hU) := U.eq_bot_or_ground_mem
  · replace hBmax := show M.Spanning (B \ {e}) ∧ e ∈ B by
      simpa [← spanning_iff_closure_eq hBeE, he] using hBmax
    replace hInmax := show M.Spanning (I \ {e}) → e ∉ I by
      simpa [← spanning_iff_closure_eq hIeE, he] using hInmax
    replace hImax := show M.Spanning (I \ {e}) ∧ e ∈ I by
      simpa [hBmax.2, he, hBmax.1.closure_eq_of_superset hss,
        ← spanning_iff_closure_eq hIeE] using hImax
    exact hInmax hImax.1 hImax.2

  simp only [mem_singleton_iff, insert_diff_of_mem, he, ← spanning_iff_closure_eq hBeE, hU,
    iff_true, mem_insert_iff, true_or, not_true_eq_false, imp_false, ← isHyperplane_iff_covBy,
    and_true, ← spanning_iff_closure_eq hIeE, not_or, not_and, not_not] at hBmax hInmax

  by_cases hsp : M.Spanning ((I ∪ B) \ {e})
  · by_cases heI : e ∈ I
    · replace hImax := show M.IsHyperplane (M.closure (I \ {e})) by
        simpa [hsp.closure_eq, heI, hU, ← isHyperplane_iff_covBy] using hImax
      exact hInmax.2 hImax heI
    replace hInmax := show ¬ M.Spanning (I \ {e}) by simpa [heI, hU] using hInmax
    replace hImax := show M.closure (I \ {e}) = M.E by
      simpa [hsp.closure_eq, heI, he, hU] using hImax
    rw [spanning_iff_closure_eq hIeE] at hInmax
    contradiction

  obtain (⟨hBsp, -⟩ | ⟨hBhp, heB⟩) := hBmax
  · exact hsp <| hBsp.superset hss hIBe'

  have hclclosure : M.closure (B \ {e}) = M.closure ((I ∪ B) \ {e}) := by
    refine by_contra fun hne ↦ hsp <| ?_
    rw [← closure_spanning_iff hIBe']
    have hssu := (M.closure_subset_closure hss).ssubset_of_ne hne
    exact hBhp.spanning_of_ssuperset hssu <| closure_subset_ground _ _

  rw [extIndep_iff_of_mem heB] at hB
  replace hImax := show M.closure (I \ {e}) = M.closure (B \ {e}) ∧ e ∈ I by
    simpa [heB, ← hclclosure, hB.2] using hImax

  replace hInmax := show ¬M.IsHyperplane (M.closure (I \ {e})) by simpa [hImax.2] using hInmax
  exact hInmax <| (hImax.1.symm ▸ hBhp)

private lemma ModularCut.extIndep_aug (U : ModularCut M) (hI : U.ExtIndep e I)
    (hInmax : ¬ Maximal (U.ExtIndep e) I) (hBmax : Maximal (U.ExtIndep e) B) :
    ∃ x ∈ B \ I, U.ExtIndep e (insert x I) := by
  obtain (he | he) := em' (M.Coloop e)
  · exact U.extIndep_aug_of_not_coloop he hI hInmax hBmax
  have hrw : (U.delete {e}).ExtIndep e = U.ExtIndep e := by
    ext; simp [ExtIndep, he.mem_closure_iff_mem, ModularCut.mem_delete_elem_iff]
  simp_rw [← hrw] at hInmax hBmax hI ⊢
  exact (U.delete {e}).extIndep_aug_of_not_coloop (fun h ↦ h.mem_ground.2 rfl) hI hInmax hBmax

private lemma ModularCut.existsMaximalSubsetProperty (U : M.ModularCut) (hXE : X ⊆ insert e M.E) :
  ExistsMaximalSubsetProperty (U.ExtIndep e) X := by
  intro I hI hIX
  obtain ⟨J, hJ, hIJ⟩ :=
    hI.diff_singleton_indep.subset_isBasis_of_subset (diff_subset_diff_left hIX)

  obtain ⟨hJX, heJ⟩ : J ⊆ X ∧ e ∉ J := by simpa [subset_diff] using hJ.subset
  have hJi : U.ExtIndep e J := .inl ⟨hJ.indep, heJ⟩
  by_contra! hcon

  have hconJe : e ∈ X → M.closure (X \ {e}) ∈ U := by
    refine fun heX ↦ by_contra fun hclosure ↦ ?_
    have hind : U.ExtIndep e (insert e J) := by
      rw [extIndep_iff_of_mem (.inl rfl)]
      simpa [heJ, hJ.indep, hJ.closure_eq_closure]
    specialize hcon (insert e J) (by simpa using hIJ)
    rw [maximal_extIndep_iff  hXE hind (insert_subset heX hJX)] at hcon
    simp [heJ, hJ.closure_eq_closure, hclosure] at hcon

  have heI : e ∈ I := by
    refine by_contra fun heI ↦ ?_
    rw [diff_singleton_eq_self heI] at hIJ
    have h' : M.closure (X \ {e}) ∉ U ∧ e ∈ X := by
      simpa [maximal_extIndep_iff hXE hJi hJX, heJ, hJ.closure_eq_closure] using hcon J hIJ
    exact h'.1 <| hconJe h'.2

  rw [extIndep_iff_of_mem heI] at hI
  specialize hconJe (hIX heI)

  obtain (rfl | hssu) := hIJ.eq_or_ssubset
  · rw [hJ.closure_eq_closure] at hI; exact hI.2 hconJe

  refine hI.2 <| U.mem_of_ssubset_indep_of_forall_diff hJ.indep hssu (fun x hx ↦ ?_)
  by_contra! hJu
  have hxe : x ≠ e := by rintro rfl; simp [heJ] at hx
  have hxJI : x ∈ J \ I := by simpa [hxe] using hx

  set J' := insert e (J \ {x}) with hJ'
  have hIeJx : I ⊆ J' := by
    simpa [hJ', insert_diff_singleton_comm hxe.symm, subset_diff, hxJI.2] using hIJ

  have hJ'e : J' \ {e} = J \ {x} := by simp [hJ', insert_diff_self_of_not_mem, heJ]
  specialize hcon J' hIeJx

  have hind : U.ExtIndep e J' := by
    simp only [extIndep_iff_of_mem (show e ∈ J' from .inl rfl), hJ'e]
    exact ⟨hJ.indep.diff _, hJu⟩

  have hJ'X : J' ⊆ X := insert_subset (hIX heI) (diff_subset.trans hJX)

  have hconJ' : (M.closure (J \ {x}) = M.closure J → e ∈ X) ∧
    ¬M.CovBy (M.closure (J \ {x})) (M.closure J) := by
    rw [maximal_extIndep_iff hXE hind hJ'X, iff_true_intro hconJe] at hcon
    simpa [hJ'e, ← hJ.closure_eq_closure, show e ∈ J' from .inl rfl] using hcon

  exact hconJ'.2 <| hJ.indep.closure_diff_covBy hxJI.1

/-- Extend a matroid `M` by a new element `e` using a modular cut `U`.
(If `e` already belongs to `M`, then this gives the extension of `M ＼ e` by `e` using `U`.) -/
@[simps!] def extendBy (M : Matroid α) (e : α) (U : M.ModularCut) : Matroid α :=
  IndepMatroid.matroid <| IndepMatroid.mk
    (E := insert e M.E)
    (Indep := U.ExtIndep e)
    (indep_empty := Or.inl ⟨M.empty_indep, not_mem_empty _⟩)
    (indep_subset := fun _ _ ↦ ModularCut.ExtIndep.subset )
    (indep_aug := fun _ _ ↦ U.extIndep_aug)
    (indep_maximal := fun _ ↦ U.existsMaximalSubsetProperty)
    (subset_ground := fun _ ↦ ModularCut.ExtIndep.subset_insert_ground)

lemma ModularCut.deleteElem_extendBy (he : e ∈ M.E) :
    (M ＼ e).extendBy e (ModularCut.ofDeleteElem M e) = M := by
  refine Eq.symm <| ext_indep (by simp [he]) fun I hI ↦ ?_
  obtain (heI | heI) := em' (e ∈ I); simp [extIndep_iff_of_not_mem heI, heI]
  obtain ⟨I, rfl, heI'⟩ : ∃ J, I = insert e J ∧ e ∉ J := ⟨I \ {e}, by simp [heI], by simp⟩
  suffices
    M.Indep (insert e I) ↔ M.Indep I ∧ (e ∈ M.closure (M.closure I \ {e}) →
      ¬M.IsFlat (insert e (M.closure I))) by
    simpa [extIndep_iff_of_mem heI, heI']

  refine ⟨fun h ↦ ⟨h.subset (subset_insert _ _), fun he _ ↦ ?_⟩, fun ⟨hIi, h⟩ ↦ ?_⟩
  · suffices e ∈ M.closure (M.closure I) from
      h.not_mem_closure_diff_of_mem (.inl rfl) <| by simpa [heI']
    exact (M.closure_subset_closure diff_subset) he
  rw [hIi.insert_indep_iff_of_not_mem heI', mem_diff, and_iff_right (hI (.inl rfl))]
  refine fun heclosure ↦ ?_
  simp only [heclosure, insert_eq_of_mem, closure_isFlat, not_true_eq_false, imp_false] at h
  exact h <| (M.closure_subset_closure <| subset_diff_singleton
    (M.subset_closure I hIi.subset_ground) heI') heclosure

lemma ModularCut.extendBy_deleteElem (U : M.ModularCut) (he : e ∉ M.E) :
    (M.extendBy e U) ＼ e = M := by
  refine ext_indep (by simpa) fun I hI ↦ ?_
  obtain ⟨-, heI⟩ := show I ⊆ M.E ∧ e ∉ I by simpa [subset_diff] using hI
  simp [deleteElem, extIndep_iff_of_not_mem heI, heI]

lemma extendBy_injective (M : Matroid α) (he : e ∉ M.E) : Injective (M.extendBy e) := by
  refine fun U U' h_eq ↦ SetLike.coe_set_eq.1 (Set.ext fun F ↦ ?_)
  obtain (hF | hF) := em' (M.IsFlat F)
  · exact iff_of_false (hF ∘ U.isFlat_of_mem) (hF ∘ U'.isFlat_of_mem)
  obtain ⟨I, hI⟩ := M.exists_isBasis F
  have heI : e ∉ I := not_mem_subset hI.indep.subset_ground he
  apply_fun (fun M ↦ M.Indep (insert e I)) at h_eq
  simpa [extendBy_Indep, ModularCut.extIndep_iff_of_mem (mem_insert e I), heI, hI.indep,
    not_iff_not, ← hF.eq_closure_of_isBasis hI] using h_eq

/-- Single-element extensions are equivalent to modular cuts. -/
def extensionEquivModularCut (M : Matroid α) (he : e ∉ M.E) :
    {N : Matroid α // (e ∈ N.E ∧ N ＼ e = M)} ≃ M.ModularCut where
  toFun N := (ModularCut.ofDeleteElem N e).copy N.2.2
  invFun U := ⟨M.extendBy e U, by simp, U.extendBy_deleteElem he⟩
  left_inv := by
    rintro ⟨N, heN, rfl⟩
    simp only [deleteElem, coe_setOf, mem_setOf_eq, Subtype.mk.injEq]
    exact ModularCut.deleteElem_extendBy heN
  right_inv := by
    apply rightInverse_of_injective_of_leftInverse
    · exact fun U U' hUU' ↦ extendBy_injective M he (by simpa using hUU')
    rintro ⟨N, heN, rfl⟩
    simp only [deleteElem, coe_setOf, mem_setOf_eq, Subtype.mk.injEq]
    exact ModularCut.deleteElem_extendBy heN

lemma ModularCut.mem_closure_extendBy_iff (U : M.ModularCut) (he : e ∉ M.E) :
    e ∈ (M.extendBy e U).closure X ↔ e ∈ X ∨ M.closure X ∈ U := by
  by_cases heX : e ∈ X
  · simp [heX, mem_closure_of_mem']
  obtain ⟨I, hI⟩ := (M.extendBy e U).exists_isBasis' X
  have hI' : M.IsBasis' I X
  · rwa [← U.extendBy_deleteElem he, deleteElem, delete_isBasis'_iff, diff_singleton_eq_self heX]

  have heI := not_mem_subset hI'.subset heX
  rw [← hI.closure_eq_closure, ← hI'.closure_eq_closure, or_iff_right heX,
    ← not_iff_not, hI.indep.not_mem_closure_iff_of_not_mem heI, extendBy_Indep,
    U.extIndep_iff_of_mem (.inl rfl)]
  simp [heI, hI'.indep]

lemma ModularCut.extendBy_closure_eq_self (U : M.ModularCut) (he : e ∉ M.E) (heX : e ∉ X)
    (hXU : M.closure X ∉ U) : (M.extendBy e U).closure X = M.closure X := by
  nth_rewrite 2 [← U.extendBy_deleteElem he]
  rw [deleteElem, delete_closure_eq, diff_singleton_eq_self heX, sdiff_eq_left.2]
  rw [disjoint_singleton_right, mem_closure_extendBy_iff _ he]
  simp [heX, hXU]

lemma ModularCut.extendBy_closure_eq_insert (U : M.ModularCut) (he : e ∉ M.E) (heX : e ∉ X)
    (hXSU : M.closure X ∈ U) : (M.extendBy e U).closure X = insert e (M.closure X) := by
  nth_rewrite 2 [← U.extendBy_deleteElem he]
  rw [deleteElem, delete_closure_eq, insert_diff_singleton]
  rw [diff_singleton_eq_self heX, eq_comm, insert_eq_self, U.mem_closure_extendBy_iff he]
  exact .inr hXSU

end extensions

section projection

private lemma projectBy_aux (U : M.ModularCut) :
    ((((M.map _ (some_injective _).injOn).extendBy none
    (U.map _ (some_injective _).injOn)) ／ (none : Option α)).comap Option.some).Indep I ↔
    M.Indep I ∧ (U ≠ ⊤ → M.closure I ∉ U) := by
  have hinj := Option.some_injective α
  obtain (rfl | hU) := eq_or_ne U ⊤
  · rw [contractElem, contract_eq_delete_of_subset_loops]
    · simp [ModularCut.extIndep_iff_of_not_mem, image_eq_image hinj, hinj.injOn]
    rw [singleton_subset_iff, ← isLoop_iff, ← singleton_dep, dep_iff]
    simp [ModularCut.extIndep_iff_of_mem, map_closure_eq, ModularCut.map, image_eq_image hinj]
  simp only [contractElem, comap_indep_iff, hinj.injOn, and_true, ne_eq, hU, not_false_eq_true,
    forall_const]
  rw [Indep.contract_indep_iff]
  · simp [ModularCut.extIndep_iff_of_mem, image_eq_image hinj, map_closure_eq,
      preimage_image_eq _ hinj, ModularCut.map, hU]
  suffices M.loops ∉ U by
    simpa [ModularCut.extIndep_iff_of_mem, (eq_comm (a := ∅)), map_closure_eq, ModularCut.map,
      image_eq_image hinj]
  rwa [Ne, ModularCut.eq_top_iff] at hU

/-- Extend `M` using the modular cut `U`, and contract the new element.
Defining this in terms of `extendBy` would be difficult if `M.E = univ`,
so we define it directly instead.   -/
def projectBy (M : Matroid α) (U : M.ModularCut) : Matroid α := Matroid.ofExistsMatroid
  (E := M.E)
  (Indep := fun I ↦ M.Indep I ∧ (U ≠ ⊤ → M.closure I ∉ U))
  (hM := ⟨_, by simp [(Option.some_injective α).preimage_image], fun _ ↦ projectBy_aux U⟩)

/-- The messier expression for `projectBy`; `projectBy` is obtained from `M` by `map`ping it
into `Option α`, extending by the new element `none` and contracting it, then `comap`ping
back to `α`.  -/
lemma projectBy_eq_map_comap (U : M.ModularCut) :
    M.projectBy U = ((((M.map _ (some_injective _).injOn).extendBy none
      (U.map _ (some_injective _).injOn)) ／ (none : Option α)).comap Option.some) := by
  refine ext_indep (by simp [projectBy, (Option.some_injective α).preimage_image]) fun I _ ↦ ?_
  rw [projectBy_aux, projectBy, Matroid.ofExistsMatroid]
  simp

@[simp] lemma projectBy_ground_eq (U : M.ModularCut) : (M.projectBy U).E = M.E := rfl

@[simp] lemma projectBy_indep_iff (U : M.ModularCut) :
    (M.projectBy U).Indep I ↔ M.Indep I ∧ (U ≠ ⊤ → M.closure I ∉ U) := Iff.rfl

lemma projectBy_indep_iff_of_ne_top {I : Set α} (hU : U ≠ ⊤) :
    (M.projectBy U).Indep I ↔ M.Indep I ∧ M.closure I ∉ U := by
  simp [hU]

lemma projectBy_top : M.projectBy ⊤ = M := by
  simp [ext_iff_indep]

@[simp] lemma extendBy_contract_eq (U : M.ModularCut) (he : e ∉ M.E) :
    (M.extendBy e U) ／ e = M.projectBy U := by
  refine ext_indep (by simpa) fun I hI ↦ ?_
  have ⟨hIE, heI⟩ : I ⊆ M.E ∧ e ∉ I := by simpa [subset_diff] using hI
  obtain rfl | hU := eq_or_ne U ⊤
  · have hl : (M.extendBy e ⊤).IsLoop e
    · rw [← singleton_dep, dep_iff, extendBy_Indep,
      ModularCut.extIndep_iff_of_mem (show e ∈ {e} from rfl)]
      simp
    rw [contractElem, contract_eq_delete_of_subset_loops (by simpa), delete_indep_iff,
      extendBy_Indep, ModularCut.extIndep_iff_of_not_mem heI, projectBy_indep_iff]
    simp [heI]
  have hnl : (M.extendBy e U).IsNonloop e
  · rw [← indep_singleton, extendBy_Indep, ModularCut.extIndep_iff_of_mem (by simp)]
    simpa [← U.eq_top_iff]
  rw [contractElem, hnl.indep.contract_indep_iff, union_singleton, extendBy_Indep,
    ModularCut.extIndep_iff_of_mem (mem_insert _ _), projectBy_indep_iff]
  simp [hU, heI]

end projection

section ExtendContract

variable {M N : Matroid α} {C D : Set α}

lemma exists_common_major_of_contract_eq_deleteElem (heC : e ∉ C) (hC : C ⊆ M.E)
    (h_eq : M ／ C = N ＼ e) : ∃ (P : Matroid α), P ＼ e = M ∧ P ／ C = N := by
  have heM : e ∉ M.E := fun heM ↦ by simpa [h_eq] using show e ∈ (M ／ C).E from ⟨heM, heC⟩
  obtain heN | heN := em' <| e ∈ N.E
  · use M
    rw [h_eq, deleteElem, deleteElem, ← delete_inter_ground_eq, Disjoint.inter_eq (by simpa),
      ← N.delete_inter_ground_eq, Disjoint.inter_eq (by simpa)]
    simp

  set UN := ModularCut.ofDeleteElem N e with hUN
  set UM := (UN.copy h_eq.symm).ofContract hC
  use M.extendBy e UM
  rw [ModularCut.extendBy_deleteElem _ heM, and_iff_right rfl]
  refine ext_indep ?_ ?_
  · rw [contract_ground, extendBy_E, insert_diff_of_not_mem _ heC, ← contract_ground, h_eq,
      deleteElem, delete_ground]
    simpa
  obtain ⟨IC, hIC⟩ := M.exists_isBasis C
  have heIC : e ∉ IC := not_mem_subset hIC.subset heC
  have hIC' : (M.extendBy e UM).IsBasis IC C
  · rw [← UM.extendBy_deleteElem heM, deleteElem, delete_isBasis_iff] at hIC
    exact hIC.1
  intro I
  simp only [contract_ground, extendBy_E]
  rw [hIC'.contract_indep_iff, extendBy_Indep, subset_diff, and_imp, disjoint_comm]
  simp +contextual only [and_true]
  intro hIE hdj

  obtain heI | heI := em' (e ∈ I)
  · rw [ModularCut.extIndep_iff_of_not_mem (by simp [heI, heIC]),
      show N.Indep I ↔ (N ＼ e).Indep I by simp [heI], ← h_eq, hIC.contract_indep_iff,
      and_iff_left hdj]

  have hrw1 : M.closure ((I ∪ IC) \ {e}) = M.closure ((I \ {e}) ∪ C)
  · rw [union_diff_distrib, diff_singleton_eq_self heIC,
      closure_union_congr_right hIC.closure_eq_closure]

  have hrw2 : (I \ {e}) ∪ IC = (I ∪ IC) \ {e}
  · rw [union_diff_distrib, diff_singleton_eq_self heIC]

  have hrw3 : N.Indep I ↔ (N ＼ e).Indep (I \ {e}) ∧ (N ＼ e).closure (I \ {e}) ∉ UN
  · nth_rw 1 [← ModularCut.deleteElem_extendBy heN, ← hUN]
    rw [extendBy_Indep, ModularCut.extIndep_iff_of_mem heI]

  have hwin : C ⊆ M.closure (I \ {e} ∪ C) := M.subset_closure_of_subset' subset_union_right

  rw [UM.extIndep_iff_of_mem (.inl heI)]
  simp [← h_eq, hrw1, hrw2, hrw3, hwin, hIC.contract_indep_iff, hdj.mono_right diff_subset, UM]

lemma exists_common_major_of_delete_eq_contractElem (heD : e ∉ D) (hD : D ⊆ M.E)
    (h_eq : M ＼ D = N ／ e) : ∃ (P : Matroid α), P ／ e = M ∧ P ＼ D = N := by
  rw [← dual_inj, delete_dual_eq_dual_contract, contractElem, contract_dual_eq_dual_delete] at h_eq
  obtain ⟨P, hPM, hPN⟩ := exists_common_major_of_contract_eq_deleteElem (by simpa) (by simpa) h_eq
  rw [eq_dual_iff_dual_eq] at hPM hPN
  refine ⟨P✶, by simpa using hPM, by simpa using hPN⟩

/-- If the contract-set is finite and disjoint from the delete-sets,
then any two matroids with a common minor have a common major. -/
lemma exists_common_major_of_contract_eq_delete {D : Finset α} (hCD : Disjoint C D) (hCE : C ⊆ M.E)
    (h_eq : M ／ C = N ＼ (D : Set α)) : ∃ (P : Matroid α), P ＼ (D : Set α) = M ∧ P ／ C = N := by
  classical
  induction' D using Finset.induction with e D heD IH generalizing N
  · exact ⟨M, by simp, by simpa using h_eq⟩

  obtain ⟨hCD, heC⟩ : Disjoint C ↑D ∧ e ∉ C := by simpa [← union_singleton] using hCD

  simp_rw [Finset.coe_insert, ← singleton_union, ← delete_delete] at h_eq ⊢

  obtain ⟨P', hP'M, hP'N⟩ := IH hCD h_eq
  have hCE' : C ⊆ P'.E
  · rw [← hP'M] at hCE
    exact hCE.trans diff_subset
  obtain ⟨Q, hQ, rfl, hQN⟩ := exists_common_major_of_contract_eq_deleteElem heC hCE' hP'N
  exact ⟨Q, by rwa [← hQ] at hP'M, rfl⟩

end ExtendContract

section LinearClass

/-
TODO. I think linear classes only work for finite matroids; if `B` and `B'` are disjoint infinite
bases of `M`, the class of hyperplanes `H` with `B\H` finite ought not to be a linear class,
but I don't know what reasonable definition would forbid that.
-/

-- def LinearClass (M : Matroid α) where
--   carrier : Set (Set α)
--   forall_isHyperplane : ∀ H ∈ carrier, M.IsHyperplane H
--   forall_hyper' : ∀ H₁ H₂ ∈ carrier,

end LinearClass
