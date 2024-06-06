import Matroid.ForMathlib.Order.Minimal
import Matroid.ForMathlib.MatroidBasic
import Matroid.Modular

/-

# Extensions

If `M` is a matroid and `e` is an element outside the ground set of `M`,
a single-element extension of `M` by `e` is a matroid `M'` for which
`M'.E = M.E ∪ {e}` and `M' ＼ e = M`.

In 1965, Crapo proved that the single-element extensions of a finite matroid `M` are
described precisely by the 'modular cuts' of `M`; a modular cut is an upper ideal in the
lattice of flats of `M` that is closed under taking intersections of modular pairs.
(in a finite matroid, `A,B` is  modular pair if `r A + r B = r (A ∪ B) + r (A ∩ B)`).
Given a modular cut `U`, the flats of `M` spanning the new element `e` in the extension `M'` are
precisely those in `U`. See [Oxley 7.2].

For infinite matroids, this condition fails; for instance, if `M` is a free matroid
on an infinite ground set, and `U` is the collection of all sets of `M` with finite complement,
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
of arbitrary matroids, and show that they specialize to Crapo's modular cuts in the finite case.
We also define the 'projection' of `M` associated with each modular cut `U` of `M`; this is the
matroid obtained from `M` by extending using `U`, then contracting the new element.

# Main Definitions.

* `Matroid.ModularCut` : a collection of flats in a matroid closed under taking superflats and
    under intersections of modular families.

* `ModularCut.principal M X` : the modular cut of `M` comprising all the flats containing `X`

* `ModularCut.restrict` : the restriction of a modular cut to a restriction of `M`.

* `ModularCut.ofDeleteElem` : the modular cut of `M ＼ e` corresponding to the extension `M`
    of `M ＼ e`.

* `ModularCut.ofForallModularPairInter` : in the finite case, a modular cut in the classical sense
    gives a modular cut in the more general sense.

* `Matroid.extendBy e U` : add an element `e` to a matroid `M` using a modular cut `U`.

* `Matroid.extensionEquiv` : the equivalence between single-element extensions of `M`
    and modular cuts of `M`.

* `Matroid.projectBy e U` : add and then contract a new element in a matroid `M`
  using a modular cut `U`.

* `Matroid.truncate` : add a new element freely spanned by `M.E`, then contract it.

-/

open Set Function Set.Notation

variable {α : Type*} {M : Matroid α} {I J B F₀ F F' X Y : Set α} {e f : α}

namespace Matroid

/-- A `ModularCut M` is a collection of flats of `M` that is closed under taking superflats and
under intersections of modular families. These parametrize the extensions of `M` by a single
element outside `M` and hence also the projections of `M`; see `Matroid.extendBy` and
`Matroid.projectBy`.  -/
@[ext] structure ModularCut (M : Matroid α) where
  (carrier : Set (Set α))
  (forall_flat : ∀ F ∈ carrier, M.Flat F)
  (forall_superset : ∀ F F', F ∈ carrier → M.Flat F' → F ⊆ F' → F' ∈ carrier)
  (forall_inter : ∀ Fs ⊆ carrier, Fs.Nonempty → M.ModularFamily (fun x : Fs ↦ x) → ⋂₀ Fs ∈ carrier)

variable {U : M.ModularCut}

instance (M : Matroid α) : SetLike (ModularCut M) (Set α) where
  coe := ModularCut.carrier
  coe_injective' U U' := by cases U; cases U'; simp

/-- Transfer a `ModularCut` across an equality. -/
def ModularCut.congr {N : Matroid α} (U : M.ModularCut) (hNM : M = N) : N.ModularCut where
  carrier := U
  forall_flat := by obtain rfl := hNM; exact U.forall_flat
  forall_superset := by obtain rfl := hNM; exact U.forall_superset
  forall_inter := by obtain rfl := hNM; exact U.forall_inter

/-- Transfer a `ModularCut` along an injection -/
def ModularCut.map {β : Type*} (U : M.ModularCut) (f : α → β) (hf : M.E.InjOn f) :
    (M.map f hf).ModularCut where
  carrier := (image f) '' U
  forall_flat := by
    rintro _ ⟨F, hF, rfl⟩
    exact (U.forall_flat F hF).map hf
  forall_superset := by
    simp_rw [flat_map_iff']
    rintro _ F' ⟨F, hF, rfl⟩ ⟨F', hF', rfl⟩ hss
    refine ⟨F', U.forall_superset _ _ hF hF' ?_, rfl⟩
    rwa [← hf.image_subset_image_iff_of_subset (U.forall_flat F hF).subset_ground hF'.subset_ground]
  forall_inter := by
    simp_rw [modularFamily_map_iff, subset_image_iff]
    rintro _ ⟨Fs, hFs, rfl⟩ hne ⟨Ys, ⟨B, hB, hYs⟩, h_eq⟩
    have hFsE : ∀ F ∈ Fs, F ⊆ M.E := fun F hF ↦ (U.forall_flat F (hFs hF)).subset_ground
    have hwin := U.forall_inter Fs hFs (by simpa using hne) ⟨B, hB, ?_⟩
    · simp only [sInter_image, mem_image, SetLike.mem_coe]
      refine ⟨_, hwin, ?_⟩
      rw [← InjOn.image_biInter_eq (f := f) (by simpa using hne), sInter_eq_biInter]
      refine hf.mono ?_
      simpa only [iUnion_subset_iff]

    simp only [Subtype.forall]
    refine fun F hF ↦ ?_
    simp only [Subtype.forall, mem_image, forall_exists_index] at hYs h_eq
    specialize h_eq _ _ ⟨hF, rfl⟩
    specialize hYs _ _ ⟨hF, rfl⟩
    rw [hf.image_eq_image_iff_of_subset (hFsE F hF) hYs.subset_ground] at h_eq
    rwa [← h_eq] at hYs

@[simp] lemma ModularCut.mem_mk_iff (S : Set (Set α)) (h₁ : ∀ F ∈ S, M.Flat F)
  (h₂ : ∀ F F', F ∈ S → M.Flat F' → F ⊆ F' → F' ∈ S)
  (h₃ : ∀ xs ⊆ S, xs.Nonempty → M.ModularFamily (fun x : xs ↦ x) → ⋂₀ xs ∈ S) {X : Set α} :
  X ∈ ModularCut.mk S h₁ h₂ h₃ ↔ X ∈ S := Iff.rfl

lemma ModularCut.flat_of_mem (U : M.ModularCut) (hF : F ∈ U) : M.Flat F :=
    U.forall_flat F hF

lemma ModularCut.superset_mem (U : M.ModularCut) (hF : F ∈ U) (hF' : M.Flat F') (hFF' : F ⊆ F') :
    F' ∈ U :=
  U.forall_superset F F' hF hF' hFF'

lemma ModularCut.cl_superset_mem (U : M.ModularCut) (hF : F ∈ U) (hFX : F ⊆ M.cl X) : M.cl X ∈ U :=
  U.superset_mem hF (M.cl_flat _) hFX

lemma ModularCut.cl_superset_mem' (U : M.ModularCut) (hX : M.cl X ∈ U) (hXY : X ⊆ Y) : M.cl Y ∈ U :=
  U.cl_superset_mem hX (M.cl_subset_cl hXY)

lemma ModularCut.sInter_mem (U : M.ModularCut) {Fs : Set (Set α)} (hne : Fs.Nonempty) (hFs : Fs ⊆ U)
    (hFs_mod : M.ModularFamily (fun F : Fs ↦ F)) : ⋂₀ Fs ∈ U :=
  U.forall_inter Fs hFs hne hFs_mod

lemma ModularCut.iInter_mem (U : M.ModularCut) {ι : Type*} [Nonempty ι] (Fs : ι → Set α)
    (hFs : ∀ i, Fs i ∈ U) (hFs_mod : M.ModularFamily Fs) : ⋂ i, Fs i ∈ U := by
  have hwin := U.sInter_mem (Fs := range Fs) (range_nonempty Fs) ?_ ?_
  · simpa using hwin
  · rintro _ ⟨i, hi, rfl⟩; exact hFs i
  obtain ⟨B, hB, hB'⟩ := hFs_mod
  exact ⟨B, hB, by simpa⟩

lemma ModularCut.inter_mem (U : M.ModularCut) (hF : F ∈ U) (hF' : F' ∈ U) (h : M.ModularPair F F') :
    F ∩ F' ∈ U := by
  rw [inter_eq_iInter]
  apply U.iInter_mem
  · simp [hF, hF']
  exact h

lemma ModularCut.cl_mem_of_mem (hF : F ∈ U) : M.cl F ∈ U := by
  rwa [(U.flat_of_mem hF).cl]

/-- The `ModularCut` of all flats containing `X`. -/
@[simps] def ModularCut.principal (M : Matroid α) (X : Set α) : M.ModularCut where
  carrier := {F | M.Flat F ∧ X ⊆ F}
  forall_flat _ h := h.1
  forall_superset _ _ hF hF' hFF' := ⟨hF', hF.2.trans hFF'⟩
  forall_inter _ hS hne _ := ⟨Flat.sInter hne fun _ h ↦ (hS h).1, subset_sInter fun _ h ↦ (hS h).2⟩

@[simp] lemma ModularCut.mem_principal_iff : F ∈ principal M X ↔ M.Flat F ∧ X ⊆ F := Iff.rfl

@[simps] def ModularCut.empty (M : Matroid α) : M.ModularCut where
  carrier := ∅
  forall_flat := by simp
  forall_superset := by simp
  forall_inter := by simp [subset_empty_iff]

instance (M : Matroid α) : PartialOrder M.ModularCut where
  le U U' := (U : Set (Set α)) ⊆ U'
  le_refl _ := Subset.rfl
  le_trans _ _ _ := Subset.trans
  le_antisymm U U' h h' := by simpa using subset_antisymm h h'

lemma ModularCut.le_iff_subset {U U' : M.ModularCut} :
  U ≤ U' ↔ (U : Set (Set α)) ⊆ U' := Iff.rfl

instance (M : Matroid α) : BoundedOrder M.ModularCut where
  top := ModularCut.principal M ∅
  le_top U x h := by simpa using U.flat_of_mem h
  bot := ModularCut.empty M
  bot_le _ _ := by simp

lemma ModularCut.eq_bot_or_ground_mem (U : M.ModularCut) : U = ⊥ ∨ M.E ∈ U := by
  obtain (hU | ⟨F, hF⟩) := (U : Set (Set α)).eq_empty_or_nonempty
  · left
    ext x
    change x ∈ (U : Set (Set α)) ↔ x ∈ ∅
    simp [hU]
  exact .inr <| U.superset_mem hF M.ground_flat (U.flat_of_mem hF).subset_ground

@[simp] protected lemma ModularCut.not_mem_bot (M : Matroid α) (X : Set α) :
    ¬ X ∈ (⊥ : M.ModularCut) :=
  not_mem_empty X

protected lemma ModularCut.mem_top_of_flat (hF : M.Flat F) : F ∈ (⊤ : M.ModularCut) :=
  ⟨hF, empty_subset F⟩

@[simp] lemma ModularCut.mem_top_iff : F ∈ (⊤ : M.ModularCut) ↔ M.Flat F :=
  ⟨fun h ↦ h.1, ModularCut.mem_top_of_flat⟩

lemma ModularCut.eq_top_iff : U = ⊤ ↔ M.cl ∅ ∈ U := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro rfl
    exact ⟨M.cl_flat ∅, empty_subset _⟩
  simp only [SetLike.ext_iff, mem_top_iff]
  refine fun F ↦ ⟨U.flat_of_mem, fun h' ↦ U.superset_mem h h' h'.loops_subset⟩

lemma top_ne_bot (M : Matroid α) : (⊤ : M.ModularCut) ≠ (⊥ : M.ModularCut) := by
  rw [Ne, eq_comm, ModularCut.eq_top_iff]; simp

lemma principal_ground_ne_top (M : Matroid α) [RkPos M] : ModularCut.principal M M.E ≠ ⊤ := by
  simp only [Ne, ModularCut.eq_top_iff, ModularCut.mem_principal_iff, cl_flat, true_and]
  obtain ⟨B, hB⟩ := M.exists_base
  obtain ⟨e, heB⟩ := hB.nonempty
  exact fun h ↦ (hB.indep.nonloop_of_mem heB).not_loop <| h (hB.subset_ground heB)

lemma ModularCut.mem_of_ssubset_indep_of_forall_diff (U : M.ModularCut) (hI : M.Indep I)
    (hJI : J ⊂ I) (h : ∀ e ∈ I \ J, M.cl (I \ {e}) ∈ U) : M.cl J ∈ U := by
  set Is : ↑(I \ J) → Set α := fun e ↦ I \ {e.1} with hIs
  have hmod : M.ModularFamily Is := hI.modularFamily_of_subsets (by simp [hIs])
  have hne := nonempty_of_ssubset hJI
  have h_inter : ⋂ e, Is e = J := by
    rw [hIs, ← biInter_eq_iInter (t := fun x _ ↦ I \ {x}), biInter_diff_singleton_eq_diff _ hne,
      diff_diff_right, diff_self, empty_union, inter_eq_self_of_subset_right hJI.subset]
  have _ := hne.coe_sort
  rw [← h_inter, ← hmod.iInter_cl_eq_cl_iInter]
  exact U.iInter_mem _ (fun ⟨i, hi⟩ ↦ h _ (by simpa)) hmod.cls_modularFamily

/-- If `X` spans a flat outside `U`, but `X ∪ {y}` spans a flat in `U` for all `y ∈ Y \ M.cl X`,
then `M.cl X` is covered by `M.cl Y`. -/
lemma ModularCut.covBy_of_maximal_cl (U : M.ModularCut) {X Y : Set α} (hXY : M.cl X ⊆ M.cl Y)
    (hYU : M.cl Y ∈ U) (hXU : M.cl X ∉ U) (hmax : ∀ x ∈ Y \ M.cl X, M.cl (insert x X) ∈ U) :
      M.cl X ⋖[M] M.cl Y := by
  obtain ⟨I, hI⟩ := M.exists_basis' X
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_basis'_of_subset (hI.subset.trans (subset_union_left X Y))
  have hJ' := hJ.basis_cl_right
  rw [← cl_cl_union_cl_eq_cl_union, union_eq_self_of_subset_left hXY, cl_cl] at hJ'

  rw [← hI.cl_eq_cl, ← M.cl_cl Y, ← hJ'.cl_eq_cl]
  rw [← M.cl_cl Y, ← hJ'.cl_eq_cl] at hYU
  rw [← hI.cl_eq_cl] at hXU

  obtain (h | hnt) := (J \ I).subsingleton_or_nontrivial
  · obtain (he | ⟨e, he⟩) := h.eq_empty_or_singleton
    · rw [(diff_eq_empty.1 he).antisymm hIJ] at hYU; contradiction
    obtain rfl : J = insert e I := by rw [← union_diff_cancel hIJ, he, union_singleton]
    simpa [show e ∉ I from (he.symm.subset rfl).2] using hJ.indep.cl_diff_covBy (.inl rfl)

  obtain (rfl | hssu) := hIJ.eq_or_ssubset
  · simp at hnt

  refine by_contra fun _ ↦ hXU <| U.mem_of_ssubset_indep_of_forall_diff hJ.indep hssu fun x hx ↦ ?_
  obtain ⟨y, hy, hyx⟩ := hnt.exists_ne x
  have hyE : y ∈ M.E := hJ.indep.subset_ground hy.1
  have hyX : y ∉ M.cl X := by
    rw [← hI.cl_eq_cl, hI.indep.not_mem_cl_iff_of_not_mem hy.2 hyE]
    exact hJ.indep.subset (insert_subset hy.1 hIJ)
  have hyY : y ∈ Y := Or.elim (hJ.subset hy.1) (False.elim ∘ (not_mem_of_mem_diff_cl ⟨hyE, hyX⟩)) id

  specialize hmax y ⟨hyY, hyX⟩
  rw [← cl_insert_cl_eq_cl_insert, ← hI.cl_eq_cl, cl_insert_cl_eq_cl_insert] at hmax
  refine U.cl_superset_mem' hmax ?_
  simp [insert_subset_iff, subset_diff, hIJ, hy.1, hyx.symm, hx.2]

section restrict

/-- A `ModularCut` in `M` gives a `ModularCut` in `M ↾ R` for any `R ⊆ M.E`. -/
def ModularCut.restrict (U : M.ModularCut) {R : Set α} (hR : R ⊆ M.E) : (M ↾ R).ModularCut where
  carrier := {F | (M ↾ R).Flat F ∧ M.cl F ∈ U}
  forall_flat F h := h.1
  forall_superset F F' h hF' hFF' := ⟨hF', (U.cl_superset_mem' h.2 hFF')⟩
  forall_inter Xs hXs hne hmod := by
    refine ⟨Flat.sInter hne (fun F hF ↦ (hXs hF).1), ?_⟩
    replace hmod := hmod.ofRestrict hR
    have _ := hne.coe_sort
    rw [sInter_eq_iInter, ← hmod.iInter_cl_eq_cl_iInter]
    exact U.iInter_mem _ (fun i ↦ (hXs i.2).2) hmod.cls_modularFamily

/-- a `ModularCut` in `M` gives a `ModularCut` in `M ＼ D` for any `D`. -/
def ModularCut.delete (U : M.ModularCut) (D : Set α) : (M ＼ D).ModularCut :=
  U.restrict (diff_subset M.E D)

lemma ModularCut.mem_delete_elem_iff :
    F ∈ U.delete {e} ↔ (e ∉ F) ∧ (F ∈ U ∨ (insert e F ∈ U ∧ e ∈ M.cl F)) := by
  rw [ModularCut.delete, ModularCut.restrict, ModularCut.mem_mk_iff, mem_setOf_eq,
    ← delete_eq_restrict, ← deleteElem, flat_deleteElem_iff]
  constructor
  rintro ⟨⟨heF, (hF | hF)⟩, hFU⟩
  · rw [hF.cl] at hFU
    exact ⟨heF, .inl hFU⟩
  · rw [← hF.cl]
    obtain (heF' | heF') := em (e ∈ M.cl F)
    · rw [← insert_eq_of_mem heF'] at hFU
      replace hFU := U.cl_mem_of_mem hFU
      rw [cl_insert_cl_eq_cl_insert] at hFU
      exact ⟨heF, .inr ⟨hFU, heF'⟩⟩
    have hF' : M.Flat F := by
      have hFE := ((subset_insert _ _).trans hF.subset_ground)
      rw [flat_iff_subset_cl_self]
      refine (subset_diff_singleton (M.cl_subset_cl (subset_insert e F)) heF').trans ?_
      simp [hF.cl]
    rw [hF'.cl] at hFU
    exact ⟨heF, .inl hFU⟩
  rintro ⟨heF, (hFU | hFU)⟩
  · simpa [(U.flat_of_mem hFU), heF, (U.flat_of_mem hFU).cl]
  have hfl := U.flat_of_mem hFU.1
  rw [← hfl.cl, ← cl_insert_cl_eq_cl_insert, insert_eq_of_mem hFU.2, cl_cl] at hFU
  exact ⟨⟨heF, .inr hfl⟩, hFU.1⟩

/-- Given an element `e` of a matroid `M`, the modular cut of `M ＼ e` corresponding to the
extension `M` of `M ＼ e`. Intended to apply when `e ∈ M.E`. -/
@[simps] def ModularCut.ofDeleteElem (M : Matroid α) (e : α) : (M ＼ e).ModularCut where
  carrier := {F | (M ＼ e).Flat F ∧ e ∈ M.cl F}
  forall_flat _ h := h.1
  forall_superset := by
    simp_rw [deleteElem, flat_delete_iff]
    rintro _ _ ⟨⟨F, -, rfl⟩, he⟩ ⟨F', hF', rfl⟩ hFF'
    exact ⟨⟨F',hF', rfl⟩, M.cl_subset_cl hFF' he⟩
  forall_inter := by
    refine fun Fs hFs hFne hmod ↦ ⟨Flat.sInter hFne fun F hF ↦ (hFs hF).1, ?_⟩
    have := hFne.coe_sort
    rw [deleteElem, delete_eq_restrict] at hmod
    rw [sInter_eq_iInter, ← (hmod.ofRestrict diff_subset).iInter_cl_eq_cl_iInter, mem_iInter]
    exact fun ⟨F, hF⟩ ↦ (hFs hF).2

lemma mem_ofDeleteElem_iff : F ∈ ModularCut.ofDeleteElem M e ↔ e ∉ F ∧ M.cl F = insert e F := by
  change _ ∧ _ ↔ _
  rw [flat_deleteElem_iff, and_assoc, and_congr_right_iff]
  refine fun he ↦ ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨(hF | hF), heF⟩
    · rw [hF.cl] at heF; contradiction
    rw [← hF.cl, ← cl_insert_cl_eq_cl_insert, insert_eq_of_mem heF, cl_cl]
  rw [h, and_iff_left (.inl rfl), ← h]
  exact .inr (M.cl_flat F)

@[simp] lemma mem_ofDeleteElem_iff' :
    F ∈ ModularCut.ofDeleteElem M e ↔ e ∈ M.cl F \ F ∧ M.Flat (insert e F) := by
  simp only [deleteElem, mem_ofDeleteElem_iff, mem_diff]
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨h.1.2, ?_⟩⟩
  · rw [← h.2, and_iff_left <| M.cl_flat F, and_iff_left h.1, h.2]
    exact mem_insert _ _
  rw [← h.2.cl, ← cl_insert_cl_eq_cl_insert, insert_eq_of_mem h.1.1, cl_cl]

end restrict

section finite

/-- For a finite matroid, the intersection condition can be replaced with a condition about
modular pairs rather than families. -/
@[simps] def ModularCut.ofForallModularPairInter (M : Matroid α) [M.Finite] (U : Set (Set α))
    (h_flat : ∀ F ∈ U, M.Flat F)
    (h_superset : ∀ ⦃F F'⦄, F ∈ U → M.Flat F' → F ⊆ F' → F' ∈ U)
    (h_pair : ∀ ⦃F F'⦄, F ∈ U → F' ∈ U → M.ModularPair F F' → F ∩ F' ∈ U) :
    M.ModularCut where
  carrier := U
  forall_flat := h_flat
  forall_superset := h_superset
  forall_inter := by
    suffices h : ∀ (S : Finset (Set α)),
        S.Nonempty → ↑S ⊆ U → M.ModularFamily (fun (F : S) ↦ F) → ⋂₀ S ∈ U by
      intro Fs hFU hne hmod
      have hFs : Fs.Finite := M.finite_setOf_flat.subset (fun F hF ↦ h_flat F (hFU hF))
      obtain ⟨S, rfl⟩ := hFs.exists_finset_coe
      exact h S (by simpa using hne) (by simpa) hmod
    apply Finset.Nonempty.cons_induction
    · suffices ∀ a ∈ U, _ → a ∈ U by simpa
      exact fun _ h _ ↦ h
    simp only [Finset.coe_cons, insert_subset_iff, sInter_insert, and_imp]
    intro F S hFS hne IH hFU hSU hmod

    set incl : S → S.cons F hFS := fun X ↦ ⟨X, by simp⟩
    refine h_pair hFU (IH hSU (hmod.comp incl)) ?_
    have : Nontrivial (S.cons F hFS) := by
      obtain ⟨F', hF'⟩ := hne
      refine ⟨⟨F, by simp⟩, ⟨F', by simp [hF']⟩, ?_⟩
      simp only [ne_eq, Subtype.mk.injEq]
      rintro rfl; contradiction
    convert hmod.modularPair_singleton_compl_biInter ⟨F, by simp⟩
    simp only [mem_compl_iff, mem_singleton_iff, iInter_subtype, sInter_eq_iInter]
    ext x;
    simp only [Finset.mem_coe, mem_iInter, Finset.mem_cons, Subtype.mk.injEq,
      iInter_iInter_eq_or_left, not_true_eq_false, iInter_of_empty, univ_inter]
    exact ⟨fun h i his _ ↦ h i his, fun h i his ↦ h i his (by rintro rfl; contradiction)⟩

end finite

section extensions

/-- `U.ExtIndep e I` means that `I` is independent in the matroid obtained from `M`
by adding an element `e` using `U`, so either `I` is independent not containing `e`,
or `I = insert e J` for some `M`-independent set `J` whose closure isn't in `U`. -/
def ModularCut.ExtIndep (U : M.ModularCut) (e : α) (I : Set α) : Prop :=
  (M.Indep I ∧ e ∉ I) ∨ (M.Indep (I \ {e}) ∧ M.cl (I \ {e}) ∉ U ∧ e ∈ I)

lemma ModularCut.extIndep_iff_of_not_mem (heI : e ∉ I) : U.ExtIndep e I ↔ M.Indep I := by
  simp [ExtIndep, heI]

lemma Indep.extIndep (hI : M.Indep I) (he : e ∉ M.E) : U.ExtIndep e I :=
  .inl ⟨hI, not_mem_subset hI.subset_ground he⟩

lemma ModularCut.extIndep_iff_of_mem (heI : e ∈ I) :
    U.ExtIndep e I ↔ M.Indep (I \ {e}) ∧ M.cl (I \ {e}) ∉ U := by
  simp [ExtIndep, heI]

lemma ModularCut.ExtIndep.diff_singleton_indep {U : M.ModularCut} (h : U.ExtIndep e I) :
    M.Indep (I \ {e}) := by
  obtain (h | h) := h; exact h.1.diff _; exact h.1

lemma ModularCut.ExtIndep.subset (h : U.ExtIndep e I) (hJI : J ⊆ I) : U.ExtIndep e J := by
  obtain (heJ | heJ) := em (e ∈ J)
  · rw [extIndep_iff_of_mem (hJI heJ)] at h
    rw [extIndep_iff_of_mem heJ, and_iff_right (h.1.subset (diff_subset_diff_left hJI))]
    exact fun hJU ↦ h.2 <| U.cl_superset_mem' hJU <| diff_subset_diff_left hJI
  rw [extIndep_iff_of_not_mem heJ]
  exact h.diff_singleton_indep.subset (subset_diff_singleton hJI heJ)

lemma ModularCut.ExtIndep.subset_insert_ground (h : U.ExtIndep e I) : I ⊆ insert e M.E :=
  diff_singleton_subset_iff.1 h.diff_singleton_indep.subset_ground

/-- This lemma gives the conditions under which `I` is a maximal `ExtIndep` subset of `X`;
it is essentially characterizing when `(M.extendBy e U).Basis I X` before `M.extendBy e U`
has been defined.
We need the lemma here because it is invoked several times when defining `M.extendBy e U`,
but it should not be used elsewhere; good API versions should be stated in terms of
`(M.extendBy e U).Basis`, and have less of a dense mess of logic on the RHS.
 -/
private lemma ModularCut.maximal_extIndep_iff (hX : X ⊆ insert e M.E) (hI : U.ExtIndep e I)
    (hIX : I ⊆ X) : I ∈ maximals (· ⊆ ·) {J | U.ExtIndep e J ∧ J ⊆ X} ↔
        (M.cl (I \ {e}) = M.cl (X \ {e}) ∧ ((e ∈ I ↔ M.cl (X \ {e}) ∈ U) → e ∉ X))
      ∨ ((M.cl (I \ {e}) ⋖[M] M.cl (X \ {e})) ∧ e ∈ I ∧ M.cl (X \ {e}) ∈ U) := by

  have hss : I \ {e} ⊆ X \ {e} := diff_subset_diff_left hIX
  have hX' : X \ {e} ⊆ M.E := by simpa

  rw [mem_maximals_iff_forall_insert (fun _ _ ht hst ↦ ⟨ht.1.subset hst, hst.trans ht.2⟩)]

  simp only [hI, hIX, and_self, insert_subset_iff, and_true, not_and, true_and, imp_not_comm]

  refine ⟨fun h ↦ ?_, fun h x hxI hi hind ↦ ?_⟩
  · simp only [ExtIndep, insert_subset_iff, hIX, and_true, imp_not_comm, not_or, not_and,
      not_not] at h

    obtain (heI | heI) := em (e ∈ I)
    · rw [extIndep_iff_of_mem heI] at hI
      obtain (hcl | hcl) := em (M.cl (X \ {e}) ∈ U)
      · simp only [heI, hcl, not_true_eq_false, imp_false, and_self, and_true]
        refine .inr <| U.covBy_of_maximal_cl (M.cl_subset_cl hss) hcl hI.2 fun x ⟨hx, hxcl⟩ ↦ ?_
        specialize h x
        have hxI : x ∉ I := by simpa [hx.2] using not_mem_of_mem_diff_cl ⟨hX' hx, hxcl⟩
        rw [← insert_diff_singleton_comm hx.2, hI.1.insert_indep_iff] at h
        exact (h hxI hx.1).2 (.inl ⟨hX' hx, hxcl⟩) (.inr heI)

      simp only [heI, hcl, iff_false, not_true_eq_false, not_false_eq_true, implies_true, and_true,
        and_false, or_false]
      refine (M.cl_subset_cl hss).antisymm (M.cl_subset_cl_of_subset_cl fun x hx ↦
        by_contra fun hxcl ↦ hcl ?_)
      have hxI : x ∉ I := by simpa [hx.2] using not_mem_of_mem_diff_cl ⟨(hX' hx), hxcl⟩

      replace h := show M.cl (insert x (I \ {e})) ∈ U by
        simpa [hxI, hx.1, heI, ← insert_diff_singleton_comm hx.2, hI.1.insert_indep_iff,
          hX' hx, hxcl] using h x

      exact U.cl_superset_mem' h (insert_subset hx hss)
    simp only [mem_insert_iff, heI, or_false] at h
    have hXI : M.cl (X \ {e}) = M.cl (I \ {e}) := by
      refine (M.cl_subset_cl hss).antisymm' (M.cl_subset_cl_of_subset_cl fun x hx ↦ ?_)
      rw [hI.diff_singleton_indep.mem_cl_iff', and_iff_right (hX' hx), mem_diff, and_iff_left hx.2,
        diff_singleton_eq_self heI]
      exact fun h' ↦ by_contra fun hxI ↦ by simp [(h x hxI hx.1).1 h'] at hx

    simp only [heI, not_false_eq_true, diff_singleton_eq_self, hXI, false_iff, not_imp_not,
      true_and, false_and, and_false, or_false]
    intro heX
    rw [extIndep_iff_of_not_mem heI] at hI
    simpa [heI, hI] using (h e heI heX).2

  obtain (heI | heI) := em (e ∈ I)
  · have hxe : x ≠ e := by rintro rfl; contradiction
    rw [extIndep_iff_of_mem heI] at hI
    rw [extIndep_iff_of_mem (.inr heI), ← insert_diff_singleton_comm hxe,
      hI.1.insert_indep_iff_of_not_mem (by simp [hxI, hxe])] at hind
    simp only [hIX heI, heI, true_iff, true_implies, true_and] at h
    obtain (⟨h_eq, -⟩ | ⟨hcv, h⟩) := h
    · exact not_mem_of_mem_diff_cl (h_eq ▸ hind.1) <| by simp [hi, hxe]
    rw [hcv.eq_cl_insert_of_mem_diff ⟨M.mem_cl_of_mem ⟨hi, hxe⟩, hind.1.2⟩,
      cl_insert_cl_eq_cl_insert] at h
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
  refine not_mem_of_mem_diff_cl hind ⟨hi, hne.symm⟩

/-- This lemma is true without the coloop hypothesis, but it is easier to prove this first and
then reduce the stronger version to this one; see `ModularCut.extIndep_aug`. -/
private lemma ModularCut.extIndep_aug_of_not_coloop (U : ModularCut M) (he : ¬ M.Coloop e)
    (hI : U.ExtIndep e I) (hInmax : I ∉ maximals (· ⊆ ·) {I | U.ExtIndep e I})
    (hBmax : B ∈ maximals (· ⊆ ·) {I | U.ExtIndep e I}) :
    ∃ x ∈ B \ I, U.ExtIndep e (insert x I) := by
  rw [coloop_iff_diff_cl, not_not] at he
  by_contra! hcon

  have hB : U.ExtIndep e B := hBmax.1
  have hIeE := hI.diff_singleton_indep.subset_ground
  have hBeE := hB.diff_singleton_indep.subset_ground
  have hss : B \ {e} ⊆ (I ∪ B) \ {e} :=
    diff_subset_diff_left <| subset_union_right I B

  have hIBe : I ∪ B ⊆ insert e M.E :=
    union_subset hI.subset_insert_ground hB.subset_insert_ground
  have hIBe' : (I ∪ B) \ {e} ⊆ M.E := by rwa [diff_singleton_subset_iff]

  have hImax : I ∈ maximals (· ⊆ ·) {J | U.ExtIndep e J ∧ J ⊆ I ∪ B} := by
    rw [mem_maximals_iff_forall_insert (fun _ _ ht hst ↦ ⟨ht.1.subset hst, hst.trans ht.2⟩),
      and_iff_right hI, and_iff_right subset_union_left]
    intro x hxI h'
    rw [insert_subset_iff, mem_union, or_iff_right hxI] at h'
    exact hcon x ⟨h'.2.1, hxI⟩ h'.1

  have hrw : {J | U.ExtIndep e J} = {J | U.ExtIndep e J ∧ J ⊆ insert e M.E} := by
    simp only [ext_iff, mem_setOf_eq, iff_self_and]
    exact  fun _ ↦ ExtIndep.subset_insert_ground

  rw [hrw, U.maximal_extIndep_iff Subset.rfl hI hI.subset_insert_ground] at hInmax
  rw [hrw, U.maximal_extIndep_iff Subset.rfl hB hB.subset_insert_ground] at hBmax
  rw [U.maximal_extIndep_iff hIBe hI subset_union_left] at hImax

  obtain (rfl | hU) := U.eq_bot_or_ground_mem
  · replace hBmax := show M.Spanning (B \ {e}) ∧ e ∈ B by
      simpa [← spanning_iff_cl hBeE, he] using hBmax
    replace hInmax := show M.Spanning (I \ {e}) → e ∉ I by
      simpa [← spanning_iff_cl hIeE, he] using hInmax
    replace hImax := show M.Spanning (I \ {e}) ∧ e ∈ I by
      simpa [hBmax.2, he, hBmax.1.cl_superset_eq hss, ← spanning_iff_cl hIeE] using hImax
    exact hInmax hImax.1 hImax.2

  simp only [mem_singleton_iff, insert_diff_of_mem, he, not_false_eq_true, diff_singleton_eq_self,
    cl_ground, hU, iff_true, mem_insert_iff, or_false, not_true_eq_false, and_false, imp_false,
    and_true, not_or, not_and, not_not, mem_union, and_self_left,
    ← spanning_iff_cl hBeE, ← spanning_iff_cl hIeE, ← hyperplane_iff_covBy] at hBmax hInmax

  obtain (hsp | hsp) := em <| M.Spanning ((I ∪ B) \ {e})
  · obtain (heI | heI) := em (e ∈ I)
    · replace hImax := show M.Hyperplane (M.cl (I \ {e})) by
        simpa [hsp.cl_eq, heI, hU, ← hyperplane_iff_covBy] using hImax
      exact hInmax.2 hImax heI
    replace hInmax := show ¬ M.Spanning (I \ {e}) by simpa [heI, hU] using hInmax
    replace hImax := show M.cl (I \ {e}) = M.E by simpa [hsp.cl_eq, heI, he, hU] using hImax
    rw [spanning_iff_cl hIeE] at hInmax; contradiction

  obtain (⟨hBsp, -⟩ | ⟨hBhp, heB⟩) := hBmax
  · exact hsp <| hBsp.superset hss hIBe'

  have hclcl : M.cl (B \ {e}) = M.cl ((I ∪ B) \ {e}) := by
    refine by_contra fun hne ↦ hsp <| ?_
    rw [← cl_spanning_iff hIBe']
    have hssu := (M.cl_subset_cl hss).ssubset_of_ne hne
    exact hBhp.spanning_of_ssuperset hssu

  rw [extIndep_iff_of_mem heB] at hB
  replace hImax := show M.cl (I \ {e}) = M.cl (B \ {e}) ∧ e ∈ I by
    simpa [heB, ← hclcl, hB.2] using hImax

  replace hInmax := show ¬M.Hyperplane (M.cl (I \ {e})) by simpa [hImax.2] using hInmax
  exact hInmax <| (hImax.1.symm ▸ hBhp)

private lemma ModularCut.extIndep_aug (U : ModularCut M) (hI : U.ExtIndep e I)
    (hInmax : I ∉ maximals (· ⊆ ·) {I | U.ExtIndep e I})
    (hBmax : B ∈ maximals (· ⊆ ·) {I | U.ExtIndep e I}) :
    ∃ x ∈ B \ I, U.ExtIndep e (insert x I) := by
  obtain (he | he) := em' (M.Coloop e)
  · exact U.extIndep_aug_of_not_coloop he hI hInmax hBmax
  have hrw : (U.delete {e}).ExtIndep e = U.ExtIndep e := by
    ext; simp [ExtIndep, he.mem_cl_iff_mem, ModularCut.mem_delete_elem_iff]
  simp_rw [← hrw] at hInmax hBmax hI ⊢
  exact (U.delete {e}).extIndep_aug_of_not_coloop (fun h ↦ h.mem_ground.2 rfl) hI hInmax hBmax

private lemma ModularCut.existsMaximalSubsetProperty (U : M.ModularCut)
    (hXE : X ⊆ insert e M.E) : ExistsMaximalSubsetProperty (U.ExtIndep e) X := by
  intro I hI hIX
  suffices hJ : ∃ J, I ⊆ J ∧ J ∈ maximals (· ⊆ ·) {K | U.ExtIndep e K ∧ K ⊆ X} by
    obtain ⟨J, hIJ, hJ⟩ := hJ
    refine ⟨J, ?_⟩
    convert maximals_inter_subset (t := {K | I ⊆ K}) ⟨hJ, hIJ⟩ using 2
    ext
    simp only [mem_setOf_eq, mem_inter_iff]
    tauto
  obtain ⟨J, hJ, hIJ⟩ :=
    hI.diff_singleton_indep.subset_basis_of_subset (diff_subset_diff_left hIX)

  obtain ⟨hJX, heJ⟩ : J ⊆ X ∧ e ∉ J := by simpa [subset_diff] using hJ.subset
  have hJi : U.ExtIndep e J := .inl ⟨hJ.indep, heJ⟩
  by_contra! hcon

  have hconJe : e ∈ X → M.cl (X \ {e}) ∈ U := by
    refine fun heX ↦ by_contra fun hcl ↦ ?_
    have hind : U.ExtIndep e (insert e J) := by
      rw [extIndep_iff_of_mem (.inl rfl)]
      simpa [heJ, hJ.indep, hJ.cl_eq_cl]
    specialize hcon (insert e J) (by simpa using hIJ)
    rw [maximal_extIndep_iff  hXE hind (insert_subset heX hJX)] at hcon
    simp [heJ, hJ.cl_eq_cl, hcl] at hcon

  have heI : e ∈ I := by
    refine by_contra fun heI ↦ ?_
    rw [diff_singleton_eq_self heI] at hIJ
    have h' : M.cl (X \ {e}) ∉ U ∧ e ∈ X := by
      simpa [maximal_extIndep_iff hXE hJi hJX, heJ, hJ.cl_eq_cl] using hcon J hIJ
    exact h'.1 <| hconJe h'.2

  rw [extIndep_iff_of_mem heI] at hI
  specialize hconJe (hIX heI)

  obtain (rfl | hssu) := hIJ.eq_or_ssubset
  · rw [hJ.cl_eq_cl] at hI; exact hI.2 hconJe

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

  have hconJ' : (M.cl (J \ {x}) = M.cl J → e ∈ X) ∧ ¬M.CovBy (M.cl (J \ {x})) (M.cl J) := by
    rw [maximal_extIndep_iff hXE hind hJ'X, iff_true_intro hconJe] at hcon
    simpa [hJ'e, ← hJ.cl_eq_cl, show e ∈ J' from .inl rfl] using hcon

  exact hconJ'.2 <| hJ.indep.cl_diff_covBy hxJI.1

/-- Extend a matroid `M` by an element `e` using a modular cut `U`.
(Intended for use when `e ∉ M.E`; if `e` already belongs to `M`,
then this gives the extension of `M ＼ e` by `e` using `U`.) -/
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
  refine Eq.symm <| eq_of_indep_iff_indep_forall (by simp [he]) fun I hI ↦ ?_
  obtain (heI | heI) := em' (e ∈ I); simp [extIndep_iff_of_not_mem heI, heI]
  obtain ⟨I, rfl, heI'⟩ : ∃ J, I = insert e J ∧ e ∉ J := ⟨I \ {e}, by simp [heI], by simp⟩
  suffices
    M.Indep (insert e I) ↔ M.Indep I ∧ (e ∈ M.cl (M.cl I \ {e}) → ¬M.Flat (insert e (M.cl I))) by
    simpa [extIndep_iff_of_mem heI, heI']

  refine ⟨fun h ↦ ⟨h.subset (subset_insert _ _), fun he _ ↦ ?_⟩, fun ⟨hIi, h⟩ ↦ ?_⟩
  · suffices e ∈ M.cl (M.cl I) from h.not_mem_cl_diff_of_mem (.inl rfl) <| by simpa [heI']
    exact (M.cl_subset_cl diff_subset) he
  rw [hIi.insert_indep_iff_of_not_mem heI', mem_diff, and_iff_right (hI (.inl rfl))]
  refine fun heCl ↦ ?_
  simp only [heCl, insert_eq_of_mem, cl_flat, not_true_eq_false, imp_false] at h
  exact h <| (M.cl_subset_cl <| subset_diff_singleton (M.subset_cl I hIi.subset_ground) heI') heCl

lemma ModularCut.extendBy_deleteElem (U : M.ModularCut) (he : e ∉ M.E) :
    (M.extendBy e U) ＼ e = M := by
  refine eq_of_indep_iff_indep_forall (by simpa) fun I hI ↦ ?_
  obtain ⟨-, heI⟩ := show I ⊆ M.E ∧ e ∉ I by simpa [subset_diff] using hI
  simp [deleteElem, extIndep_iff_of_not_mem heI, heI]

lemma extendBy_injective (M : Matroid α) (he : e ∉ M.E) : Injective (M.extendBy e) := by
  refine fun U U' h_eq ↦ SetLike.coe_set_eq.1 (Set.ext fun F ↦ ?_)
  obtain (hF | hF) := em' (M.Flat F)
  · exact iff_of_false (hF ∘ U.flat_of_mem) (hF ∘ U'.flat_of_mem)
  obtain ⟨I, hI⟩ := M.exists_basis F
  have heI : e ∉ I := not_mem_subset hI.indep.subset_ground he
  apply_fun (fun M ↦ M.Indep (insert e I)) at h_eq
  simpa [extendBy_Indep, ModularCut.extIndep_iff_of_mem (mem_insert e I), heI, hI.indep,
    not_iff_not, ← hF.eq_cl_of_basis hI] using h_eq

/-- Single-element extensions are equivalent to modular cuts. -/
def extensionEquivModularCut (M : Matroid α) (he : e ∉ M.E) :
    {N : Matroid α // (e ∈ N.E ∧ N ＼ e = M)} ≃ M.ModularCut where
  toFun N := (ModularCut.ofDeleteElem N e).congr N.2.2
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

end extensions

section projection

/-- Extend `M` using the modular cut `U`, and contract the new element. -/
def projectBy (M : Matroid α) (U : M.ModularCut) : Matroid α := Matroid.ofExistsMatroid
  (E := M.E)
  (Indep := fun I ↦ M.Indep I ∧ (U ≠ ⊤ → M.cl I ∉ U))
  (hM := by
    have hinj := Option.some_injective α
    have hf : InjOn _ M.E := hinj.injOn M.E
    set M' := (M.map _ hf).extendBy none (U.map _ hf) with hM'
    use (M' ／ (none : Option α)).comap (Option.some)
    suffices ∀ (I : Set α),
      ((M.map some hf).extendBy none (U.map some hf) ／ (none : Option α)).Indep (some '' I) ↔
      M.Indep I ∧ (U ≠ ⊤ → M.cl I ∉ U) by
      simpa [preimage_image_eq _ hinj, hinj.injOn _, hM']
    intro I
    obtain (rfl | hU) := eq_or_ne U ⊤
    · rw [contract_elem, contract_eq_delete_of_subset_loops]
      · simp [ModularCut.extIndep_iff_of_not_mem, image_eq_image hinj]
      rw [singleton_subset_iff, ← loop_iff_mem_cl_empty, ← singleton_dep, dep_iff]
      simp [ModularCut.extIndep_iff_of_mem, map_cl_eq, ModularCut.map, image_eq_image hinj]
    rw [contract_elem, Indep.contract_indep_iff]
    · simp [ModularCut.extIndep_iff_of_mem, image_eq_image hinj, map_cl_eq,
        preimage_image_eq _ hinj, ModularCut.map, hU]
    suffices M.cl ∅ ∉ U by
      simpa [ModularCut.extIndep_iff_of_mem, (eq_comm (a := ∅)), map_cl_eq, ModularCut.map,
        image_eq_image hinj]
    rwa [Ne, ModularCut.eq_top_iff] at hU )

@[simp] lemma projectBy_ground_eq (U : M.ModularCut) : (M.projectBy U).E = M.E := rfl

@[simp] lemma projectBy_indep_iff (U : M.ModularCut) :
    (M.projectBy U).Indep I ↔ M.Indep I ∧ (U ≠ ⊤ → M.cl I ∉ U) := Iff.rfl

lemma projectBy_indep_iff_of_ne_top {I : Set α} (hU : U ≠ ⊤) :
    (M.projectBy U).Indep I ↔ M.Indep I ∧ M.cl I ∉ U := by
  simp [hU]

lemma projectBy_top : M.projectBy ⊤ = M := by
  simp [eq_iff_indep_iff_indep_forall]

/-- The matroid on `M.E` whose independent sets are the independent nonbases of `M`. -/
def truncate (M : Matroid α) := M.projectBy (ModularCut.principal M M.E)

@[simp] lemma truncate_ground_eq : M.truncate.E = M.E := rfl

@[simp] lemma truncate_indep_iff [M.RkPos] : M.truncate.Indep I ↔ M.Indep I ∧ ¬ M.Base I := by
  suffices M.Indep I → (¬M.E ⊆ M.cl I ↔ ¬M.Base I) by simpa [truncate, M.principal_ground_ne_top]
  refine fun hI ↦ ⟨fun hcl hB ↦ hcl ?_, fun h hcl ↦ h (hI.base_of_spanning ?_)⟩
  · simp [hB.cl_eq, Subset.rfl]
  rwa [spanning_iff_ground_subset_cl]

end projection

section LinearClass

/-
TODO. I think linear classes only work for finite matroids; if `B` and `B'` are disjoint infinite bases of `M`, the class of hyperplanes `H` with `B\H` finite ought not to be a linear class, but I don't know what reasonable definition would forbid that.
-/

-- def LinearClass (M : Matroid α) where
--   carrier : Set (Set α)
--   forall_hyperplane : ∀ H ∈ carrier, M.Hyperplane H
--   forall_hyper' : ∀ H₁ H₂ ∈ carrier,

end LinearClass
