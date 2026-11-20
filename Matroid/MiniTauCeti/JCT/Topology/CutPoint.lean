module

public import Matroid.MiniTauCeti.JCT.Topology.ConnectedComponent
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Matroid.MiniTauCeti.JCT.Topology.Order

@[expose] public section

/-!
# Cut-point separation and rooted orders

`Separates T D a b` retains both endpoints in `T \ D` and distinguishes them by a
relatively clopen set. `separationOrder` uses this strict separation to order an
arbitrary connected space from a root. If every other point separates two fixed
endpoints, `separatorLinearOrder` is linear and has those endpoints as its bounds.

The connectedness argument does not require a separation axiom: adjoining a deleted
point to either clopen side gives a connected set (`isConnected_insert`). This gives
the nesting of cuts, the order laws, and the component-membership formula.
T₁ is used only for openness of order rays; compactness then identifies
the resulting order topology with the original topology. The unrestricted rooted
relation is a preorder; preconnectedness supplies antisymmetry.
-/

open Set Topology


namespace CutPoint

variable {K : Type*} [TopologicalSpace K] {T D U V : Set K} {a b x y z : K}

/-- A clopen separation of `T \ D` with both endpoints retained. -/
def Separates (T D : Set K) (a b : K) : Prop :=
  a ∈ T \ D ∧ b ∈ T \ D ∧ ∃ U : Set K,
    IsClopen ((Subtype.val : ↥(T \ D) → K) ⁻¹' U) ∧ a ∈ U ∧ b ∉ U

/-- Ward's separation relation rooted at `a`. -/
def separationLE (a x y : K) : Prop :=
  x = a ∨ x = y ∨ Separates univ {x} a y

lemma Separates.preimage {X : Type*} [TopologicalSpace X] {f : X → K} {a b : X}
    (h : Separates T D (f a) (f b)) (hf : ContinuousOn f (f ⁻¹' (T \ D))) :
    Separates (f ⁻¹' T) (f ⁻¹' D) a b := by
  obtain ⟨ha, hb, U, hU, haU, hbU⟩ := h
  let g : ↥((f ⁻¹' T) \ (f ⁻¹' D)) → ↥(T \ D) := fun z ↦ ⟨f z, z.property⟩
  have hg : Continuous g := (continuousOn_iff_continuous_domRestrict.mp hf).subtype_mk _
  exact ⟨ha, hb, f ⁻¹' U, hU.preimage hg, haU, hbU⟩

lemma Separates.symm (h : Separates T D a b) : Separates T D b a := by
  obtain ⟨ha, hb, U, hU, haU, hbU⟩ := h
  exact ⟨hb, ha, Uᶜ, hU.compl, hbU, fun h ↦ h haU⟩

lemma Separates.ne (h : Separates T D a b) : a ≠ b := by
  obtain ⟨_, _, U, _, ha, hb⟩ := h
  exact fun hab ↦ hb (hab ▸ ha)

lemma Separates.left_notMem (h : Separates T D a b) : a ∉ D := h.1.2
lemma Separates.right_notMem (h : Separates T D a b) : b ∉ D := h.2.1.2

/-- A connected subset containing the separated endpoints must meet the deleted set. -/
lemma Separates.not_subset (h : Separates T D a b) {S : Set K}
    (hS : IsPreconnected S) (ha : a ∈ S) (hb : b ∈ S) : ¬ S ⊆ T \ D := by
  intro hsub
  obtain ⟨_, _, U, hU, haU, hbU⟩ := h
  have hpre : IsPreconnected ((Subtype.val : ↥(T \ D) → K) ⁻¹' S) := by
    apply IsInducing.subtypeVal.isPreconnected_image.mp
    simpa [Subtype.image_preimage_coe, inter_eq_right.mpr hsub] using hS
  exact hbU (hpre.subset_isClopen hU ⟨⟨a, hsub ha⟩, ha, haU⟩
    (show (⟨b, hsub hb⟩ : ↥(T \ D)) ∈ Subtype.val ⁻¹' S from hb))

/-- Separation implies distinct components, with no finiteness assumption. -/
lemma Separates.connectedComponentIn_ne (h : Separates T D a b) :
    connectedComponentIn (T \ D) a ≠ connectedComponentIn (T \ D) b := by
  intro he
  exact h.not_subset isPreconnected_connectedComponentIn (mem_connectedComponentIn h.1)
    (he.symm ▸ mem_connectedComponentIn h.2.1) (connectedComponentIn_subset _ _)

lemma separates_iff_connectedComponentIn_ne
    [TotallySeparatedSpace (ConnectedComponents ↥(T \ D))] :
    Separates T D a b ↔ a ∈ T \ D ∧ b ∈ T \ D ∧
      connectedComponentIn (T \ D) a ≠ connectedComponentIn (T \ D) b := by
  constructor
  · intro h
    exact ⟨h.1, h.2.1, h.connectedComponentIn_ne⟩
  · rintro ⟨ha, hb, hne⟩
    have hne' : ConnectedComponents.mk (⟨a, ha⟩ : ↥(T \ D)) ≠
        ConnectedComponents.mk (⟨b, hb⟩ : ↥(T \ D)) := by
      intro he
      apply hne
      rw [connectedComponentIn_eq_image ha, connectedComponentIn_eq_image hb]
      exact congrArg (Subtype.val '' ·) (ConnectedComponents.coe_eq_coe.mp he)
    obtain ⟨V, hV, haV, hbV⟩ := exists_isClopen_of_totally_separated hne'
    let W := ConnectedComponents.mk ⁻¹' V
    refine ⟨ha, hb, Subtype.val '' W, ?_, ⟨⟨a, ha⟩, haV, rfl⟩, ?_⟩
    · rw [preimage_image_eq _ Subtype.val_injective]
      exact hV.preimage ConnectedComponents.continuous_coe
    · rintro ⟨z, hz, he⟩
      have hz' : z = ⟨b, hb⟩ := Subtype.ext he
      exact hbV (hz' ▸ hz)

/-- Adjoining the deleted point to a clopen side gives a connected set.
No separation axiom on the ambient space is required. -/
lemma isConnected_insert [PreconnectedSpace K]
    (hU : IsClopen ((Subtype.val : ↥({x}ᶜ : Set K) → K) ⁻¹' U)) :
    IsConnected (insert x U) := by
  have hU' : IsClopen ((Subtype.val : ↥((univ : Set K) \ {x}) → K) ⁻¹' insert x U) := by
    have heq : (Subtype.val : ↥((univ : Set K) \ {x}) → K) ⁻¹' insert x U =
        Subtype.val ⁻¹' U := by
      ext z
      exact or_iff_right z.property.2
    rw [heq]
    exact (congrArg (fun S : Set K ↦ IsClopen ((Subtype.val : ↥S → K) ⁻¹' U))
      (compl_eq_univ_sdiff {x})).mp hU
  exact ⟨⟨x, mem_insert x U⟩, isPreconnected_univ.of_isClopen_sdiff isPreconnected_singleton
    (singleton_subset_iff.mpr (mem_insert x U)) (subset_univ _) hU'⟩

lemma Separates.mem_of_isPreconnected (h : Separates univ {x} a b) {S : Set K}
    (hS : IsPreconnected S) (ha : a ∈ S) (hb : b ∈ S) : x ∈ S := by
  by_contra hx
  exact h.not_subset hS ha hb (by intro t ht; simp only [mem_sdiff, mem_univ,
    mem_singleton_iff, true_and]; exact fun he ↦ hx (he ▸ ht))

private lemma Separates.exists_side (h : Separates univ {x} a b) :
    ∃ U : Set K, x ∉ U ∧ a ∈ U ∧ b ∉ U ∧
      IsClopen ((Subtype.val : ↥({x}ᶜ : Set K) → K) ⁻¹' U) := by
  obtain ⟨ha, hb, U, hU, haU, hbU⟩ := h
  refine ⟨U \ {x}, fun ht ↦ ht.2 rfl, ⟨haU, ha.2⟩, fun ht ↦ hbU ht.1, ?_⟩
  have he : (Subtype.val : ↥({x}ᶜ : Set K) → K) ⁻¹' (U \ {x}) =
      (Subtype.val : ↥({x}ᶜ : Set K) → K) ⁻¹' U := by ext t; simp
  rw [he]
  exact (congrArg (fun S : Set K ↦
    IsClopen ((Subtype.val : ↥S → K) ⁻¹' U)) (compl_eq_univ_sdiff {x})).mpr hU

private lemma isConnected_compl [PreconnectedSpace K] (hxU : x ∉ U)
    (hU : IsClopen ((Subtype.val : ↥({x}ᶜ : Set K) → K) ⁻¹' U)) :
    IsConnected Uᶜ := by
  have hV : IsClopen ((Subtype.val : ↥({x}ᶜ : Set K) → K) ⁻¹' (Uᶜ \ {x})) := by
    have he : (Subtype.val : ↥({x}ᶜ : Set K) → K) ⁻¹' (Uᶜ \ {x}) =
        ((Subtype.val : ↥({x}ᶜ : Set K) → K) ⁻¹' U)ᶜ := by ext t; simp
    rw [he]
    exact hU.compl
  have he : insert x (Uᶜ \ {x}) = Uᶜ := by ext t; simp only [mem_insert_iff,
    mem_sdiff, mem_compl_iff, mem_singleton_iff]; by_cases ht : t = x <;> simp_all
  rw [← he]
  exact isConnected_insert hV

lemma Separates.antisymm [PreconnectedSpace K] (h : Separates univ {x} a y) :
    ¬ Separates univ {y} a x := by
  intro h'
  obtain ⟨U, -, haU, hyU, hU⟩ := h.exists_side
  have hy := h'.mem_of_isPreconnected (isConnected_insert hU).isPreconnected
    (mem_insert_of_mem x haU) (mem_insert x U)
  rcases hy with hyx | hyU'
  · exact h.right_notMem hyx
  · exact hyU hyU'

lemma Separates.trans_of_ne (hxy : Separates univ {x} a y)
    (hyz : Separates univ {y} a z) (hxz : x ≠ z) : Separates univ {x} a z := by
  obtain ⟨U, hxU, haU, hyU, hU⟩ := hxy.exists_side
  by_cases hzU : z ∈ U
  · obtain ⟨V, _, haV, hzV, hV⟩ := hyz.exists_side
    let A : Set ↥({x}ᶜ : Set K) := Subtype.val ⁻¹' U
    let f : ↥A → ↥({y}ᶜ : Set K) := fun t ↦
      ⟨t.val.val, fun he ↦ hyU (he ▸ t.property)⟩
    have hf : Continuous f :=
      (continuous_subtypeVal.comp continuous_subtypeVal).subtype_mk _
    have hW := hV.preimage hf
    have himage : IsClopen ((Subtype.val : ↥A → ↥({x}ᶜ : Set K)) ''
        (f ⁻¹' (Subtype.val ⁻¹' V))) :=
      ⟨hU.isClosed.isClosedMap_subtypeVal _ hW.isClosed,
        hU.isOpen.isOpenMap_subtypeVal _ hW.isOpen⟩
    have he : ((Subtype.val : ↥A → ↥({x}ᶜ : Set K)) ''
        (f ⁻¹' (Subtype.val ⁻¹' V))) = Subtype.val ⁻¹' (U ∩ V) := by
      ext t
      constructor
      · rintro ⟨s, hs, rfl⟩
        exact ⟨s.property, hs⟩
      · rintro ⟨htU, htV⟩
        exact ⟨⟨t, htU⟩, htV, rfl⟩
    refine ⟨hxy.1, ⟨mem_univ _, hxz.symm⟩, U ∩ V, ?_, ⟨haU, haV⟩,
      fun hz ↦ hzV hz.2⟩
    rw [he] at himage
    exact (congrArg (fun S : Set K ↦ IsClopen ((Subtype.val : ↥S → K) ⁻¹' (U ∩ V)))
      (compl_eq_univ_sdiff {x})).mp himage
  · refine ⟨hxy.1, ⟨mem_univ _, hxz.symm⟩, U, ?_, haU, hzU⟩
    exact (congrArg (fun S : Set K ↦ IsClopen ((Subtype.val : ↥S → K) ⁻¹' U))
      (compl_eq_univ_sdiff {x})).mp hU

/-- Without connectedness the rooted relation is still a preorder. -/
@[instance_reducible]
def separationPreorder (a : K) : Preorder K where
  le := separationLE a
  le_refl _ := Or.inr (Or.inl rfl)
  le_trans x y z hxy hyz := by
    rcases hxy with rfl | rfl | hxy
    · exact Or.inl rfl
    · exact hyz
    rcases hyz with rfl | rfl | hyz
    · exact False.elim (hxy.ne rfl)
    · exact Or.inr (Or.inr hxy)
    · by_cases hxz : x = z
      · exact Or.inr (Or.inl hxz)
      · exact Or.inr (Or.inr (hxy.trans_of_ne hyz hxz))

lemma Separates.trans [PreconnectedSpace K] (hxy : Separates univ {x} a y)
    (hyz : Separates univ {y} a z) : Separates univ {x} a z :=
  hxy.trans_of_ne hyz (fun hxz ↦ hxy.antisymm (hxz ▸ hyz))

/-- The partial order defined by separation from a fixed root. -/
@[instance_reducible]
def separationOrder [PreconnectedSpace K] (a : K) : PartialOrder K where
  __ := separationPreorder a
  le_antisymm x y hxy hyx := by
    rcases hxy with rfl | rfl | hxy
    · rcases hyx with rfl | rfl | hyx
      · rfl
      · rfl
      · exact False.elim (hyx.ne rfl)
    · rfl
    rcases hyx with rfl | rfl | hyx
    · exact False.elim (hxy.ne rfl)
    · rfl
    · exact False.elim (hxy.antisymm hyx)

private lemma separates_of_side (hxU : x ∉ U) (haU : a ∈ U) (hbU : b ∉ U)
    (hbx : b ≠ x)
    (hU : IsClopen ((Subtype.val : ↥({x}ᶜ : Set K) → K) ⁻¹' U)) :
    Separates univ {x} a b :=
  ⟨⟨mem_univ _, fun he ↦ hxU (he ▸ haU)⟩, ⟨mem_univ _, hbx⟩, U,
    (congrArg (fun S : Set K ↦ IsClopen ((Subtype.val : ↥S → K) ⁻¹' U))
      (compl_eq_univ_sdiff {x})).mp hU, haU, hbU⟩

private lemma Separates.compare [PreconnectedSpace K] (hx : Separates univ {x} a b)
    (hy : Separates univ {y} a b) (hxy : x ≠ y) :
    Separates univ {x} a y ∨ Separates univ {y} a x := by
  obtain ⟨U, hxU, haU, hbU, hU⟩ := hx.exists_side
  obtain ⟨V, hyV, haV, hbV, hV⟩ := hy.exists_side
  by_cases hyU : y ∈ U
  · right
    have hxV : x ∉ V := by
      intro hxV
      have hyb := separates_of_side hxU hyU hbU hx.right_notMem hU
      exact hyb.mem_of_isPreconnected (isConnected_compl hyV hV).isPreconnected hyV hbV hxV
    exact separates_of_side hyV haV hxV hxy hV
  · exact Or.inl (separates_of_side hxU haU hyU hxy.symm hU)

/-- The rooted order is linear when every other point separates the two endpoints. -/
@[instance_reducible]
noncomputable def separatorLinearOrder [PreconnectedSpace K] (a b : K)
    (hsep : ∀ z : K, z ≠ a → z ≠ b → Separates univ {z} a b) : LinearOrder K where
  __ := separationOrder a
  le_total x y := by
    by_cases hxa : x = a
    · exact Or.inl (Or.inl hxa)
    by_cases hya : y = a
    · exact Or.inr (Or.inl hya)
    by_cases hxy : x = y
    · exact Or.inl (Or.inr (Or.inl hxy))
    by_cases hxb : x = b
    · right
      exact Or.inr (Or.inr (hxb ▸ hsep y hya (fun he ↦ hxy (hxb.trans he.symm))))
    by_cases hyb : y = b
    · left
      exact Or.inr (Or.inr (hyb ▸ hsep x hxa hxb))
    exact ((hsep x hxa hxb).compare (hsep y hya hyb) hxy).imp
      (fun h ↦ Or.inr (Or.inr h)) (fun h ↦ Or.inr (Or.inr h))
  toDecidableLE := Classical.decRel _

theorem separatorLinearOrder_endpoints [PreconnectedSpace K] (a b : K)
    (hsep : ∀ z : K, z ≠ a → z ≠ b → Separates univ {z} a b) :
    letI := separatorLinearOrder a b hsep
    (∀ z : K, a ≤ z) ∧ (∀ z : K, z ≤ b) := by
  refine ⟨fun _ ↦ Or.inl rfl, fun z ↦ ?_⟩
  by_cases hza : z = a
  · exact Or.inl hza
  by_cases hzb : z = b
  · exact Or.inr (Or.inl hzb)
  exact Or.inr (Or.inr (hsep z hza hzb))

lemma Separates.mem_connectedComponentIn [PreconnectedSpace K]
    (h : Separates univ {x} a y) :
    x ∈ connectedComponentIn ((univ : Set K) \ {y}) a := by
  obtain ⟨U, -, haU, hyU, hU⟩ := h.exists_side
  exact (isConnected_insert hU).isPreconnected.subset_connectedComponentIn
    (mem_insert_of_mem x haU) (by
      intro t ht
      refine ⟨mem_univ _, ?_⟩
      intro he
      rcases he ▸ ht with hyx | hyU'
      · exact h.right_notMem hyx
      · exact hyU hyU') (mem_insert x U)

theorem separationLE_iff_mem_component_of_comparable [PreconnectedSpace K] (a x y : K)
    (hcompare : separationLE a x y ∨ separationLE a y x) :
    separationLE a x y ↔ x = y ∨ x ∈ connectedComponentIn ((univ : Set K) \ {y}) a := by
  constructor
  · rintro (hxa | hxy | h)
    · by_cases hay : a = y
      · exact Or.inl (hxa.trans hay)
      · exact Or.inr (hxa.symm ▸ mem_connectedComponentIn ⟨mem_univ _, hay⟩)
    · exact Or.inl hxy
    · exact Or.inr h.mem_connectedComponentIn
  · rintro (hxy | hx)
    · exact Or.inr (Or.inl hxy)
    by_contra hn
    rcases hcompare.resolve_left hn with hya | hyx | hs
    · have hay := connectedComponentIn_nonempty_iff.mp ⟨x, hx⟩
      exact hay.2 hya.symm
    · exact hn (Or.inr (Or.inl hyx.symm))
    · exact hs.not_subset isPreconnected_connectedComponentIn
        (mem_connectedComponentIn hs.1) hx (connectedComponentIn_subset _ _)

theorem separationLE_iff_mem_component [PreconnectedSpace K] (a b : K)
    (hsep : ∀ z : K, z ≠ a → z ≠ b → Separates univ {z} a b) (x y : K) :
    separationLE a x y ↔ x = y ∨ x ∈ connectedComponentIn ((univ : Set K) \ {y}) a :=
  separationLE_iff_mem_component_of_comparable a x y
    ((separatorLinearOrder a b hsep).le_total x y)

private lemma side_eq_Iio [PreconnectedSpace K] (a b : K)
    (hsep : ∀ z : K, z ≠ a → z ≠ b → Separates univ {z} a b)
    (y : K) (hyU : y ∉ U) (haU : a ∈ U) (hbU : b ∉ U)
    (hU : IsClopen ((Subtype.val : ↥({y}ᶜ : Set K) → K) ⁻¹' U)) :
    letI := separatorLinearOrder a b hsep
    U = Iio y := by
  let := separatorLinearOrder a b hsep
  have hxy {x : K} (hx : x ∈ U) : x ≠ y := fun he ↦ hyU (he ▸ hx)
  ext x
  constructor
  · intro hxU
    apply lt_of_le_of_ne _ (hxy hxU)
    by_cases hxa : x = a
    · exact Or.inl hxa
    have hxb : x ≠ b := fun he ↦ hbU (he ▸ hxU)
    obtain ⟨V, hxV, haV, hbV, hV⟩ := (hsep x hxa hxb).exists_side
    have hyV : y ∉ V := by
      intro hyV
      have hyb := separates_of_side hxV hyV hbV hxb.symm hV
      exact hyb.mem_of_isPreconnected (isConnected_compl hyU hU).isPreconnected hyU hbU hxU
    exact Or.inr (Or.inr (separates_of_side hxV haV hyV (hxy hxU).symm hV))
  · intro hxy'
    change x < y at hxy'
    rcases hxy'.le with he | he | hs
    · exact he.symm ▸ haU
    · exact False.elim (hxy'.ne he)
    · exact (hs.mem_of_isPreconnected (isConnected_insert hU).isPreconnected
        (mem_insert_of_mem y haU) (mem_insert y U)).resolve_left hxy'.ne

private lemma isOpen_of_puncture [T1Space K] (hxU : x ∉ U)
    (hU : IsOpen ((Subtype.val : ↥({x}ᶜ : Set K) → K) ⁻¹' U)) : IsOpen U := by
  have hsub : U ⊆ {x}ᶜ := fun t ht he ↦ hxU (he ▸ ht)
  have hopen := isOpen_compl_singleton.isOpenMap_subtypeVal _ hU
  simpa only [Subtype.image_preimage_coe, inter_eq_right.mpr hsub] using hopen

/-- The order rays are open already under T₁, without compactness.
This is the coarser-topology direction used for noncompact completed circuit components. -/
lemma separatorLinearOrder_isOpen_rays [PreconnectedSpace K] [T1Space K]
    (a b : K)
    (hsep : ∀ z : K, z ≠ a → z ≠ b → Separates univ {z} a b) :
    letI := separatorLinearOrder a b hsep
    ∀ y : K, IsOpen (Ioi y) ∧ IsOpen (Iio y) := by
  let := separatorLinearOrder a b hsep
  obtain ⟨hmin, hmax⟩ := separatorLinearOrder_endpoints a b hsep
  intro y
  by_cases hya : y = a
  · subst y
    have hleft : Iio a = (∅ : Set K) := by ext x; simp [not_lt.mpr (hmin x)]
    have hright : Ioi a = ({a}ᶜ : Set K) := by
      ext x
      exact ⟨fun h ↦ h.ne', fun h ↦ lt_of_le_of_ne (hmin x) (Ne.symm h)⟩
    rw [hleft, hright]
    exact ⟨isOpen_compl_singleton, isOpen_empty⟩
  by_cases hyb : y = b
  · subst y
    have hright : Ioi b = (∅ : Set K) := by ext x; simp [not_lt.mpr (hmax x)]
    have hleft : Iio b = ({b}ᶜ : Set K) := by
      ext x
      exact ⟨fun h ↦ h.ne, fun h ↦ lt_of_le_of_ne (hmax x) h⟩
    rw [hleft, hright]
    exact ⟨isOpen_empty, isOpen_compl_singleton⟩
  obtain ⟨U, hyU, haU, hbU, hU⟩ := (hsep y hya hyb).exists_side
  have he := side_eq_Iio a b hsep y hyU haU hbU hU
  have hright : Ioi y = Uᶜ \ {y} := by
    rw [he]
    ext x
    simp only [mem_Ioi, mem_sdiff, mem_compl_iff, mem_Iio, not_lt, mem_singleton_iff]
    exact ⟨fun h ↦ ⟨h.le, h.ne'⟩, fun h ↦ lt_of_le_of_ne h.1 (Ne.symm h.2)⟩
  refine ⟨?_, he ▸ isOpen_of_puncture hyU hU.isOpen⟩
  rw [hright]
  apply isOpen_of_puncture (x := y) (by simp)
  have he' : (Subtype.val : ↥({y}ᶜ : Set K) → K) ⁻¹' (Uᶜ \ {y}) =
      ((Subtype.val : ↥({y}ᶜ : Set K) → K) ⁻¹' U)ᶜ := by ext t; simp
  rw [he']
  exact hU.compl.isOpen

theorem separatorLinearOrder_orderTopology [PreconnectedSpace K] [CompactSpace K] [T1Space K]
    (a b : K)
    (hsep : ∀ z : K, z ≠ a → z ≠ b → Separates univ {z} a b) :
    letI := separatorLinearOrder a b hsep
    OrderTopology K := by
  let := separatorLinearOrder a b hsep
  exact orderTopology_of_compact_of_isOpen_rays
    (separatorLinearOrder_isOpen_rays a b hsep)

end CutPoint
