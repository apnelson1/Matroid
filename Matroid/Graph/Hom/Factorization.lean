module

public import Matroid.ForMathlib.Function
public import Matroid.Graph.Hom.Image

/-!
# Factorization of graph homomorphisms

`Q.FactorsThrough P` means that `Q = P.comp D` for a homomorphism `D`. Its chosen `factor`
requires only this existence hypothesis. The factor is unique when `P.Surjective`,
which expresses surjectivity onto the whole target. Under this hypothesis, factorization
is equivalent to factorization of both carrier maps. Mutual factorization compares two
surjective presentations by an isomorphism. Composition is in diagrammatic order.
-/

@[expose] public section

open Function

namespace Graph.Hom

variable {V₀ E₀ V₁ E₁ V₂ E₂ V₃ E₃ : Type*} {G : Graph V₀ E₀} {H : Graph V₁ E₁} {K : Graph V₂ E₂}
  {L : Graph V₃ E₃} {P : Hom G H} {Q : Hom G K} {R : Hom G L}

/-- A link using an edge in the image lifts to coherent source endpoints.
Coverage of other edges and vertices is not required. -/
theorem exists_isLink_of_mem_edgeImage (P : Hom G H)
    {e : E(H)} (he : e.1 ∈ P.edgeImage) {x y : V(H)} (h : H.IsLink e.1 x.1 y.1) :
    ∃ (e₀ : E(G)) (x₀ y₀ : V(G)), G.IsLink e₀.1 x₀.1 y₀.1 ∧
      P.edgeMap e₀ = e ∧ P.vertMap x₀ = x ∧ P.vertMap y₀ = y := by
  obtain ⟨e₀, he₀⟩ := P.mem_edgeImage_iff.mp he
  obtain rfl : P.edgeMap e₀ = e := Subtype.ext he₀
  obtain ⟨u₀, v₀, huv⟩ := G.exists_isLink_of_mem_edgeSet e₀.2
  have h' := P.map_isLink (x := ⟨u₀, huv.left_mem⟩) (y := ⟨v₀, huv.right_mem⟩) huv
  obtain ⟨hx, hy⟩ | ⟨hx, hy⟩ := h.eq_and_eq_or_eq_and_eq h'
  · exact ⟨e₀, ⟨u₀, huv.left_mem⟩, ⟨v₀, huv.right_mem⟩, huv, rfl,
      Subtype.ext hx.symm, Subtype.ext hy.symm⟩
  · exact ⟨e₀, ⟨v₀, huv.right_mem⟩, ⟨u₀, huv.left_mem⟩, huv.symm, rfl,
      Subtype.ext hx.symm, Subtype.ext hy.symm⟩

/-- `Q` factors through `P` by a homomorphism on the entire target of `P`. -/
def FactorsThrough (Q : Hom G K) (P : Hom G H) : Prop :=
  ∃ D : Hom H K, P.comp D = Q

namespace FactorsThrough

/-- Choose a factor from the supplied factorization. Surjectivity is needed for uniqueness,
not for this construction. -/
noncomputable def factor (h : Q.FactorsThrough P) : Hom H K := h.choose

/-- Every homomorphism factors through itself via the identity. -/
protected theorem rfl (P : Hom G H) : P.FactorsThrough P :=
  ⟨Hom.id H, P.comp_id⟩

/-- Compose the supplied factorization witnesses. -/
theorem trans (hRQ : R.FactorsThrough Q) (hQP : Q.FactorsThrough P) : R.FactorsThrough P :=
  ⟨hQP.factor.comp hRQ.factor, by
    have hQP' : P.comp hQP.factor = Q := by simpa [factor] using hQP.choose_spec
    have hRQ' : Q.comp hRQ.factor = R := by simpa [factor] using hRQ.choose_spec
    rw [← Hom.comp_assoc, hQP', hRQ']⟩

/-- The chosen factor solves the factorization equation. -/
theorem comp_factor (h : Q.FactorsThrough P) : P.comp h.factor = Q :=
  h.choose_spec

@[simp]
theorem factor_vertMap_apply (h : Q.FactorsThrough P) (x : V(G)) :
    h.factor.vertMap (P.vertMap x) = Q.vertMap x :=
  congrArg (fun F : Hom G K ↦ F.vertMap x) h.comp_factor

@[simp]
theorem factor_edgeMap_apply (h : Q.FactorsThrough P) (e : E(G)) :
    h.factor.edgeMap (P.edgeMap e) = Q.edgeMap e :=
  congrArg (fun F : Hom G K ↦ F.edgeMap e) h.comp_factor

/-- A homomorphism factorization induces a factorization on vertices. -/
theorem vertMap (h : Q.FactorsThrough P) : Q.vertMap.FactorsThrough P.vertMap :=
  fun x y hxy ↦ (h.factor_vertMap_apply x).symm.trans (congrArg h.factor.vertMap hxy) |>.trans
    (h.factor_vertMap_apply y)

/-- A homomorphism factorization induces a factorization on edges. -/
theorem edgeMap (h : Q.FactorsThrough P) : Q.edgeMap.FactorsThrough P.edgeMap :=
  fun e f hef ↦ (h.factor_edgeMap_apply e).symm.trans (congrArg h.factor.edgeMap hef) |>.trans
    (h.factor_edgeMap_apply f)

/-- A factor through the whole target is uniquely determined by its composite. -/
theorem factor_eq_iff (h : Q.FactorsThrough P) (hP : P.Surjective) (D : Hom H K) :
    h.factor = D ↔ P.comp D = Q := by
  exact ⟨fun hD ↦ hD ▸ h.comp_factor, fun hD ↦ P.comp_right_injective hP.vertMap hP.edgeMap
    <| h.comp_factor.trans hD.symm⟩

/-- Vertex surjectivity alone preserves the vertex image of a factor. -/
theorem vertexImage_factor (h : Q.FactorsThrough P) (hP : Function.Surjective P.vertMap) :
    h.factor.vertexImage = Q.vertexImage := by
  ext v
  constructor
  · rintro ⟨u, rfl⟩
    obtain ⟨x, hx⟩ := hP u
    exact ⟨x, congrArg Subtype.val (hx ▸ (h.factor_vertMap_apply x).symm)⟩
  · rintro ⟨x, rfl⟩
    exact ⟨P.vertMap x, congrArg Subtype.val (h.factor_vertMap_apply x)⟩

/-- Edge surjectivity alone preserves the edge image of a factor. -/
theorem edgeImage_factor (h : Q.FactorsThrough P) (hP : Function.Surjective P.edgeMap) :
    h.factor.edgeImage = Q.edgeImage := by
  ext e
  constructor
  · rintro ⟨f, rfl⟩
    obtain ⟨e₀, he₀⟩ := hP f
    exact ⟨e₀, congrArg Subtype.val (he₀ ▸ (h.factor_edgeMap_apply e₀).symm)⟩
  · rintro ⟨e₀, rfl⟩
    exact ⟨P.edgeMap e₀, congrArg Subtype.val (h.factor_edgeMap_apply e₀)⟩

/-- Factoring through a surjection does not change the image in the final target. -/
theorem image_factor (h : Q.FactorsThrough P) (hP : P.Surjective) :
    h.factor.Image = Q.Image := by
  apply Graph.ext_of_le_le h.factor.image_le Q.image_le
  · simpa only [Hom.image_vertexSet] using h.vertexImage_factor hP.vertMap
  · simpa only [Hom.image_edgeSet] using h.edgeImage_factor hP.edgeMap

theorem factor_vertMap_surjective_iff (h : Q.FactorsThrough P)
    (hP : Function.Surjective P.vertMap) :
    Function.Surjective h.factor.vertMap ↔ Function.Surjective Q.vertMap := by
  have hV' := h.vertexImage_factor hP
  rw [← h.factor.vertexImage_eq_iff, ← Q.vertexImage_eq_iff]
  exact ⟨fun hv ↦ hV'.symm.trans hv, fun hv ↦ hV'.trans hv⟩

theorem factor_edgeMap_surjective_iff (h : Q.FactorsThrough P)
    (hP : Function.Surjective P.edgeMap) :
    Function.Surjective h.factor.edgeMap ↔ Function.Surjective Q.edgeMap := by
  have hE' := h.edgeImage_factor hP
  rw [← h.factor.edgeImage_eq_iff, ← Q.edgeImage_eq_iff]
  exact ⟨fun he ↦ hE'.symm.trans he, fun he ↦ hE'.trans he⟩

theorem factor_vertMap_injective_iff (h : Q.FactorsThrough P) (hP : Function.Surjective P.vertMap) :
    Injective h.factor.vertMap ↔ P.vertMap.FactorsThrough Q.vertMap := by
  refine ⟨fun hinj x y hxy ↦ hinj ?_, fun hthrough u v huv ↦ ?_⟩
  · rw [h.factor_vertMap_apply x, h.factor_vertMap_apply y, hxy]
  · obtain ⟨x, rfl⟩ := hP u
    obtain ⟨y, rfl⟩ := hP v
    apply hthrough
    rw [← h.factor_vertMap_apply x, ← h.factor_vertMap_apply y]
    exact huv

theorem factor_edgeMap_injective_iff (h : Q.FactorsThrough P) (hP : Function.Surjective P.edgeMap) :
    Injective h.factor.edgeMap ↔ P.edgeMap.FactorsThrough Q.edgeMap := by
  refine ⟨fun hinj e f hef ↦ hinj ?_, fun hthrough e f hef ↦ ?_⟩
  · rw [h.factor_edgeMap_apply e, h.factor_edgeMap_apply f, hef]
  · obtain ⟨e₀, rfl⟩ := hP e
    obtain ⟨f₀, rfl⟩ := hP f
    apply hthrough
    rw [← h.factor_edgeMap_apply e₀, ← h.factor_edgeMap_apply f₀]
    exact hef

@[simp]
theorem factor_self (h : P.FactorsThrough P) (hP : P.Surjective) : h.factor = Hom.id H :=
  (h.factor_eq_iff hP (Hom.id H)).mpr P.comp_id

/-- Composition of factors is determined by the original surjective presentation.
The intermediate presentation need not be surjective. -/
theorem factor_comp (hQP : Q.FactorsThrough P) (hRQ : R.FactorsThrough Q)
    (hP : P.Surjective) : hQP.factor.comp hRQ.factor = (hRQ.trans hQP).factor := by
  symm
  apply ((hRQ.trans hQP).factor_eq_iff hP (hQP.factor.comp hRQ.factor)).mpr
  rw [← Hom.comp_assoc, hQP.comp_factor, hRQ.comp_factor]

end FactorsThrough

-- Carrier coordinates belong only to the construction behind the public existence bridge.
private noncomputable def factorOfMaps (hP : P.Surjective)
    (hV : Q.vertMap.FactorsThrough P.vertMap) (hE : Q.edgeMap.FactorsThrough P.edgeMap) :
    Hom H K where
  vertMap := hP.vertMap.factor Q.vertMap
  edgeMap := hP.edgeMap.factor Q.edgeMap
  map_isLink e x y hxy := by
    obtain ⟨e₀, x₀, y₀, hxy₀, rfl, rfl, rfl⟩ := P.exists_isLink_of_mem_edgeImage
      ((P.edgeImage_eq_iff.mpr hP.edgeMap).symm ▸ e.2) hxy
    rw [hE.factor_apply hP.edgeMap e₀, hV.factor_apply hP.vertMap x₀,
      hV.factor_apply hP.vertMap y₀]
    exact Q.map_isLink hxy₀

/-- Compatible carrier maps give an actual factorization when `P` is surjective. -/
theorem factorsThrough_of_maps (hP : P.Surjective)
    (hV : Q.vertMap.FactorsThrough P.vertMap) (hE : Q.edgeMap.FactorsThrough P.edgeMap) :
    Q.FactorsThrough P :=
  ⟨factorOfMaps hP hV hE, Hom.ext (fun x ↦ hV.factor_apply _ x) (fun e ↦ hE.factor_apply _ e)⟩

/-- On a surjective presentation, carrier compatibility characterizes homomorphism factorization. -/
theorem factorsThrough_iff (hP : P.Surjective) :
    Q.FactorsThrough P ↔ Q.vertMap.FactorsThrough P.vertMap ∧ Q.edgeMap.FactorsThrough P.edgeMap :=
  ⟨fun h ↦ ⟨h.vertMap, h.edgeMap⟩, fun ⟨hV, hE⟩ ↦ factorsThrough_of_maps hP hV hE⟩

/-- Mutual factorizations of surjective presentations give an isomorphism between their targets.
The two supplied factorizations provide the forward map and its specified inverse. -/
noncomputable def isoOfFactorsThrough (hP : P.Surjective) (hQ : Q.Surjective)
    (h : Q.FactorsThrough P) (h' : P.FactorsThrough Q) : Iso H K where
  toHom := h.factor
  vertMap_injective := (h.factor_vertMap_injective_iff hP.vertMap).mpr h'.vertMap
  edgeMap_injective := (h.factor_edgeMap_injective_iff hP.edgeMap).mpr h'.edgeMap
  invVertMap := h'.factor.vertMap
  invEdgeMap := h'.factor.edgeMap
  vertMap_leftInverse x := by
    obtain ⟨x₀, hx⟩ := hP.vertMap x
    rw [← hx, h.factor_vertMap_apply x₀, h'.factor_vertMap_apply x₀]
  vertMap_rightInverse x := by
    obtain ⟨x₀, hx⟩ := hQ.vertMap x
    rw [← hx, h'.factor_vertMap_apply x₀, h.factor_vertMap_apply x₀]
  edgeMap_leftInverse e := by
    obtain ⟨e₀, he⟩ := hP.edgeMap e
    rw [← he, h.factor_edgeMap_apply e₀, h'.factor_edgeMap_apply e₀]
  edgeMap_rightInverse e := by
    obtain ⟨e₀, he⟩ := hQ.edgeMap e
    rw [← he, h'.factor_edgeMap_apply e₀, h.factor_edgeMap_apply e₀]

@[simp]
theorem isoOfFactorsThrough_toHom (hP : P.Surjective) (hQ : Q.Surjective)
    (h : Q.FactorsThrough P) (h' : P.FactorsThrough Q) :
    (isoOfFactorsThrough hP hQ h h').toHom = h.factor :=
  rfl

@[simp]
theorem isoOfFactorsThrough_invVertMap_apply (hP : P.Surjective) (hQ : Q.Surjective)
    (h : Q.FactorsThrough P) (h' : P.FactorsThrough Q) (x : V(G)) :
    (isoOfFactorsThrough hP hQ h h').invVertMap (Q.vertMap x) = P.vertMap x :=
  h'.factor_vertMap_apply x

@[simp]
theorem isoOfFactorsThrough_invEdgeMap_apply (hP : P.Surjective) (hQ : Q.Surjective)
    (h : Q.FactorsThrough P) (h' : P.FactorsThrough Q) (e : E(G)) :
    (isoOfFactorsThrough hP hQ h h').invEdgeMap (Q.edgeMap e) = P.edgeMap e :=
  h'.factor_edgeMap_apply e

@[simp]
theorem isoOfFactorsThrough_symm (hP : P.Surjective) (hQ : Q.Surjective)
    (h : Q.FactorsThrough P) (h' : P.FactorsThrough Q) :
    (isoOfFactorsThrough hP hQ h h').symm = isoOfFactorsThrough hQ hP h' h := by
  apply Iso.ext <;> intro <;> rfl

@[simp]
theorem isoOfFactorsThrough_self (hP : P.Surjective) (h h' : P.FactorsThrough P) :
    isoOfFactorsThrough hP hP h h' = Iso.id H :=
  Iso.toHom_injective <| h.factor_self hP

/-- Comparison of three surjective presentations is coherent. -/
theorem isoOfFactorsThrough_comp (hP : P.Surjective) (hQ : Q.Surjective)
    (hR : R.Surjective) (h : Q.FactorsThrough P) (h' : P.FactorsThrough Q)
    (j : R.FactorsThrough Q) (j' : Q.FactorsThrough R) :
    (isoOfFactorsThrough hP hQ h h').comp (isoOfFactorsThrough hQ hR j j') =
      isoOfFactorsThrough hP hR (j.trans h) (h'.trans j') :=
  Iso.toHom_injective <| h.factor_comp j hP

end Graph.Hom
