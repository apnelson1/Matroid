import Matroid.Graph.Degree.Leaf

variable {α β : Type*} {x y z u v w : α} {e f : β} {G H : Graph α β} {F F₁ F₂ : Set β} {X Y : Set α}
{d : ℕ}

open Set WList

namespace Graph

/-! ### Minimum degree -/


/-- `G.MinDegreePos` means that `G` has no degree-zero vertices. -/
def MinDegreePos (G : Graph α β) : Prop := ∀ ⦃x⦄, x ∈ V(G) → ∃ e, G.Inc e x

lemma MinDegreePos.one_le_eDegree (hG : G.MinDegreePos) (hx : x ∈ V(G)) : 1 ≤ G.eDegree x := by
  rw [ENat.one_le_iff_ne_zero]
  simp only [ne_eq, eDegree_eq_zero_iff_inc, not_forall, not_not]
  exact hG hx

lemma MinDegreePos.one_le_degree [G.LocallyFinite] (hG : G.MinDegreePos) (hx : x ∈ V(G)) :
    1 ≤ G.degree x := by
  rw [← Nat.cast_le (α := ℕ∞), natCast_degree_eq]
  exact hG.one_le_eDegree hx

lemma MinDegreePos.finite_of_edgeSet_finite (hG : G.MinDegreePos) (hE : E(G).Finite) :
    G.Finite where
  vertexSet_finite := by
    have hle := ENat.tsum_le_tsum (f := fun x : V(G) ↦ 1) (g := fun x : V(G) ↦ G.eDegree x)
    simp only [Pi.le_def, Subtype.coe_prop, (fun x ↦ hG.one_le_eDegree), implies_true,
      ENat.tsum_subtype_const, one_mul, G.handshake_eDegree_subtype, forall_const] at hle
    rw [← encard_lt_top_iff] at hE ⊢
    generalize ha : E(G).encard = a at hle hE
    generalize hb : V(G).encard = b at hle
    enat_to_nat
  edgeSet_finite := hE

lemma MinDegreePos.edgeSet_finite_iff (hG : G.MinDegreePos) : E(G).Finite ↔ G.Finite :=
  ⟨hG.finite_of_edgeSet_finite, fun h ↦ h.edgeSet_finite⟩
