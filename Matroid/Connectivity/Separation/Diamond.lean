import Matroid.Connectivity.Separation.Vertical

namespace Matroid

open Set Separation

variable {i b c d : Bool} {α : Type*} {e f g : α} {C D K T X : Set α} {M N M₀ M₁ : Matroid α}
  {k : ℕ∞} {w : Matroid α → Set α → ℕ∞} {f : ℕ∞ → ℕ∞} {rem : Bool → Bool}

@[ext]
structure Diamond (M M₀ M₁ : Matroid α) where
  isMinor_left_top : M₀ ≤m M
  isMinor_right_top : M₁ ≤m M
  left : M₀.Separation
  right : M₁.Separation

variable {Δ : M.Diamond M₀ M₁}

namespace Diamond

@[simps]
protected def copy {N N₀ N₁ : Matroid α} (Δ : Diamond M M₀ M₁) (h : M = N) (h₀ : M₀ = N₀)
    (h₁ : M₁ = N₁) : N.Diamond N₀ N₁ where
  isMinor_left_top := by subst h h₀; exact Δ.isMinor_left_top
  isMinor_right_top := by subst h h₁; exact Δ.isMinor_right_top
  left := Δ.left.copy h₀
  right := Δ.right.copy h₁

@[simps]
protected def symm (Δ : Diamond M M₀ M₁) : Diamond M M₁ M₀ where
  isMinor_left_top := Δ.isMinor_right_top
  isMinor_right_top := Δ.isMinor_left_top
  left := Δ.right
  right := Δ.left

@[simp]
lemma copy_symm {N N₀ N₁ : Matroid α} (Δ : Diamond M M₀ M₁) (h : M = N) (h₀ : M₀ = N₀)
    (h₁ : M₁ = N₁) : (Δ.copy h h₀ h₁).symm = Δ.symm.copy h h₁ h₀ := by
  ext <;> simp

def top (Δ : M.Diamond M₀ M₁) (b c : Bool) : M.Separation :=
  bif b then Δ.left.ofGroundSubset Δ.isMinor_left_top.subset c
    else Δ.right.ofGroundSubset Δ.isMinor_right_top.subset c

@[simp]
lemma top_symm (Δ : M.Diamond M₀ M₁) : Δ.symm.top b c = Δ.top (!b) c := by
  simp [top]

@[simp]
lemma top_eq_ofDelete_left (Δ : M.Diamond (M ＼ D) M₁) (c : Bool) :
    Δ.top true c = Δ.left.ofDelete c := rfl

@[simp]
lemma top_eq_ofDelete_right (Δ : M.Diamond M₀ (M ＼ D)) (c : Bool) :
    Δ.top false c = Δ.right.ofDelete c := rfl

@[simp]
lemma top_eq_ofContract_left (Δ : M.Diamond (M ／ C) M₁) (c : Bool) :
    Δ.top true c = Δ.left.ofContract c := rfl

@[simp]
lemma top_eq_ofContract_right (Δ : M.Diamond M₀ (M ／ C)) (c : Bool) :
    Δ.top false c = Δ.right.ofContract c := rfl

@[simp]
lemma top_eq_ofRemove_left (Δ : M.Diamond (M.remove X b) M₁) (c : Bool) :
    Δ.top true c = Δ.left.ofRemove c := rfl

@[simp]
lemma top_eq_ofRemove_right (Δ : M.Diamond M₀ (M.remove X b)) (c : Bool) :
    Δ.top false c = Δ.right.ofRemove c := rfl

def diffLeft (_ : M.Diamond M₀ M₁) : Set α := M.E \ M₀.E

@[simp]
lemma diffLeft_delete (Δ : M.Diamond (M ＼ D) M₁) (hD : D ⊆ M.E := by aesop_mat) :
    Δ.diffLeft = D := by
  simpa [diffLeft]

@[simp]
lemma diffLeft_contract (Δ : M.Diamond (M ／ C) M₁) (hC : C ⊆ M.E := by aesop_mat) :
    Δ.diffLeft = C := by
  simpa [diffLeft]

@[simp]
lemma diffLeft_remove {b : Bool} (Δ : M.Diamond (M.remove X b) M₁)
    (hX : X ⊆ M.E := by aesop_mat) : Δ.diffLeft = X := by
  simpa [diffLeft]

def diffRight (_ : M.Diamond M₀ M₁) : Set α := M.E \ M₁.E

@[simp]
lemma diffRight_delete (Δ : M.Diamond M₀ (M ＼ D)) (hD : D ⊆ M.E := by aesop_mat) :
    Δ.diffRight = D := by
  simpa [diffRight]

@[simp]
lemma diffRight_contract (Δ : M.Diamond M₀ (M ／ C)) (hC : C ⊆ M.E := by aesop_mat) :
    Δ.diffRight = C := by
  simpa [diffRight]

@[simp]
lemma diffright_remove {b : Bool} (Δ : M.Diamond M₀ (M.remove X b))
    (hX : X ⊆ M.E := by aesop_mat) : Δ.diffRight = X := by
  simpa [diffRight]

lemma bc1 (Δ : M.Diamond (M ／ X) (M ＼ X)) (b c₁ c₂ : Bool) :
    ((Δ.top b c₁).inter (Δ.top (!b) c₂) (!c₁) (!c₂)).eConn +
    ((Δ.top b !c₁).inter (Δ.top (!b) !c₂) c₁ c₂).eConn
    ≤ Δ.left.eConn + Δ.right.eConn + M.eConn X := by
  cases b
  · simp only [top_eq_ofDelete_right, Bool.not_false, top_eq_ofContract_left,
      ← Separation.eConn_eq _ true (M := M), Separation.inter_apply_true, ofDelete_apply_not,
      ofContract_apply_not, ofDelete_not_apply, ofContract_not_apply]
    grw [← Δ.left.eConn_inter_add_eConn_inter_le]



    -- obtain rfl | rfl := c₁.eq_or_eq_not c₂
    -- · simp [← Separation.eConn_eq _ true (M := M)]
    --   rw [Separation.ofDelete_apply, Separation.ofContract_apply]
    --   simp
    --   simp only [top_eq_ofDelete_right, Bool.not_false, top_eq_ofContract_left, bne_self_eq_false,
    --   BEq.rfl]
    --   rw [← Separation.eConn_eq _ true]
    --   grw [← Δ.left.eConn_inter_add_eConn_inter_le_add Δ.right false, Separation.inter_apply_true,
    --     Separation.ofDelete_apply, Separation.ofContract_apply]
    --   simp

    --   cases c₁
    --   · simp

    --     rw [Separation.ofDelete_apply, Separation.ofContract_apply]
    --     simp

    -- cases c₁
    -- · cases c₂
    --   · simp
    --     rw [← Separation.eConn_eq _ true]
    --     simp
    --     have := Δ.left.eConn_inter_add_eConn_inter_le_add Δ.right false
    --     simp



    -- simp

-- /-- The generalized Bixby-Coullard inequality for pairs of separations. -/
-- lemma eConn_inter_add_eConn_inter_le_add (P : (M ／ X).Separation) (Q : (M ＼ X).Separation)
--     (i : Bool) :
--     M.eConn (P i ∩ Q i) + M.eConn (P (!i) ∩ Q (!i)) ≤ P.eConn + Q.eConn + M.eConn X := by00
