import Matroid.Connectivity.Local
import Matroid.Connectivity.Separation


open Set Set.Notation

namespace Matroid

variable {α : Type*} {M : Matroid α} {B B' I I' J K X Y : Set α}

/- Put the `1` on the RHS! Your version below is stated in terms of `Nat` subtraction,
so will be harder to apply. -/
lemma Exercise_for_DRP' (M : Matroid α) [RankFinite M] (X Y : Set α) (e : α) (heX : e ∉ X)
    (heY : e ∉ Y) :
    M.conn (X ∩ Y) + M.conn (insert e (X ∪ Y)) ≤  1 + (M ＼ e).conn X + (M ／ e).conn Y := by
  -- Apply submodularity fo the pairs `(X, insert e Y)` and `(M.E \ insert e X, Y)`, and simplify.
  have hsm := M.rk_submod X (insert e Y)
  rw [union_insert, inter_insert_of_not_mem heX] at hsm
  have hsm' := M.rk_submod_compl (insert e X) Y
  rw [insert_union, insert_inter_of_not_mem heY] at hsm'
  -- Now `zify` and simplify.
  zify
  simp only [intCast_conn_eq, deleteElem, delete_ground, diff_singleton_diff_eq, contractElem,
    contract_rk_cast_int_eq, union_singleton, contract_ground, insert_diff_insert,
    contract_rank_cast_int_eq]
  -- Rewrite this particular annoying term. If `e ∈ M.E` is assumed, this can be taken
  -- care of more easily .
  have hrw : M.rk (insert e (M.E \ Y)) = M.rk (M.E \ Y) := by
    by_cases he : e ∈ M.E
    · rw [insert_eq_of_mem (by simp [he, heY])]
    rw [rk_insert_of_not_mem_ground _ he]

  have hle : (M ＼ ({e} : Set α)).rank ≤ M.rank := delete_rank_le M {e}
  have hle' : M.rk {e} ≤ 1 := rk_singleton_le M e

  rw [delete_rk_eq_of_disjoint _ (by simpa), delete_rk_eq_of_disjoint _ (by simp), hrw]

  linarith

lemma Exercise_for_DRP (M : Matroid α) [RankFinite M] (X Y : Set α) (e : α) (he : e ∈ M.E)
    (heX : e ∉ X) (heY : e ∉ Y) : M.conn (X ∩ Y) + M.conn (X ∪ Y ∪ {e})
    ≤  (M ＼ e).conn X + (M ／ e).conn Y + 1 := by
  --The proof starts with getting all the equations for the contractions, there is 3 of them
  have : M.rk {e} ≤ 1 := by sorry
  have hconY : M.rk (insert e Y) - 1 = ((M ／ e).rk Y : ℤ ) := by sorry
    -- You can rewrite what it means to contract an element with set notation using contractElem
    -- You can then use the definition of contracting for integers
    -- union_singleton opens insert e X to e ∪ X
    --linarith
  have hconEY : M.rk (M.E \ Y) - 1 = ((M ／ e).rk (M.E \ (insert e Y)) : ℤ ) := by
    --similar to hconY but with an extra step since we need the following observation
    have hins : insert e (M.E \ insert e Y) =  M.E \ Y := by
      sorry
    sorry
  have hconE : M.rank - 1 = ((M ／ e).rk (M.E \ {e}) : ℤ ) := by
    sorry
    -- This may be useful to finsih: rw [insert_diff_self_of_mem he, ←rank_def M]
  --End of the contractions. We are now going to get the equations of submodularity, there is two of them
  have hsub1 : (M.rk ( X ∪ Y ∪ {e}) : ℤ ) + (M.rk ( X ∩ Y) : ℤ)
      ≤ M.rk X + M.rk (insert e Y) := by sorry
  have hsub2 : (M.rk (M.E \ (X ∩ Y)) : ℤ) + (M.rk (M.E \ ( X ∪ Y ∪ {e})) : ℤ)
      ≤ M.rk (M.E \ (insert e X)) + M.rk (M.E \ Y) := by sorry
  --This equation is the last one we need as aid.
  have hneed : ( (M ＼ e).rank : ℤ)  ≤ (M.rank : ℤ) := by sorry
  --We now want to subsitute the definition of connectivity with the following
  have hf : M.conn (X ∩ Y) + M.conn (X ∪ Y ∪ {e}) =
      ((M.rk ( X ∪ Y ∪ {e}) : ℤ ) + ( M.rk ( X ∩ Y)) : ℤ ) +
      ((M.rk (M.E \ (X ∩ Y)) + M.rk (M.E \ ( X ∪ Y ∪ {e}))) : ℤ ) - (2 * M.rank : ℤ ) := by
    --The proof is easy if we use int_cast_conn_eq and linarith
    sorry
  -- To not get annoyed with Lean we use zify. This let's us subtract without getting annoyed
  zify
  -- We use the following 3 to change the rank function of a deletion to the rank function of the matroid
  have hdelx : (M ＼ e).E \ X = M.E \ insert e X := by sorry
  have hconYh : (M ／ e).E \ Y = M.E \ insert e Y :=  by sorry
  have hrkcon : (M ／ e).rk (M.E \ {e}) = (M ／ e).rank := rk_eq_rank fun ⦃a⦄ a ↦ a
  --Here I used a lot of rw
  rw [intCast_conn_eq (M ＼ e) X, intCast_conn_eq (M ／ e) Y, hf ]
  rw[delete_elem_rk_eq, delete_elem_rk_eq, hdelx, hconYh, ←hrkcon]
  · linarith
  · sorry
  sorry
-- gh repo clone apnelson1/Matroid

lemma book_854 (M : Matroid α) [RankFinite M] (X' Y': Set α  ) (hX'E : X' ⊆ M.E )
    (hY'E : Y' ⊆ M.E \ X' ) (hXX' : X ⊆ X') (hYY' : Y ⊆ Y') :
    M.connBetween X Y ≤ M.connBetween X' Y' := by sorry

--The correct notation is connBetween, see Separation for the infinite version,
--Peter is adding a bunch of lemmas to this section

lemma exists_partition_Conn_eq_ConnBetween (hXY : Disjoint X Y) (hXE : X ⊆ M.E) (hYE : Y ⊆ M.E) :
    ∃ P : M.Partition, P.SepOf X Y ∧ P.eConn = M.connBetween X Y := by sorry

lemma book_855_del {X₁ D : Set α} (M : Matroid α) [RankFinite M] (hX₁E : X₁ ⊆ M.E) :
    ( M ＼ D ).connBetween (X₁ \ D) ((M.E \ X₁) \ D) ≤ M.connBetween X₁ (M.E \ X₁) := by
  suffices hi : ∀ i : ℕ, D.ncard ≤ i → ( M ＼ D ).connBetween (X₁ \ D) ((M.E \ X₁) \ D) ≤ M.connBetween X₁ (M.E \ X₁)
  · sorry
  · intro i hi
    induction' i with n IH generalizing D
    have hD : D = ∅ := by sorry --Ask Peter
    rw [hD]
    simp only [delete_empty, diff_empty, le_refl]
    --Induction step
    sorry

lemma book_855 {C D X' Y': Set α} (M : Matroid α) [RankFinite M] (hX' : X' ⊆ M.E ) (hY' : Y' ⊆ M.E \ X')
    (hX : X ⊆ X' \ (C ∪ D)) (hY : Y ⊆ (Y' \ (C ∪ D)))  :
    ((M ／ C ) ＼ D ).connBetween X Y ≤ M.connBetween X' Y' := by
  --Suffices is a tactic used to reduce the goal to prove something that implies the goal. It creates two goals.
  --The first goal is to prove that the new hypothesis implies the result
  -- Second goal is to prove the added hypothesis
  --We will be using this tactic to set up the induction late
  suffices hNM : ((M ／ C ) ＼ D ).connBetween X Y ≤ M.connBetween X Y
  · have h854 : M.connBetween X Y ≤ M.connBetween X' Y' := by sorry
    exact Nat.le_trans hNM h854
  · have hex : ∃ X₁ ⊆ M.E, X ⊆ X₁ ∧ Y ⊆ M.E \ X₁ ∧ M.connBetween X₁ (M.E \ X₁) = M.connBetween X Y := by
      sorry
      --Let's leave this one like this for now.
      --Peter seems to have a similar lemma for eNat and I will bug him to make it for connBetween
    obtain ⟨X₁, hX₁ ⟩ := hex
    have h813 : ((M ／ C ) ＼ D ).connBetween (X₁ \ (D ∪ C)) ((M.E \ X₁) \ (D ∪ C))
        ≤ M.connBetween X₁ (M.E \ X₁) := by
      sorry
    sorry


--There are 3 things to work in for next week:
--Lemma book_854 should be the easiest mathematically but I didn't add anything to the lean proof.
--Lemma book_855 has a sketch. Hardes part is using duality to apply lemma book_855_del.
--This one will have one sorry.
--Lemma book_855_del is the series of inequalities form the book but we need to use induction instead of just saying wlog.
--Alternatively the same proof without induction will work by dividing D into X₁ and the complement.
