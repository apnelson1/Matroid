import Matroid.Connectivity.Local

open Set Set.Notation

namespace Matroid

variable {α : Type*} {M : Matroid α} {B B' I I' J K X Y : Set α}


lemma Exercise_for_DRP (M : Matroid α) [FiniteRk M] (X Y : Set α) (e : α) (he : e ∈ M.E) (heco : M.Nonloop e)
    (heX : e ∉ X) (heY : e ∉ Y) : M.conn (X ∩ Y) + M.conn (X ∪ Y ∪ {e}) - 1
    ≤  (M ＼ e).conn X + (M ／ e).conn Y := by
  --The proof starts with getting all the equations for the contractions, there is 3 of them
  have : M.rk {e} = 1 := Nonloop.rk_eq sorry
  --Here is where you use that 'e' is not a loop
  have hconY : M.rk (insert e Y) - 1 = ((M ／ e).rk Y : ℤ ) := by sorry
    -- You can rewrite what it means to contract an element with set notation using contract_elem
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
  have hf : M.conn (X ∩ Y) + M.conn (X ∪ Y ∪ {e}) - 1 =
      ((M.rk ( X ∪ Y ∪ {e}) : ℤ ) + ( M.rk ( X ∩ Y)) : ℤ ) +
      ((M.rk (M.E \ (X ∩ Y)) + M.rk (M.E \ ( X ∪ Y ∪ {e}))) : ℤ ) - (2 * M.rank : ℤ ) -1 := by
    --The proof is easy if we use int_cast_conn_eq and linarith
    sorry
  -- To not get annoyed with Lean we use zify. This let's us subtract without getting annoyed
  zify
  -- We use the following 3 to change the rank function of a deletion to the rank function of the matroid
  have hdelx : (M ＼ e).E \ X = M.E \ insert e X := by sorry
  have hconYh : (M ／ e).E \ Y = M.E \ insert e Y :=  by sorry
  have hrkcon : (M ／ e).rk (M.E \ {e}) = (M ／ e).rank := rk_eq_rank fun ⦃a⦄ a ↦ a
  --Here I used a lot of rw
  rw [Nat.cast_sub, Nat.cast_add, int_cast_conn_eq (M ＼ e) X, int_cast_conn_eq (M ／ e) Y, Nat.cast_one, hf ]
  rw[delete_elem_rk_eq, delete_elem_rk_eq, hdelx, hconYh, ←hrkcon]
  · linarith
  · sorry
  sorry
  zify
  sorry

-- gh repo clone apnelson1/Matroid
