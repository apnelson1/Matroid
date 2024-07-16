import Matroid.Constructions.Matching
import Matroid.Constructions.DirectSum

namespace Matroid

universe u

variable {α ι : Type*}

protected def Union [DecidableEq α] (Ms : ι → Matroid α) : Matroid α :=
  (Matroid.prod Ms).adjMap (fun x y ↦ x.2 = y) Set.univ

lemma union_indep_iff [DecidableEq α] {Ms : ι → Matroid α} (h : ∀ i, (Ms i).Finitary) :
  Matroid.union
