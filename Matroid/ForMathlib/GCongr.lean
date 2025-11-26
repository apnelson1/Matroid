import Matroid.ForMathlib.Matroid.Closure

namespace Matroid

variable {α : Type*} {M : Matroid α} {X Y : Set α} {e f : α}

@[gcongr]
lemma Indep.mono (hXY : X ⊆ Y) (hY : M.Indep Y) : M.Indep X := hY.subset hXY

@[gcongr]
lemma Nonspanning.mono (hXY : X ⊆ Y) (hY : M.Nonspanning Y) : M.Nonspanning X := hY.subset hXY

attribute [gcongr] Matroid.closure_subset_closure

attribute [gcongr] Set.encard_le_encard
