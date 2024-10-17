import Matroid.Extension

namespace Matroid

variable {α β : Type*} {e : α} {f : β}

def TwoSum (M : Matroid α) (N : Matroid β) (e : α) (f : β) : Matroid (α ⊕ β) := by
  let MN := M.sum N
  let L : Set (α ⊕ β) := {.inl e, .inr f}
  exact ((MN.projectBy <| ModularCut.principal MN L) ＼ L)
