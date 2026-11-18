module

public import Mathlib.Init
public meta import Lean.Meta.Tactic.Grind.RegisterCommand

@[expose] public section

/-- Rules for matroid ground-set side conditions. -/
register_grind_attr matroid_ground
