import Lean

-- variable {Foo : ℕ∞ → Prop} {Bar : Prop}

-- example (foo_imp_bar : ∀ x, Foo x → Bar) (h : Foo 2) : Bar := by
--   grind -- succeeds

-- set_option pp.all true
-- example (foo_imp_bar : ∀ x, Foo x → Bar) (h : Foo 2) : Bar := by
--   norm_cast at h
--   grind -- succeeds

-- example (foo_imp_bar : ∀ x, Foo x → Bar) (h : Foo 2) : Bar := by
--   norm_cast at h
--   norm_cast at h
--   -- any larger number of norm_casts succeed but seem to do nothing
--   grind -- fails

-- example (foo_imp_bar : ∀ x, Foo x → Bar) (h : Foo 1) : Bar := by
--   norm_cast at h
--   -- warning is given that norm_cast did nothing
--   grind  -- succeeds
