import Mathlib.Tactic.Tauto

lemma iff_of_imp_iff {A B C : Prop} (h1 : A → C) (h2 : B → C) (h3 : C → (A ↔ B)) : A ↔ B := by
  tauto
