import Mathlib.Data.Set.Basic

variable {π : α → Type _}

def Function.restrict (f : ∀ a : α, π a) (s : Set α) : ∀ a : s, π a := fun x => f x

-- notation:1000 lhs:1024 " ↾ " rhs:1000 => (Function.restrict lhs rhs)
infix:1023 " ↾ " => Function.restrict

theorem restrict_eq (f : α → β) (s : Set α) : (f ↾ s) = f ∘ Subtype.val := rfl

theorem id_restrict_eq (s : Set α) : id ↾ s = Subtype.val := rfl

@[simp] theorem restrict_apply (f : α → β) (s : Set α) (x : s) : Function.restrict f s x = f x := rfl
