import Init.Prelude

structure natWithProof (b : Bool) where
  n : ℕ
  nothing : True

variable {b : Bool} {RedHerring : natWithProof b}

def copy₁ (p : natWithProof b) : natWithProof b where
  n := p.n
  nothing := trivial

#check copy₁
-- succ₂ {b : Bool} (p : natWithProof b) : natWithProof b

omit RedHerring in
def copy₂ (p : natWithProof b) : natWithProof b where
  n := p.n
  nothing := by cases b with trivial

#check copy₂
-- succ₁ {b : Bool} {RedHerring : natWithProof b} (p : natWithProof b) : natWithProof b
-- garbage gets included in the type signature of `copy₂`, even when it is explicitly omitted.
