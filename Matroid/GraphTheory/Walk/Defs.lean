/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Mathlib.Data.Sym.Sym2
public import Mathlib.Data.Set.Card

/-!
# Walks in a graph

-/

@[expose] public section

open Set Function Nat

inductive Walk {V : Type*} : Type _ → Type _ → V → V → Type _ where
| nil (I E : Type*) (v : V) : Walk I E v v
| cons {I E : Type _} (u : V) (i : I) (e : E) (j : I) {v w : V} (W : Walk I E v w) : Walk I E u w

namespace Walk

variable {V I E : Type*}

def 


end Walk
