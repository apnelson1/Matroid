/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Mathlib.Data.PEquiv
public import Mathlib.Data.Set.Card

/-!
# Partial equivalences from embeddings

This file constructs a partial equivalence on ambient types from an embedding whose domain is a
subtype.
-/

@[expose] public section

open Set Function

/-- An embedding defined on a subset, regarded as a partial equivalence of the ambient types. -/
noncomputable def PEquiv.ofEmbedding {α β : Type*} {s : Set α} (f : s ↪ β) : α ≃. β := by
  classical
  exact
    { toFun := fun a => if h : a ∈ s then some (f ⟨a, h⟩) else none
      invFun := fun b =>
        if h : b ∈ Set.range f then some (((Equiv.ofInjective f f.injective).symm ⟨b, h⟩ : s) : α)
        else none
      inv a b:= by
        by_cases ha : a ∈ s
        · by_cases hb : b ∈ Set.range (f : s → β)
          · simp only [ha, hb, ↓reduceDIte, Option.some.injEq]
            constructor
            · rintro rfl
              simpa using Equiv.apply_ofInjective_symm (f := (f : s → β)) f.injective ⟨b, hb⟩
            · rintro rfl
              simp
          · simp only [ha, hb, ↓reduceDIte, Option.some.injEq, reduceCtorEq, false_iff]
            exact fun h ↦ hb ⟨⟨a, ha⟩, h⟩
        · by_cases hb : b ∈ Set.range (f : s → β)
          · simp only [ha, hb, ↓reduceDIte, Option.some.injEq, reduceCtorEq, iff_false]
            exact fun h ↦ ha (h ▸ Subtype.coe_prop _)
          · simp [ha, hb] }

/-- `PEquiv.ofEmbedding` is defined exactly on the source set, where it agrees with the
embedding. -/
@[simp] theorem PEquiv.mem_ofEmbedding_iff {α β : Type*} {s : Set α} (f : s ↪ β) {a : α}
    {b : β} : b ∈ PEquiv.ofEmbedding f a ↔ ∃ h : a ∈ s, f ⟨a, h⟩ = b := by
  classical
  show PEquiv.ofEmbedding f a = some b ↔ _
  by_cases ha : a ∈ s <;> simp [PEquiv.ofEmbedding, ha]

@[simp] theorem PEquiv.ofEmbedding_isSome_iff {α β : Type*} {s : Set α} (f : s ↪ β)
    (a : α) : (PEquiv.ofEmbedding f a).isSome ↔ a ∈ s := by
  simp only [Option.isSome_iff_exists, ← Option.mem_def, PEquiv.mem_ofEmbedding_iff]
  exact ⟨fun ⟨_, h, _⟩ ↦ h, fun h ↦ ⟨f ⟨a, h⟩, h, rfl⟩⟩

@[simp] theorem PEquiv.ofEmbedding_symm_isSome_iff {α β : Type*} {s : Set α} (f : s ↪ β)
    (b : β) : ((PEquiv.ofEmbedding f).symm b).isSome ↔ b ∈ Set.range f := by
  simp only [Option.isSome_iff_exists, ← Option.mem_def, PEquiv.mem_iff_mem,
    PEquiv.mem_ofEmbedding_iff]
  exact ⟨fun ⟨_, h, heq⟩ ↦ ⟨_, heq⟩, fun ⟨x, hx⟩ ↦ ⟨x, x.2, by simpa using hx⟩⟩
