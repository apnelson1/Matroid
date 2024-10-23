
import Mathlib.Data.Set.Basic

theorem diff_subset_diff_iff_subset {α : Type*} {s t r : Set α} (hs : s ⊆ r) (ht : t ⊆ r) :
    r \ s ⊆ r \ t ↔ t ⊆ s :=
  sdiff_le_sdiff_iff_le hs ht
