import Matroid.Graph.Constructions
import Matroid.Graph.Simple

variable {α β : Type*} {a b x y z u v w : α} {e f : β} {G H : Graph α β} {F : Set β} {X Y : Set α}

open Set

namespace Graph

/-- A graph with one vertex and loops at that vertex -/
@[simps]
def bouquet (v : α) (F : Set β) : Graph α β where
  vertexSet := {v}
  edgeSet := F
  IsLink e x y := e ∈ F ∧ x = v ∧ y = v
  isLink_symm e := by simp +contextual [Symmetric]
  eq_or_eq_of_isLink_of_isLink := by aesop
  edge_mem_iff_exists_isLink := by aesop
  left_mem_of_isLink := by aesop

@[simp]
lemma bouquet_inc_iff : (bouquet v F).Inc e x ↔ e ∈ F ∧ x = v := by
  simp [Inc]

/-- Every graph on just one vertex is a bouquet on that vertex-/
lemma eq_bouquet (hv : v ∈ V(G)) (hss : V(G).Subsingleton) : G = bouquet v E(G) := by
  have hrw := hss.eq_singleton_of_mem hv
  refine Graph.ext_inc (by simpa) fun e x ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp [bouquet_inc_iff, ← mem_singleton_iff, ← hrw, h.edge_mem, h.vertex_mem]
  simp only [bouquet_inc_iff] at h
  obtain ⟨z,w, hzw⟩ := exists_isLink_of_mem_edgeSet h.1
  rw [h.2, ← show z = v from (show z ∈ {v} from hrw ▸ hzw.left_mem)]
  exact hzw.inc_left

/-- Every graph on just one vertex is a bouquet on that vertex-/
lemma exists_eq_bouquet_edge (hv : v ∈ V(G)) (hss : V(G).Subsingleton) : ∃ F, G = bouquet v F :=
  ⟨E(G), eq_bouquet hv hss⟩

lemma exists_eq_bouquet (hne : V(G).Nonempty) (hss : V(G).Subsingleton) : ∃ x F, G = bouquet x F :=
  ⟨_, _, eq_bouquet hne.some_mem hss⟩

/-- A graph with exactly two vertices and no loops. -/
@[simps]
def banana (a b : α) (F : Set β) : Graph α β where
  vertexSet := {a,b}
  edgeSet := F
  IsLink e x y := e ∈ F ∧ ((x = a ∧ y = b) ∨ (x = b ∧ y = a))
  isLink_symm _ _ _ := by aesop
  eq_or_eq_of_isLink_of_isLink := by aesop
  edge_mem_iff_exists_isLink := by aesop
  left_mem_of_isLink := by aesop

@[simp]
lemma banana_inc_iff : (banana a b F).Inc e x ↔ e ∈ F ∧ (x = a ∨ x = b) := by
  simp only [Inc, banana_isLink, exists_and_left, and_congr_right_iff]
  aesop

lemma eq_banana [G.Loopless] (hV : V(G) = {a,b}) : G = banana a b E(G) := by
  refine Graph.ext_inc (by simpa) fun e x ↦ ?_
  simp only [banana_inc_iff]
  refine ⟨fun h ↦ ⟨h.edge_mem, by simpa using (show x ∈ {a,b} from hV ▸ h.vertex_mem)⟩, ?_⟩
  suffices aux : ∀ c, V(G) = {x,c} → e ∈ E(G) → G.Inc e x by
    rintro ⟨he, rfl | rfl⟩
    · exact aux _ hV he
    exact aux _ (pair_comm _ _ ▸ hV) he
  intro c hC he
  obtain ⟨z,w, hezw⟩ := exists_isLink_of_mem_edgeSet he
  obtain rfl | hzx := eq_or_ne z x
  · exact hezw.inc_left
  obtain rfl | hwx := eq_or_ne w x
  · exact hezw.inc_right
  have h1 := hC ▸ hezw.left_mem
  have h2 := hC ▸ hezw.right_mem
  obtain rfl : z = c := by simpa [hzx] using h1
  obtain rfl : w = z := by simpa [hwx] using h2
  exact (hezw.adj.ne rfl).elim

lemma exists_eq_banana [G.Loopless] (hV : V(G) = {a,b}) : ∃ F, G = banana a b F :=
  ⟨_, eq_banana hV⟩

lemma exists_eq_banana_of_encard [G.Loopless] (hV : V(G).encard = 2) :
    ∃ a b F, a ≠ b ∧ G = banana a b F := by
  obtain ⟨a, b, hab, hV⟩ := encard_eq_two.1 hV
  exact ⟨a, b, E(G), hab, eq_banana hV⟩
