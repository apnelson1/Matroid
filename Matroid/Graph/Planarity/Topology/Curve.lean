import Mathlib.Analysis.InnerProductSpace.PiL2 -- inefficient import
import Mathlib.Topology.UniformSpace.Path
import Mathlib.Topology.Separation.Connected
import Matroid.ForMathlib.List
import Mathlib.Analysis.Complex.Circle
import Mathlib.Topology.MetricSpace.Basic

universe u
variable {α β : Type u} [TopologicalSpace α] {a b c u v w x y z : α} {C L : List α} {X Y : Set α}

open Set Function TopologicalSpace Topology Metric Nat unitInterval

structure Curve (α) [TopologicalSpace α] (x y : α) extends Path x y where
  toFun_inj : Injective toFun

structure JordanCurve (α) [TopologicalSpace α] extends C(Circle, α) where
  toFun_inj : Injective toFun

structure JordanDecomposition [MetricSpace α] (γ : JordanCurve α) where
  interior : Set α
  exterior : Set α
  partition : range γ.toFun ∪ interior ∪ exterior = univ
  interior_isConnected : IsConnected interior
  exterior_isConnected : IsConnected exterior
  interior_isOpen : IsOpen interior
  exterior_isOpen : IsOpen exterior
  frontier_interior : frontier interior = range γ.toFun
  frontier_exterior : frontier exterior = range γ.toFun

def HasJordan (α) [MetricSpace α] : Prop := ∀ γ : JordanCurve α, Nonempty (JordanDecomposition γ)

lemma foo (γ : JordanCurve α) (hu : u ∈ range γ.toFun) (hv : v ∈ range γ.toFun) (P : Curve α u v)
    (hP : range P.toFun ∩ range γ.toFun = {u, v}) :
    ∃ S₁ S₂ S₃, S₁ ∪ S₂ ∪ S₃ ∪ range γ.toFun ∪ range P.toFun = univ ∧
    IsOpen S₁ ∧ IsOpen S₂ ∧ IsOpen S₃ ∧ IsConnected S₁ ∧ IsConnected S₂ ∧ IsConnected S₃ ∧
    
