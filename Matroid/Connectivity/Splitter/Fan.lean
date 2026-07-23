import Matroid.Connectivity.Fan.Cyclic
import Matroid.Connectivity.Splitter.Cretaceous
import Matroid.Connectivity.Splitter.TutteTriangle

open Set Function

namespace Matroid

variable {α β : Type*} {M : Matroid α} {N : Matroid β} {X Y C K T : Set α} {e f g x y : α}
    {b c d : Bool} {n i j : ℕ} {F : List α} {J : Bool → ZMod n → α}

lemma Simple.nonempty_isoMinor_deleteElem_of_parallel (hN : N.Simple) (hNM : N ≤i M)
    (hef : M.Parallel e f) (hne : e ≠ f) : Nonempty (N ≤i M ＼ {e}) := by
  classical
  obtain ⟨M₀, hM₀, i, -⟩ := hNM.exists_iso
  have hsi := hN.of_iso i
  wlog hefM₀ : e ∈ M₀.E → f ∈ M₀.E generalizing e f with aux
  · obtain ⟨i⟩ := aux hef.symm hne.symm (by grind)
    rw [hef.parallel'.deleteElem_eq_mapEquiv]
    exact ⟨i.trans_iso <| isoMapEquiv ..⟩
  suffices aux : M₀ ≤m M ＼ {e} ∨ M₀ ≤m M ＼ {f}
  · obtain h | h := aux
    · exact ⟨i.transIsMinor h⟩
    rw [hef.parallel'.deleteElem_eq_mapEquiv]
    exact ⟨i.isoMinor.trans (h.isoMinor.trans_iso (isoMapEquiv ..))⟩
  by_contra! hcon
  by_cases hec : M₀ ≤m M ／ {e}
  · by_cases hfN : f ∈ M₀.E
    · exact ((hN.of_iso i).loopless.isNonloop_of_mem hfN).not_isLoop <|
        (hef.isLoop_contractElem hne).of_isMinor hfN hec
    obtain ⟨rfl | rfl, hf⟩ := hec.exists_isMinor_removeElem hfN
    · refine hcon.2 <| hf.trans <| contract_delete_isMinor_delete _ <| by simpa
    rw [remove_true, contract_contract, union_singleton, hef.parallel'.symm.contract_pair_eq] at hf
    exact hcon.1 <| hf.trans <| contract_delete_isMinor_delete _ (by simpa using hne.symm)
  by_cases heE : e ∈ M₀.E
  · exact hne (hef.parallel'.of_isMinor hM₀ heE (hefM₀ heE)).eq
  simpa [hcon.1, hec] using hM₀.exists_isMinor_removeElem heE


lemma foo (hM : M.TutteConnected 3) (hN : N.TutteConnected 3) (hNM : Nonempty (N ≤i M ＼ {e}))
    (hT : M.IsTriad {e, f, g}) :
    (∃ x b, x ∈ M.E ∧ (M.remove b {x}).TutteConnected 3 ∧ Nonempty (N ≤i M.remove b {x})) ∨
    ∃ (F : List α) (b : Bool), 4 ≤ F.length ∧ M.IsFan F true c := by
  wlog hwl : (M ／ {f}).TutteConnected 3 → (M ／ {g}).TutteConnected 3 generalizing f g with aux
  · exact aux hT.swap_right (by grind)
  by_cases hconn : (M ／ {g}).TutteConnected 3
  · refine .inl ⟨g, true, hT.mem_ground₃, hconn, ?_⟩
