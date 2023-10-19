import Matroid.Representation.Basic 

variable {α β W W' 𝔽 R : Type _} {e f x : α} {I B X Y : Set α} {M : Matroid α} [Field 𝔽] 
  [AddCommGroup W] [Module 𝔽 W] [AddCommGroup W'] [Module 𝔽 W']



structure MatrixRep (M : Matroid α) (𝔽 R : Type _) [Field 𝔽] where 
  (to_matrix : Matrix R M.E 𝔽)
  (as_rep : M.Rep 𝔽 (Matrix R Unit 𝔽))
  (compatible : ∀ e : M.E, as_rep e = Matrix.of (fun x _ ↦ to_matrix x e) )

instance {R : Type _} : Coe (M.MatrixRep 𝔽 R) (Matrix R M.E 𝔽) := ⟨MatrixRep.to_matrix⟩ 

noncomputable def Rep.to_matrixRep (v : M.Rep 𝔽 (R → 𝔽)) : MatrixRep M 𝔽 R where 
  to_matrix := Matrix.of (fun e x ↦ v ((x : M.E) : α) e)
  as_rep := v.map_equiv (Matrix.col_linearEquiv _ _)
  compatible := fun _ ↦ funext fun _ ↦ funext fun _ ↦ by simp 

noncomputable def Rep.to_matrixRep_of_base [FiniteRk M] (v : M.Rep 𝔽 W) (hB : M.Base B) : 
    MatrixRep M 𝔽 B := 
  (v.to_standard_rep' hB).to_matrixRep 
  
theorem MatrixRep.representable (A : M.MatrixRep 𝔽 R) : M.Representable 𝔽 := A.as_rep.representable      
    
noncomputable def Representable.fin_matrixRep [FiniteRk M] (hM : M.Representable 𝔽) : 
    M.MatrixRep 𝔽 (Fin M.rk) := 
  (Classical.choose hM.exists_fin_rep).to_matrixRep
