module

public import Matroid.Modular.Flat
public import Matroid.Axioms.Flat

@[expose] public section

variable {α ι : Type*} {M N : Matroid α} {X Y C F F' F₀ F₁ T : Set α} {e f g : α}

set_option linter.style.longLine false

open Set

namespace Matroid

@[pp_nodot]
structure SumFlat (M N : Matroid α) (F : Set α) : Prop where
  isFlat_left : M.IsFlat (F ∩ M.E)
  isFlat_right : N.IsFlat (F ∩ N.E)
  subset_union : F ⊆ M.E ∪ N.E

structure SumFlat' (M N : Matroid α) (F₀ F₁ F : Set α) : Prop where
  isFlat_left : M.IsFlat F₀
  isFlat_right : N.IsFlat F₁
  inter_left : F ∩ M.E = F₀
  inter_right : F ∩ N.E = F₁
  union_eq : F₀ ∪ F₁ = F

lemma sumFlat'_of_subset_subset (hF₀ : M.IsFlat F₀) (hF₁ : N.IsFlat F₁) (h₀ : F₀ ∩ N.E ⊆ F₁)
    (h₁ : F₁ ∩ M.E ⊆ F₀) : SumFlat' M N F₀ F₁ (F₀ ∪ F₁) := by
  refine ⟨hF₀, hF₁, ?_, ?_, rfl⟩
  · rwa [union_inter_distrib_right, inter_eq_self_of_subset_left hF₀.subset_ground, union_eq_left]
  rwa [union_inter_distrib_right, inter_eq_self_of_subset_left hF₁.subset_ground, union_eq_right]

lemma sumFlat'_ground_ground (M N : Matroid α) : SumFlat' M N M.E N.E (M.E ∪ N.E) := by
  apply sumFlat'_of_subset_subset ?_ ?_ ?_ ?_ <;> simp

structure IsSummablePair (M N : Matroid α) (T : Set α) : Prop where
  inter_eq : M.E ∩ N.E = T
  restrict_eq_restrict : M ↾ T = N ↾ T
  isModularFlat_left : M.IsModularFlat T

attribute [grind →] IsSummablePair.inter_eq

lemma IsSummablePair.closure_inter_right (h : IsSummablePair M N T) (X : Set α) :
    M.closure X ∩ N.E = M.closure X ∩ T := by
  grind

lemma IsSummablePair.closure_inter_left (h : IsSummablePair M N T) (X : Set α) :
    N.closure X ∩ M.E = N.closure X ∩ T := by
  grind

lemma IsSummablePair.closure_union_closure_right (h : IsSummablePair M N T) :
    M.closure (X ∪ N.closure X) = M.closure (X ∪ (N.closure X ∩ T)) := by
  rw [← closure_inter_ground, union_inter_distrib_right, h.closure_inter_left,
    closure_union_congr_left (M.closure_inter_ground ..)]

lemma IsSummablePair.closure_union_closure_left (h : IsSummablePair M N T) :
    N.closure (X ∪ M.closure X) = N.closure (X ∪ (M.closure X ∩ T)) := by
  rw [← closure_inter_ground, union_inter_distrib_right, h.closure_inter_right,
    closure_union_congr_left (N.closure_inter_ground ..)]

lemma IsSummablePair.closure_inter_eq_closure (h : IsSummablePair M N T) (hX : X ⊆ T) :
    N.closure X ∩ T = M.closure X := by
  rw [← N.restrict_closure_eq hX (by grind), ← h.restrict_eq_restrict,
    M.restrict_closure_eq hX (by grind),
    inter_eq_self_of_subset_left (h.isModularFlat_left.isFlat.closure_subset_of_subset hX)]

lemma IsSummablePair.closure_subset_closure (h : IsSummablePair M N T) (hX : X ⊆ N.E) :
    M.closure X ⊆ N.closure X := by
  wlog hXT : X ⊆ T generalizing X with aux
  · grw [← closure_inter_ground, aux (by grind) (by grind), inter_subset_left]
  grw [← h.closure_inter_eq_closure hXT, inter_subset_left]

lemma IsSummablePair.closure_union_inter_subset_closure (h : IsSummablePair M N T) (hY : Y ⊆ N.E) :
    M.closure (X ∪ Y) ∩ T ⊆ N.closure ((M.closure X ∩ T) ∪ Y) := by
  grw [← M.closure_union_closure_left_eq, inter_comm,
    ← M.closure_union_congr_right (M.closure_inter_ground ..),
    h.isModularFlat_left.distrib_of_subset_self
    (M.closure_isFlat ..) (by grind), h.closure_subset_closure (by grind),
    inter_subset_left (t := M.E), inter_comm]

lemma IsSummablePair.isFlat_left_closure_right_inter (h : IsSummablePair M N T) (X : Set α) :
    M.IsFlat (N.closure X ∩ M.E) := by
  suffices aux : (M ↾ T).IsFlat (N.closure X ∩ M.E) by
    replace aux := aux.closure
    rwa [restrict_closure_eq _ (by grind) (by grind), inter_eq_self_of_subset_left,
      ← isFlat_iff_closure_eq] at aux
    rw [← h.isModularFlat_left.isFlat.closure]
    exact M.closure_subset_closure <| by grind
  grw [h.restrict_eq_restrict, h.closure_inter_left, isFlat_iff_subset_closure_self,
    restrict_closure_eq _ inter_subset_right (by grind), subset_inter_iff,
    and_iff_left inter_subset_right, inter_subset_left, inter_subset_left, closure_closure]

lemma IsSummablePair.closure_union_inter_subset (h : IsSummablePair M N T) (X : Set α) :
    M.closure (X ∪ N.closure X) ∩ T ⊆ N.closure (X ∪ M.closure X) := by
  grw [← M.closure_union_congr_right (M.closure_inter_ground ..),
    h.closure_union_inter_subset_closure (by grind), union_comm,
    inter_subset_left, N.closure_union_closure_left_eq, inter_subset_left]

def biclosure (M N : Matroid α) (X : Set α) : Set α :=
  M.closure (X ∪ N.closure (X ∪ M.closure X)) ∪ N.closure (X ∪ M.closure X)

lemma biclosure_subset_biclosure (M N : Matroid α) (hXY : X ⊆ Y) :
    biclosure M N X ⊆ biclosure M N Y := by
  grw [biclosure, hXY, ← biclosure]

lemma subset_biclosure (M N : Matroid α) (hX : X ⊆ M.E ∪ N.E) : X ⊆ biclosure M N X := by
  nth_grw 1 [biclosure, ← inter_eq_self_of_subset_left hX, inter_union_distrib_left]
  apply union_subset_union <;>
  grw [← subset_union_left, inter_ground_subset_closure]

lemma biclosure_subset_union_ground (M N : Matroid α) (X : Set α) :
    biclosure M N X ⊆ M.E ∪ N.E :=
  union_subset_union (closure_subset_ground ..) (closure_subset_ground ..)

lemma biclosure_inter_union_ground (M N : Matroid α) (X : Set α) :
    biclosure M N (X ∩ (M.E ∪ N.E)) = biclosure M N X := by
  rw [biclosure, biclosure]
  convert rfl using 2
  · rw [eq_comm, ← M.closure_inter_ground, union_inter_distrib_right,
      ← M.closure_inter_ground (X ∩ _), inter_assoc, inter_eq_self_of_subset_right
      subset_union_left, ← N.closure_inter_ground, union_inter_distrib_right,
      inter_assoc, inter_eq_self_of_subset_right subset_union_right,
      ← union_inter_distrib_right, ← union_inter_distrib_right, closure_inter_ground,
      closure_inter_ground, closure_inter_ground]
  rw [eq_comm, ← N.closure_inter_ground, union_inter_distrib_right, inter_assoc,
    inter_eq_self_of_subset_right subset_union_right, ← union_inter_distrib_right,
    closure_inter_ground, ← M.closure_inter_ground, inter_assoc,
    inter_eq_self_of_subset_right subset_union_left, closure_inter_ground]

lemma biclosure_inter_inter_ground (M N : Matroid α) (X : Set α) :
    biclosure M N (X ∩ (M.E ∪ N.E)) ∩ (M.E ∪ N.E) = biclosure M N X := by
  grw [biclosure_inter_union_ground, inter_eq_left, biclosure_subset_union_ground ..]

lemma IsSummablePair.biclosure_inter_right_eq (h : IsSummablePair M N T) (X : Set α) :
    (biclosure M N X) ∩ N.E = N.closure (X ∪ M.closure X) := by
  nth_grw 1 [biclosure, union_inter_distrib_right,
    inter_eq_self_of_subset_left (N.closure_subset_ground ..), union_eq_right,
    h.closure_inter_right, subset_union_left (s := X) (t := M.closure X),
    h.closure_union_inter_subset, union_assoc,
    union_eq_self_of_subset_left (M.closure_subset_closure subset_union_left),
    Matroid.closure_union_closure_right_eq, union_self]

lemma biclosure_inter_left_eq (M N : Matroid α) (X : Set α) :
    (biclosure M N X) ∩ M.E = M.closure (X ∪ N.closure (X ∪ M.closure X)) := by
  grw [biclosure, union_inter_distrib_right,
    inter_eq_self_of_subset_left (M.closure_subset_ground _), union_eq_left,
    M.inter_ground_subset_closure, ← subset_union_right (s := X) (t := N.closure _)]

lemma closure_biclosure_left (X : Set α) : M.closure (biclosure M N X) = biclosure M N X ∩ M.E := by
  refine (M.inter_ground_subset_closure _).antisymm' ?_
  rw [biclosure_inter_left_eq, ← M.closure_inter_ground]
  refine M.closure_subset_closure_of_subset_closure <| ?_
  grw [biclosure, union_inter_distrib_right, union_subset_iff, and_iff_right inter_subset_left,
    M.inter_ground_subset_closure, ← subset_union_right (s := X) (t := N.closure _)]

lemma IsSummablePair.closure_biclosure_right (h : IsSummablePair M N T) (X : Set α) :
    N.closure (biclosure M N X) = biclosure M N X ∩ N.E := by
  refine (N.inter_ground_subset_closure _).antisymm' ?_
  rw [h.biclosure_inter_right_eq, ← N.closure_inter_ground]
  exact N.closure_subset_closure_of_subset_closure <| by rw [h.biclosure_inter_right_eq]

lemma IsSummablePair.biclosure_biclosure (h : IsSummablePair M N T) (X : Set α) :
    biclosure M N (biclosure M N X) = biclosure M N X := by
  refine (subset_biclosure _ _ (biclosure_subset_union_ground ..)).antisymm' ?_
  grw [biclosure, closure_biclosure_left, union_eq_self_of_subset_right inter_subset_left,
    h.closure_biclosure_right, union_eq_self_of_subset_right inter_subset_left,
    closure_biclosure_left, ← inter_union_distrib_left, inter_subset_left]

-- (closure_exchange : ∀ ⦃X e f⦄, X ⊆ E → e ∈ E → f ∈ E →
--       f ∈ closure (insert e X) \ closure X → e ∈ closure (insert f X) \ X)

lemma IsSummablePair.biclosure_biclosure_insert (h : IsSummablePair M N T) (X : Set α) (e : α) :
    M.biclosure N (insert e (M.biclosure N X)) = M.biclosure N (insert e X) := by
  by_cases! he : e ∉ M.E ∪ N.E
  · rw [← biclosure_inter_inter_ground, insert_inter_of_notMem he, biclosure_inter_inter_ground,
      h.biclosure_biclosure, eq_comm, ← biclosure_inter_union_ground, insert_inter_of_notMem he,
      biclosure_inter_union_ground]
  wlog hX : X ⊆ M.E ∪ N.E generalizing X with aux
  · grw [← biclosure_inter_union_ground _ _ X, aux _ inter_subset_right, ← insert_inter_of_mem he,
      biclosure_inter_union_ground]
  refine subset_antisymm ?_ <| biclosure_subset_biclosure _ _ <| insert_subset_insert <|
    subset_biclosure _ _ hX
  nth_rw 3 [← h.biclosure_biclosure]
  refine biclosure_subset_biclosure _ _ <| insert_subset ?_ <| biclosure_subset_biclosure _ _
    <| subset_insert ..
  grw [← subset_biclosure _ _ (insert_subset he hX)]
  exact mem_insert ..

-- FALSE
lemma IsSummablePair.closure_inter_biclosure_left (h : IsSummablePair M N T) (hX : X ⊆ M.E ∪ N.E)
    (he : e ∈ M.E) : M.closure (insert e (M.biclosure N X)) = biclosure M N (insert e X) ∩ M.E := by
  sorry
  -- refine subset_antisymm ?_ ?_
  -- · grw [← h.biclosure_biclosure_insert hX (.inl he), biclosure_inter_left_eq, ← subset_union_left]
  -- rw [← M.closure_inter_ground, insert_inter_of_mem he, biclosure_inter_left_eq,
  --   biclosure_inter_left_eq, closure_insert_closure_eq_closure_insert,
  --   insert_union (t := M.closure _), ← union_insert,
  --   insert_eq_of_mem (M.mem_closure_of_mem' (mem_insert ..) he)]
  -- obtain heq | hssu :=
  --   (inter_subset_inter_left N.E (M.closure_subset_closure (subset_insert e X))).eq_or_ssubset
  -- · rw [← closure_union_congr_right (N.closure_inter_ground ..),
  --     ← heq, closure_union_congr_right (N.closure_inter_ground ..), insert_union]
  -- obtain ⟨f, ⟨hfeX, hfN⟩, hfX⟩ := exists_of_ssubset hssu
  -- rw [mem_inter_iff, and_iff_left hfN] at hfX

  -- have aux : Disjoint X M.E := sorry
  -- rw [← closure_inter_ground, union_inter_distrib_right, ← M.closure_inter_ground (insert e X),
  --   ← M.closure_inter_ground X, insert_inter_of_mem he, aux.inter_eq]
  -- simp
  -- have hss2 : M.closure (N.closure (insert f (X ∪ M.closure X))) ⊆
  --     M.closure (insert f (N.closure (X ∪ M.closure X))) := by
  --   rw [← M.closure_inter_ground]
  --   refine closure_subset_closure_of_subset_closure ?_
  --   rw [← N.closure_insert_closure_eq_closure_insert]
  --   sorry
  -- sorry

-- FALSE - take `X = ∅`, and `e` to be a point of `M.E \ N.E` parallel to a point of `N`.
lemma IsSummablePair.closure_inter_biclosure_right (h : IsSummablePair M N T) (hX : X ⊆ M.E ∪ N.E)
    (he : e ∈ M.E ∪ N.E) :

    N.closure (insert e (M.biclosure N X)) = biclosure M N (insert e X) ∩ N.E := by
  refine subset_antisymm ?_ ?_
  · grw [← h.biclosure_biclosure_insert, h.biclosure_inter_right_eq, ← subset_union_left]
  rw [h.biclosure_inter_right_eq, ← N.closure_inter_ground,
    closure_subset_closure_iff_subset_closure, union_inter_distrib_right, union_subset_iff]
  refine ⟨?_, ?_⟩
  · refine subset_closure_of_subset' _ ?_ inter_subset_right
    by_cases heN : e ∈ N.E
    · grw [insert_inter_of_mem heN, inter_subset_left, ← subset_biclosure M N hX]
    grw [insert_inter_of_notMem heN, ← subset_insert, inter_subset_left, ← subset_biclosure _ _ hX]
  by_cases! heM : e ∉ M.E
  · grw [← closure_inter_ground, insert_inter_of_notMem heM, closure_inter_ground,
      ← subset_insert, inter_ground_subset_closure, biclosure, ← subset_union_left,
        ← subset_union_left]
  grw [biclosure, ← subset_union_left, inter_ground_subset_closure, ← subset_union_left]
  sorry

  -- grw [← N.closure_union_closure_right_eq, hss, N.closure_union_closure_right_eq, union_insert,
  --   ← M.closure_union_closure_right_eq, hss2, M.closure_union_closure_right_eq]
    -- rw [h.clo]


  -- rw [← closure_insert_congr ⟨hfeX, hfX⟩, closure_union_congr_right (N.closure_inter_ground ..)]
  -- have := (M.closure_exchange ⟨hfeX, hfX⟩).1
  -- grw [biclosure_inter_left_eq]
  -- rw [← closure_biclosure_left]
  -- rw [← inter_eq_self_of_subset_left (M.closure_subset_ground ..)]

lemma IsSummablePair.closure_exchange (h : IsSummablePair M N T) (hX : X ⊆ M.E ∪ N.E)
    (he : e ∈ M.E ∪ N.E) (hf : f ∈ M.E ∪ N.E) (hfX : f ∉ M.biclosure N X)
    (hfeX : f ∈ M.biclosure N (insert e X)) : e ∈ M.biclosure N (insert f X) := by
  -- have hss : N.closure (M.closure (insert e X)) ⊆ N.closure (insert f (M.closure X)) := by
  --   grw [← closure_insert_congr ⟨hfeX, hfX⟩, ← N.closure_inter_ground,
  --     closure_subset_closure_iff_subset_closure, h.closure_inter_right, ← union_singleton,
  --     h.closure_union_inter_subset_closure (by simpa), ← union_singleton, inter_subset_left]
  -- rw [← h.biclosure_biclosure_insert]
  obtain hfE | hfE := hf
  ·
    have h1 := mem_inter hfeX hfE
    rw [biclosure_inter_left_eq] at h1
    by_cases! heM : e ∉ M.E
    ·
      grw [biclosure, ← subset_union_right]


    -- have := h.cl


    -- have hss1 := inter_subset_inter_left N.E <| M.closure_subset_closure (subset_insert e X)
    -- by_cases! heM : e ∉ M.E
    -- · rw [← M.closure_union_congr_left (M.closure_inter_ground ..),
    --     ← M.closure_inter_ground (insert ..), insert_inter_of_notMem heM, M.closure_inter_ground,
    --     M.closure_union_congr_left (M.closure_inter_ground ..)] at h1
    --   nth_grw 1 [biclosure, ← subset_union_right, ← subset_union_left]
    --   have hss : N.closure (M.closure (insert e X)) ⊆ M.closure (insert e (N.closure X)) := by
    --     sorry
    --   grw [← N.closure_union_closure_left_eq] at h1
    -- obtain heq | hssu := hss1.eq_or_ssubset
    -- · rw [← N.closure_union_congr_right (N.closure_inter_ground ..), ← heq,
    --     N.closure_union_congr_right (N.closure_inter_ground ..)] at h1
  --   rw [biclosure_inter_left_eq] at h1
  --   have hins : f ∈ M.closure (insert e (M.biclosure N X)) := by
  --     _

  -- -- suffices hcl' : f ∈ M.closure (insert e (M.biclosure N X))
  -- -- ·
  -- --   refine mem_of_mem_of_subset (M.closure_exchange ⟨hcl', by grind [closure_biclosure_left]⟩).1 ?_
  -- --     grw [← inter_subset_left (s := M.biclosure N (insert f X)) (t := M.E),
  -- --       ← closure_inter_ground, insert_inter_of_mem hfE, biclosure_inter_left_eq,
  -- --       closure_insert_closure_eq_closure_insert, biclosure_inter_left_eq]
  -- --     exact M.closure_subset_closure <| insert_subset (by grind) <| by grw [← subset_insert]
  -- by_cases! hfE : f ∉ N.E
  -- · have hi := mem_inter hfeX (show f ∈ M.E by grind)
  --   rw [biclosure_inter_left_eq] at hi
  --   by_cases! heE : e ∉ N.E
  --   · rw [← N.closure_inter_ground, union_inter_distrib_right, insert_inter_of_notMem heE,
  --       ← union_inter_distrib_right, N.closure_inter_ground] at hi
  --     have hins : f ∈ M.closure (insert e (M.biclosure N X)) := by
  --       refine mem_of_mem_of_subset hi ?_
  --       grw [biclosure, ← subset_union_left (s := M.closure _),
  --         closure_insert_closure_eq_closure_insert]
  --     refine mem_of_mem_of_subset (M.closure_exchange ⟨hins, by grind [closure_biclosure_left]⟩).1 ?_
  --     grw [← inter_subset_left (s := M.biclosure N (insert f X)) (t := M.E),
  --       ← closure_inter_ground, insert_inter_of_mem (by grind), biclosure_inter_left_eq,
  --       closure_insert_closure_eq_closure_insert, biclosure_inter_left_eq]
  --     exact M.closure_subset_closure <| insert_subset (by grind) <| by grw [← subset_insert]
  --   rw [← h.biclosure_inter_right_eq] at hi
  --     -- have := (M.closure_exchange ⟨hins, ?_⟩).1
  --     -- rw [← closure_inter_ground, insert_inter_of_mem (by grind), biclosure_inter_left_eq] at this ⊢
  --     -- refine mem_of_mem_of_subset ?_ subset_union_left





  --   -- have hcl := (M.biclosure_inter_left_eq N (insert e X)).subset ⟨hfeX, hfE⟩
  --   suffices hcl' : f ∈ M.closure (insert e (M.biclosure N X))
  --   · refine mem_of_mem_of_subset (M.closure_exchange ⟨hcl', by grind [closure_biclosure_left]⟩).1 ?_
  --     grw [← inter_subset_left (s := M.biclosure N (insert f X)) (t := M.E),
  --       ← closure_inter_ground, insert_inter_of_mem hfE, biclosure_inter_left_eq,
  --       closure_insert_closure_eq_closure_insert, biclosure_inter_left_eq]
  --     exact M.closure_subset_closure <| insert_subset (by grind) <| by grw [← subset_insert]
  --   -- refine mem_of_mem_of_subset (mem_inter hfeX hfE) ?_
  --   -- rw [biclosure_inter_left_eq]
  --   by_cases! heE : e ∉ M.E
  --   · have hcon := mem_inter hfeX hfE
  --     rw [biclosure_inter_left_eq, ← M.closure_inter_ground, union_inter_distrib_right,
  --       ← M.closure_inter_ground (insert ..), insert_inter_of_notMem heE,
  --       M.closure_inter_ground, ← union_inter_distrib_right, M.closure_inter_ground] at hcon
  --     rw [← closure_inter_ground, insert_inter_of_notMem heE, biclosure_inter_left_eq,
  --       closure_closure]

  --   sorry

  --   rw [← closure_inter_ground, union_inter_distrib_right, ← M.closure_inter_ground (insert e X),
  --     insert_inter_of_notMem heE, closure_inter_ground, ← M.closure_inter_ground (insert e _),
  --     insert_inter_of_notMem heE]
  --   by_cases heE : e ∈ M.E
  --   · refine mem_of_mem_of_subset (mem_inter hfeX hfE) ?_
  --     rw [biclosure_inter_left_eq, ← M.closure_inter_ground (insert e (M.biclosure N _)),
  --       insert_inter_of_mem heE, biclosure_inter_left_eq, closure_insert_closure_eq_closure_insert,
  --       insert_union (t := M.closure (insert e X)), ← union_insert,
  --       insert_eq_of_mem (M.mem_closure_of_mem' (mem_insert ..) heE),]
  --     sorry
  --   rw [← closure_inter_ground, insert_inter_of_notMem heE]
  --   refine mem_of_mem_of_subset (mem_inter hfeX hfE) ?_

  --   obtain heE | heE := he
  --   · refine mem_of_mem_of_subset (mem_inter hfeX hfE) ?_
  --     rw [biclosure_inter_left_eq, ← M.closure_inter_ground (insert e (M.biclosure N _)),
  --       insert_inter_of_mem heE, biclosure_inter_left_eq, closure_insert_closure_eq_closure_insert,
  --       insert_union (t := M.closure (insert e X)), ← union_insert,
  --       insert_eq_of_mem (M.mem_closure_of_mem' (mem_insert ..) heE)]
  -- sorry



    --   have aux : (N.closure (insert e X ∪ M.closure (insert e X))) ∩ M.E ⊆
    --       M.closure (insert e (N.closure (X ∪ M.closure X))) := by
    --     rw [← M.closure_insert_closure_eq_closure_insert (X := N.closure (X ∪ M.closure X))]
    --   refine M.closure_subset_closure_of_subset_closure ?_
    --   -- refine closure_subset_closure_of_subset_closure <| union_subset ?_ ?_
    --   -- · grw [inter_ground_subset_closure, ← ]

    --   -- grw [← closure_inter_ground, insert_inter_of_mem heE, biclosure_inter_left_eq,
    --   --   closure_insert_closure_eq_closure_insert]

    -- refine mem_of_mem_of_subset (mem_inter hfeX hfE) ?_
    -- grw [biclosure_inter_left_eq, ← closure_inter_ground, union_inter_distrib_right]
    -- refine M.closure_subset_closure_of_subset_closure <| union_subset ?_ ?_
    -- · grw [inter_ground_subset_closure, ← subset_biclosure _ _ hX]
    -- grw [inter_ground_subset_closure]
    -- sorry

    -- grw [← closure_insert_closure_eq_closure_insert, closure_biclosure_left,
    --   biclosure_inter_left_eq, closure_insert_closure_eq_closure_insert,
    --   ← insert_inter_of_mem hfE, closure_inter_ground,
    --   ← inter_subset_left (s := M.biclosure N (insert f X)) (t := M.E),
    --   biclosure_inter_left_eq]
    -- refine closure_subset_closure_of_subset_closure ?_








-- structure IsFlatPair (M N : Matroid α) (F₀ F₁ : Set α) where
--   isFlat_left : M.IsFlat F₀
--   isFlat_right : N.IsFlat F₁
--   subset_right : F₀ ∩ N.E ⊆ F₁
--   subset_left : F₁ ∩ M.E ⊆ F₀

-- lemma IsFlatPair.symm (h : IsFlatPair M N F₀ F₁) : IsFlatPair N M F₁ F₀ :=
--   ⟨h.isFlat_right, h.isFlat_left, h.subset_left, h.subset_right⟩

-- @[grind →]
-- lemma IsFlatPair.subset_ground_left (h : IsFlatPair M N F₀ F₁) : F₀ ⊆ M.E :=
--   h.isFlat_left.subset_ground

-- @[grind →]
-- lemma IsFlatPair.subset_ground_right (h : IsFlatPair M N F₀ F₁) : F₁ ⊆ N.E :=
--   h.isFlat_right.subset_ground

-- lemma IsFlatPair.union_inter_ground_left (h : IsFlatPair M N F₀ F₁) : (F₀ ∪ F₁) ∩ M.E = F₀ := by
--   rw [union_inter_distrib_right, inter_eq_self_of_subset_left h.subset_ground_left,
--     union_eq_self_of_subset_right h.subset_left]

-- lemma IsFlatPair.union_inter_ground_right (h : IsFlatPair M N F₀ F₁) : (F₀ ∪ F₁) ∩ N.E = F₁ := by
--   rw [union_inter_distrib_right, inter_eq_self_of_subset_left h.subset_ground_right,
--     union_eq_self_of_subset_left h.subset_right]

-- attribute [grind →] IsFlatPair.isFlat_left IsFlatPair.isFlat_right

-- lemma IsSummablePair.isFlatPair (h : IsSummablePair M N T) (hF₀ : M.IsFlat F₀) (X : Set α) :
--     IsFlatPair M N (M.closure (F₀ ∪ N.closure (F₀ ∪ X))) (N.closure (F₀ ∪ X)) := by
--   refine ⟨by simp, by simp, ?_, ?_⟩
--   · grw [h.closure_inter_right, ← closure_inter_ground, union_inter_distrib_right,
--       inter_eq_self_of_subset_left hF₀.subset_ground, h.closure_inter_left, inter_comm,
--       h.isModularFlat_left.distrib_of_subset_self hF₀ (Y := N.closure (F₀ ∪ X) ∩ T)
--       inter_subset_right, h.closure_subset_closure (by grind)]
--     refine N.closure_subset_closure_of_subset_closure <| union_subset ?_ inter_subset_left
--     exact subset_closure_of_subset' _ (by grind) (by grind)
--   grw [← subset_union_right (t := N.closure (F₀ ∪ X)),
--     ← M.subset_closure_of_subset' inter_subset_left inter_subset_right]

-- def IsSumFlat (M N : Matroid α) (F : Set α) : Prop :=
--   ∃ F₀ F₁, IsFlatPair M N F₀ F₁ ∧ F₀ ∪ F₁ = F

-- lemma IsSumFlat.symm (h : IsSumFlat M N F) : IsSumFlat N M F := by
--   obtain ⟨F₀, F₁, h, rfl⟩ := h
--   exact ⟨F₁, F₀, h.symm, union_comm ..⟩

-- lemma IsFlatPair.isSumFlat_union (h : IsFlatPair M N F₀ F₁) : IsSumFlat M N (F₀ ∪ F₁) :=
--   ⟨_, _, h, rfl⟩

-- -- /-- If `F` is a sum flat containing the flat `F₀` on the LHS and the set `X` on the RHS,
-- -- then it must contain a bunch of other stuff. -/
-- -- lemma IsSumFlat.subset_of_subset_subset (h : M.IsSumFlat N F) (hF₀ : M.IsFlat F₀) (hF₀F : F₀ ⊆ F)
-- --     (hX : X ⊆ N.E) (hXF : X ⊆ F) :
-- --     M.closure (F₀ ∪ N.closure (F₀ ∪ X)) ∪ N.closure (F₀ ∪ X) ⊆ F := by
-- --   obtain ⟨K₀, K₁, hK, rfl⟩ := h
-- --   have h₀ : F₀ ⊆ K₀ := by
-- --     rwa [← hK.union_inter_ground_left, subset_inter_iff, and_iff_left hF₀.subset_ground]
-- --   have hss : N.closure (F₀ ∪ X) ⊆ K₁ := by
-- --     grw [← closure_inter_ground, union_inter_distrib_right, inter_eq_self_of_subset_left hX]
-- --     refine hK.isFlat_right.closure_subset_of_subset <| union_subset ?_ ?_
-- --     · grw [h₀, ← hK.union_inter_ground_right, ← subset_union_left]
-- --     grw [← hK.union_inter_ground_right, subset_inter_iff, and_iff_left hX, hXF]
-- --   refine union_subset_union ?_ hss
-- --   nth_grw 1 [h₀, hss, ← closure_inter_ground, hK.union_inter_ground_left, hK.isFlat_left.closure]

-- -- lemma IsSumFlat.subset_of_subset_subset' (h : M.IsSumFlat N F) (hXF : X ⊆ F) (hYF : Y ⊆ F) :
-- --     M.closure (X ∪ N.closure (X ∪ Y)) ⊆ F := by
-- --   obtain ⟨K₀, K₁, hK, rfl⟩ := h
-- --   grw [← subset_union_left (s := K₀), hXF, ← closure_inter_ground, union_inter_distrib_right,
-- --     hK.union_inter_ground_left, union_eq_self_of_subset_right hYF,
-- --       ← N.closure_inter_ground, hK.union_inter_ground_right, hK.isFlat_right.closure,
-- --       ← inter_eq_self_of_subset_left hK.subset_ground_left, ← union_inter_distrib_right,
-- --       hK.union_inter_ground_left, hK.isFlat_left.closure,
-- --       inter_eq_self_of_subset_left hK.subset_ground_left]

-- lemma IsSumFlat.subset_of_subset_subset (h : M.IsSumFlat N F) (hXF : X ⊆ F) :
--     M.closure (X ∪ N.closure X) ⊆ F := by
--   obtain ⟨K₀, K₁, hK, rfl⟩ := h
--   grw [hXF, ← N.closure_inter_ground, hK.union_inter_ground_right, hK.isFlat_right.closure,
--     union_assoc, union_self, ← closure_inter_ground, hK.union_inter_ground_left,
--     hK.isFlat_left.closure, ← subset_union_left]

-- lemma foo (h : IsSummablePair M N T) (h : IsSumFlat M N F) (he : e ∈ M.E) (heF₀ : e ∉ F) :
--     ∃ (F' : Set α), e ∈ F' ∧ Minimal (fun X ↦ F ⊂ X ∧ IsSumFlat M N X) F' := by
--   obtain ⟨F₀, F₁, hF₀F₁, rfl⟩ := h

--   -- have h' := h.isFlatPair (M.closure_isFlat (insert e F₀)) F₁
--   -- rw [closure_union_closure_left_eq] at h'

--   set F₀e := M.closure (insert e F₀) with hF₀e
--   have hF₀e_flat : M.IsFlat F₀e := closure_isFlat ..
--   set F₀' := M.closure (F₀e ∪ N.closure (F₀e ∪ F₁)) with hF₀'
--   set F₁' := N.closure (F₀e ∪ F₁) with hF₁'
--   -- set F' := F₀' ∪ F₁' with hF'
--   have hFp : IsFlatPair M N F₀' F₁' := h.isFlatPair hF₀e_flat F₁
--   have heF' : e ∈ F₀' ∪ F₁' := by
--     grw [← subset_union_left, hF₀', hF₀e, ← subset_union_left, closure_closure]
--     exact M.mem_closure_of_mem' (by simp) he
--   have hssu : F₀ ∪ F₁ ⊂ F₀' ∪ F₁' := sorry
--   refine ⟨F₀' ∪ F₁', heF', minimal_iff_forall_ssubset.2 ⟨⟨hssu, hFp.isSumFlat_union⟩, ?_⟩⟩
--   rintro _ hKss ⟨hssK, K₀, K₁, hK, rfl⟩
--   have hFK₀ : F₀ ⊆ K₀ := by
--     grw [← hK.union_inter_ground_left, subset_inter_iff, and_iff_left hF₀F₁.subset_ground_left,
--       ← hssK, ← subset_union_left]

--   by_cases heK₀ : e ∈ K₀
--   · refine hKss.not_subset <| union_subset ?_ ?_
--     · grw [← hK.isSumFlat_union.subset_of_subset_subset (X := insert e (F₀ ∪ F₁)) (by grind),
--         ← subset_union_left, hF₀', ← closure_inter_ground,
--         closure_subset_closure_iff_subset_closure, union_inter_distrib_right,
--         inter_eq_self_of_subset_left (by grind), union_subset_iff, hF₀e,
--         and_iff_right (closure_subset_closure _ (by grind))]

--       -- show K₀ = M.closure (insert e K₀) by rw [insert_eq_of_mem heK₀, hK.isFlat_left.closure],
--       -- ← hK.isFlat_right.closure,
--       -- insert_union]
--     have hss₀ : F₀' ⊆ K₀ := by
--       -- rw [← hK.union_inter_ground_left, subset_inter_iff, and_iff_left (by grind), ]
--       grw [hF₀', hF₁', ← closure_inter_ground, hK.isFlat_left.closure_subset_iff_subset (by grind),
--         union_inter_distrib_right, union_subset_iff,
--         inter_eq_self_of_subset_left hF₀e_flat.subset_ground, hF₀e,
--         hK.isFlat_left.closure_subset_iff_subset (by grind), and_iff_right (by grind),
--         ← hK.union_inter_ground_left, ← insert_eq_self.2 heK₀, insert_union, ← hssK]
--     have h₀' := hK.isSumFlat_union.subset_of_subset_subset (X := insert e F₀) (by grind)
--     have h₁' := union_comm K₀ _ ▸ hK.symm.isSumFlat_union.subset_of_subset_subset
--       (X := F₁) (by grind)

--     refine (h'.trans_ssubset hKss).not_subset ?_
--     rw [hF₀', hF₁', hF₀e]

--   -- -- set F₀' := M.closure (insert e F₀) with hF₀'
--   -- -- set F' := M.closure (insert e F₀ ∪ N.closure (F₀e ∪ F₁)) ∪ N.closure (F₀e ∪ F₁) with hF'
--   -- have heF' : e ∈ F' := .inl <| M.mem_closure_of_mem' (by simp [hF₀e]) he
--   -- have hssu : F₀ ∪ F₁ ⊂ F' := by
--   --   refine (union_subset_union ?_ ?_).ssubset_of_mem_notMem heF' heF₀
--   --   · grw [hF₀', ← subset_union_left, hF₀e, ← subset_insert, hF₀F₁.isFlat_left.closure]
--   --   grw [hF₁', ← subset_union_right, hF₀F₁.isFlat_right.closure]
--   -- have := h'.isSumFlat_union
--   -- simp_rw [minimal_iff_forall_ssubset]
--   -- refine ⟨F', heF', ⟨hssu, ?_⟩, fun X hXF' ⟨hXssu, hXsf⟩ ↦ ?_⟩
--   -- · rw [hF', hF₀', hF₁']
--   -- obtain ⟨K₀, K₁, hK, rfl⟩ := hXsf
--   -- by_cases heK₀ : e ∈ K₀
--   -- · have h₀ : F₀' ⊆ K₀ := by
--   --     grw [hF₀', hK.isFlat_left.closure_subset_iff_subset (by grind), insert_subset_iff,
--   --       and_iff_right heK₀, ← hK.union_inter_ground_left, ← hF₀F₁.union_inter_ground_left,
--   --       hXssu]

--     -- have h₁ : F₁' ⊆ K₀ := by



--   -- refine ⟨_, ?_, minimal_iff_forall_ssubset.2 ⟨⟨?_, h'.isSumFlat_union⟩, ?_⟩⟩

--   -- have := hN.isModularPair.inter_closure_eq
--   -- -- have hmod := (hN _ (N.closure_isFlat (F₁ ∪ M.closure (insert e F₀)))).inter_closure_eq
--   -- rw [closure_closure] at hmod
--   -- grw [← inter_eq_self_of_subset_left (N.closure_subset_ground _), inter_assoc, inter_comm N.E,
--   --   N.subset_closure (M.E ∩ N.E), ← hmod]
--   -- have hmod' := (hN F₁ h.isFlat_right).inter_closure_eq
--   -- rw [← inter_assoc, closure_inter_ground] at hmod

--     -- have := h.subset_right

-- -- lemma foo (hM : M.IsFlat F₀) (hN : N.IsFlat F₁) (hF₀F₁ : F₁ ∩ M.E ⊆ F₀) (heM : e ∈ M.E) (heN : e ∉ N.E) (heF₀ : e ∉ F₀) :
-- --     N.closure (F₁ ∪ (M.closure (insert e F₀) ∩ N.E)) ∩ M.E ⊆ M.closure (insert e F₀)

-- -- lemma sumFlat'_iInter (M N : Matroid α) [Nonempty ι] (F₀ F₁ F : ι → Set α)
-- --     (h : ∀ i, SumFlat' M N (F₀ i) (F₁ i) (F i)) :
-- --     SumFlat' M N (⋂ i, F₀ i) (⋂ i, F₁ i) (⋂ i, F i) := by
-- --   refine ⟨IsFlat.iInter (fun i ↦ (h i).isFlat_left), IsFlat.iInter (fun i ↦ (h i).isFlat_right),
-- --     ?_, ?_, ?_⟩
-- --   · rw [iInter_inter, iInter_congr fun i ↦ (h i).inter_left]
-- --   · rw [iInter_inter, iInter_congr fun i ↦ (h i).inter_right]
-- --   obtain i : ι := Classical.ofNonempty
-- --   grw [← iInter_congr (fun i ↦ (h i).inter_left), ← iInter_congr (fun i ↦ (h i).inter_right),
-- --     ← iInter_inter, ← iInter_inter, ← inter_union_distrib_left, inter_eq_left,
-- --     iInter_subset _ i, ← (h i).union_eq]
-- --   exact union_subset_union (h i).isFlat_left.subset_ground (h i).isFlat_right.subset_ground

-- -- lemma SumFlat'.bar_left (hF : SumFlat' M N F₀ F₁ F) (heM : e ∈ M.E) (he : e ∉ N.E) (heF : e ∉ F₀) :
-- --   SumFlat M N (M.closure (insert e F₀)) (N.closure (F₁ ∪ (M.closure (insert e F₀) ∩ N.E)))

-- -- lemma sumFlat_ground (M N : Matroid α) : SumFlat M N (M.E ∪ N.E) := by
-- --   refine ⟨?_, ?_, rfl.subset⟩
-- --   · rw [inter_eq_self_of_subset_right subset_union_left]
-- --     exact M.ground_isFlat
-- --   rw [inter_eq_self_of_subset_right subset_union_right]
-- --   exact N.ground_isFlat

-- -- lemma sumFlat_iInter [Nonempty ι] (F : ι → Set α) (hFs : ∀ i, SumFlat M N (F i)) :
-- --     SumFlat M N <| (⋂ i, F i) := by
-- --   refine ⟨?_, ?_, ?_⟩
-- --   · rw [iInter_inter]
-- --     exact IsFlat.iInter fun i ↦ (hFs i).isFlat_left
-- --   · rw [iInter_inter]
-- --     exact IsFlat.iInter fun i ↦ (hFs i).isFlat_right
-- --   sorry


-- -- lemma SumFlat.inter (hF : SumFlat M N F) (hF' : SumFlat M N F') :
-- --     SumFlat M N (F ∩ F') := sorry

-- -- -- @[simp]
-- -- lemma sumFlat_closure_union_closure (hX : M.closure X ∩ N.E ⊆ N.closure Y)
-- --     (hY : N.closure Y ∩ M.E ⊆ M.closure X) : SumFlat M N (M.closure X ∪ N.closure Y) := by
-- --   refine ⟨?_, ?_, union_subset_union (closure_subset_ground ..) (closure_subset_ground ..)⟩
-- --   · rw [union_inter_distrib_right, union_eq_self_of_subset_right (by grind),
-- --       inter_eq_self_of_subset_left (M.closure_subset_ground ..)]
-- --     exact M.closure_isFlat ..
-- --   rw [union_inter_distrib_right, inter_eq_self_of_subset_left (N.closure_subset_ground ..),
-- --     union_eq_self_of_subset_left hX]
-- --   exact N.closure_isFlat ..


-- -- lemma SumFlat.bar_left (hF : SumFlat M N F) (heM : e ∈ M.E) (he : e ∉ N.E) (heF : e ∉ F) :
-- --   SumFlat M N (M.closure (insert e (F ∩ M.E)) ∪ N.closure (F ∩ N.E ∪ N.closure ((insert e (F ∩ M.E)))))

-- -- lemma SumFlat.foo_left (hF : SumFlat M N F) (heM : e ∈ M.E) (he : e ∉ N.E) (heF : e ∉ F) :
-- --     ∃ F', SumFlat M N F' ∧ e ∈ F' ∧ Minimal (fun X ↦ F ⊂ X ∧ SumFlat M N X) F' := by
-- --   have hsf : SumFlat M N
-- --       (M.closure (insert e (F ∩ M.E)) ∪ N.closure ((F ∩ M.closure (F ∩ M.E ∩ N.E)) ∩ N.E)) := by
-- --     refine sumFlat_closure_union_closure ?_ ?_
-- --   refine ⟨_, hsf,
-- --     .inl (mem_closure_of_mem' _ (mem_insert ..) he), minimal_iff_forall_ssubset.2
-- --     ⟨⟨?_, hsf⟩, ?_⟩⟩

-- --   · sorry
-- --   sorry





-- -- lemma SumFlat.foo (hF : SumFlat M N F) (he : e ∈ M.E ∪ N.E) (heF : e ∉ F) :
-- --     ∃! F', SumFlat M N F' ∧ e ∈ F' ∧ Minimal (fun X ↦ F ⊂ X ∧ SumFlat M N X) F' := by
-- --   sorry

-- --     -- rw [inter_assoc, inter_eq_self_of_subset_right subset_union_left]
-- --     -- have := IsFlat.iInter_inter_ground (M := M) (Fs := fun (F : Fs) ↦ F.1 ∩ M.E)
-- --     --   (fun F ↦ (hFs F.1 F.2).isFlat_left)
-- --     -- simp only [iInter_coe_set] at this
-- --     -- rw [biInter_inter] at this
