import NLS.FunctionalAnalysis.NeumannCompositionBound

/-! # Neumann inversion in an equivalent norm

Only the conjugated operator must be small. The actual inverse acts on the
original carrier. Every other equivalent norm in which the same operator is
small gives its own bound two for that very same inverse.
-/
noncomputable section
namespace NLS.FunctionalAnalysis
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- A half-contractive equation gives the bound two in its chosen equivalent norm. -/
theorem norm_equiv_solution_le_two (e : E ≃L[ℂ] G) (T : E →L[ℂ] E)
    (hT : ∀ a : E, ‖e (T a)‖ ≤ (1/2:ℝ)*‖e a‖)
    (x y : E) (he : x-T x = y) : ‖e x‖ ≤ 2*‖e y‖ := by
  have h := norm_le_norm_sub_add (e x) (e (T x))
  rw [← map_sub,he] at h
  linarith [hT x]

/-- A conjugated half-contraction has an actual two-sided inverse on the original space. -/
theorem exists_equivalentNorm_neumann_inverse (e : E ≃L[ℂ] F) (T : E →L[ℂ] E)
    (hT : ‖e.toContinuousLinearMap.comp (T.comp e.symm.toContinuousLinearMap)‖ ≤ (1/2:ℝ)) :
    ∃ K : E →L[ℂ] E, (∀ x : E, K (x-T x) = x) ∧ (∀ x : E, K x-T (K x) = x) := by
  let A := e.toContinuousLinearMap.comp (T.comp e.symm.toContinuousLinearMap)
  have hnear : ‖(ContinuousLinearMap.id ℂ F).comp
      (ContinuousLinearMap.id ℂ F-(ContinuousLinearMap.id ℂ F-A))‖ ≤ (1/2:ℝ) := by
    simpa only [sub_sub_cancel,ContinuousLinearMap.id_comp] using hT
  obtain ⟨B,hB1,hB2,_⟩ := NLS.exists_inverse_norm_le_two_mul_of_composition_near
    (ContinuousLinearMap.id ℂ F-A) (ContinuousLinearMap.id ℂ F) (ContinuousLinearMap.id ℂ F)
    (by simp) (by simp) hnear
  refine ⟨e.symm.toContinuousLinearMap.comp (B.comp e.toContinuousLinearMap), ?_, ?_⟩
  · intro x
    have hb := congrArg (fun U : F →L[ℂ] F => U (e x)) hB2
    change B (e x-A (e x)) = e x at hb
    simp only [A,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply] at hb
    change e.symm (B (e (x-T x))) = x
    rw [map_sub,hb,ContinuousLinearEquiv.symm_apply_apply]
  · intro x
    have hb := congrArg (fun U : F →L[ℂ] F => U (e x)) hB1
    change B (e x)-A (B (e x)) = e x at hb
    apply e.injective
    change e (e.symm (B (e x))-T (e.symm (B (e x)))) = e x
    rw [map_sub,ContinuousLinearEquiv.apply_symm_apply]
    exact hb

/-- The actual original-carrier inverse obtained from the verified equivalent-norm criterion. -/
def equivalentNormNeumannInverse (e : E ≃L[ℂ] F) (T : E →L[ℂ] E)
    (hT : ‖e.toContinuousLinearMap.comp (T.comp e.symm.toContinuousLinearMap)‖ ≤ (1/2:ℝ)) :
    E →L[ℂ] E := Classical.choose (exists_equivalentNorm_neumann_inverse e T hT)

theorem equivalentNormNeumannInverse_left (e : E ≃L[ℂ] F) (T : E →L[ℂ] E)
    (hT : ‖e.toContinuousLinearMap.comp (T.comp e.symm.toContinuousLinearMap)‖ ≤ (1/2:ℝ)) (x : E) :
    equivalentNormNeumannInverse e T hT (x-T x) = x :=
  (Classical.choose_spec (exists_equivalentNorm_neumann_inverse e T hT)).1 x

theorem equivalentNormNeumannInverse_right (e : E ≃L[ℂ] F) (T : E →L[ℂ] E)
    (hT : ‖e.toContinuousLinearMap.comp (T.comp e.symm.toContinuousLinearMap)‖ ≤ (1/2:ℝ)) (x : E) :
    equivalentNormNeumannInverse e T hT x-T (equivalentNormNeumannInverse e T hT x) = x :=
  (Classical.choose_spec (exists_equivalentNorm_neumann_inverse e T hT)).2 x

end NLS.FunctionalAnalysis
