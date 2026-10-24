import NLS.ZakharovShabat.SymmetricSignedGapDerivativeMatrix
import NLS.ZakharovShabat.SymmetricDirichletLocalInverse
import NLS.ZakharovShabat.SymmetricSignedGapCompactDerivative
import NLS.SequenceSpaces.CompactCoefficientComplexification
import NLS.FunctionalAnalysis.CompactInverseDerivative

/-! # Compactness of the actual signed-gap matrix in Dirichlet coordinates

The real signed-gap derivative is complexified using the actual real-form
identity. Its compact remainder therefore holds on symmetric complex
directions. The bounded Dirichlet inverse preserves that remainder, so
the actual coordinate matrix is twice identity plus a compact operator.
-/
noncomputable section
open Set Complex
namespace NLS.ZakharovShabat

def complexSymmetricSignedGapDerivative (φ : CoeffPair 2) : Coeff 2 →L[ℂ] Coeff 2 :=
  (fderiv ℂ (sourceSignedGapSequence (p := 2) (by simp) (by norm_num)) φ).comp
    (complexSymmetricSourceCoefficients 2)

/-- Restricting the complex derivative to real coordinates gives exactly the
complex inclusion of the previously constructed real derivative. -/
theorem complexSymmetricSignedGapDerivative_real_restriction (a : RealCoeff 2) :
    ((complexSymmetricSignedGapDerivative (symmetricSourceCoefficients 2 a)).restrictScalars ℝ).comp
      (RealCoeff.complexCLM 2) = (RealCoeff.complexCLM 2).comp
        (fderiv ℝ (symmetricSourceSignedGapMap (p := 2) (by simp) (by norm_num)) a) := by
  let F := sourceSignedGapSequence (p := 2) (by simp) (by norm_num)
  let G := symmetricSourceSignedGapMap (p := 2) (by simp) (by norm_num)
  let R := symmetricSourceCoefficients 2
  let C := RealCoeff.complexCLM 2
  obtain ⟨_,_,hr,hF⟩ := exists_sourceSignedGapSequence_analytic_common_domain
    (p := 2) (by simp) (by norm_num)
  have hf := (hF (R a) (hr (symmetricSourceCoefficients_realType a))).differentiableAt.hasFDerivAt
  have hg := (analyticAt_symmetricSourceSignedGapMap (p := 2) (by simp) (by norm_num) a).differentiableAt.hasFDerivAt
  have he : C ∘ G = F ∘ R := by
    funext b
    exact RealCoeff.complexCLM_reCLM 2 _ (fun n => sourceSignedGapSequence_im_eq_zero
      (by simp) (by norm_num) (symmetricRealSourceCoefficients 2 b) n)
  have hl := C.hasFDerivAt.comp a hg
  have hd := (hf.restrictScalars ℝ).comp a R.hasFDerivAt
  change HasFDerivAt (C ∘ G) _ a at hl
  rw [he] at hl
  have hderiv := hl.unique hd
  calc
    _ = ((fderiv ℂ F (R a)).restrictScalars ℝ).comp R := by
      apply ContinuousLinearMap.ext
      intro h
      change (fderiv ℂ F (R a))
        (complexSymmetricSourceCoefficients 2 (RealCoeff.complexCLM 2 h)) =
        (fderiv ℂ F (R a)) (R h)
      rw [complexSymmetricSourceCoefficients_realCoeff]
    _ = _ := hderiv.symm

/-- Twice-identity-plus-compact holds on all symmetric complex directions. -/
theorem isCompactOperator_complexSymmetricSignedGapDerivative_sub_two_id (a : RealCoeff 2) :
    IsCompactOperator (complexSymmetricSignedGapDerivative (symmetricSourceCoefficients 2 a) -
      (2 : ℂ) • (1 : Coeff 2 →L[ℂ] Coeff 2)) := by
  apply Coeff.Complexification.isCompactOperator_of_real_restriction
  have hc := (isCompactOperator_fderiv_symmetricSourceSignedGapMap_sub_two_id a).clm_comp
    (RealCoeff.complexCLM 2)
  have he : ((complexSymmetricSignedGapDerivative (symmetricSourceCoefficients 2 a) -
      (2 : ℂ) • (1 : Coeff 2 →L[ℂ] Coeff 2)).restrictScalars ℝ).comp (RealCoeff.complexCLM 2) =
      (RealCoeff.complexCLM 2).comp
        (fderiv ℝ (symmetricSourceSignedGapMap (p := 2) (by simp) (by norm_num)) a -
          (2 : ℝ) • ContinuousLinearMap.id ℝ (RealCoeff 2)) := by
    have h := complexSymmetricSignedGapDerivative_real_restriction a
    apply ContinuousLinearMap.ext
    intro v
    have hv := congrArg (fun L : RealCoeff 2 →L[ℝ] Coeff 2 => L v) h
    change complexSymmetricSignedGapDerivative (symmetricSourceCoefficients 2 a)
      (RealCoeff.complexCLM 2 v) =
      RealCoeff.complexCLM 2
        (fderiv ℝ (symmetricSourceSignedGapMap (p := 2) (by simp) (by norm_num)) a v) at hv
    change complexSymmetricSignedGapDerivative (symmetricSourceCoefficients 2 a)
      (RealCoeff.complexCLM 2 v) - (2 : ℂ) • RealCoeff.complexCLM 2 v =
      RealCoeff.complexCLM 2
        (fderiv ℝ (symmetricSourceSignedGapMap (p := 2) (by simp) (by norm_num)) a v -
          (2 : ℝ) • v)
    rw [hv]
    simp only [two_smul, map_sub, map_add]
  have hc' : IsCompactOperator ((RealCoeff.complexCLM 2).comp
      (fderiv ℝ (symmetricSourceSignedGapMap (p := 2) (by simp) (by norm_num)) a -
        (2 : ℝ) • ContinuousLinearMap.id ℝ (RealCoeff 2))) := hc
  exact he.symm ▸ hc'

/-- The actual matrix after the Dirichlet coordinate change retains its compact remainder. -/
theorem isCompactOperator_symmetricSignedGapDerivativeMatrix_sub_two_id (a : RealCoeff 2) :
    let φ := symmetricSourceCoefficients 2 a
    let hφ := symmetricSourceCoefficients_realType a
    let href := congrArg Subtype.val (symmetricRealSourceCoefficients_reflection_fixed a)
    IsCompactOperator (symmetricSignedGapDerivativeMatrix φ hφ href -
      (2 : ℂ) • (1 : Coeff 2 →L[ℂ] Coeff 2)) := by
  dsimp only
  let φ := symmetricSourceCoefficients 2 a
  have hφ := symmetricSourceCoefficients_realType a
  have href : sourceSpatialReflection φ = φ :=
    congrArg Subtype.val (symmetricRealSourceCoefficients_reflection_fixed a)
  let B := (symmetricDirichletDerivativeEquiv φ hφ href).symm.toContinuousLinearMap
  have hi : (symmetricDirichletDerivative φ).comp B = ContinuousLinearMap.id ℂ (Coeff 2) := by
    apply ContinuousLinearMap.ext
    intro x
    exact (symmetricDirichletDerivativeEquiv φ hφ href).apply_symm_apply x
  have hb := NLS.isCompactOperator_rightInverse_sub_id (symmetricDirichletDerivative φ) B
    (isCompactOperator_symmetricDirichletDerivative_sub_id φ hφ) hi
  exact NLS.isCompactOperator_comp_sub_of_compact_remainders
    (complexSymmetricSignedGapDerivative φ) ((2 : ℂ) • (1 : Coeff 2 →L[ℂ] Coeff 2)) B
    (isCompactOperator_complexSymmetricSignedGapDerivative_sub_two_id a) hb

end NLS.ZakharovShabat
