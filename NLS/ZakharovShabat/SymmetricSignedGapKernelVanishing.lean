import NLS.ZakharovShabat.SymmetricSignedGapKernelVariation
import NLS.ZakharovShabat.SymmetricSignedGapRealKernel
import NLS.ZakharovShabat.SourcePsiBoundarySignInterpolation

/-! # Vanishing of the actual signed-gap gradient kernel

A real kernel vector supplies an entire full-product variation with
opposite values at the actual Dirichlet and Neumann roots. Interpolation
forces its normalized root direction to vanish. Reality of the matrix
then gives complex injectivity and invertibility of the real derivative.
-/
noncomputable section
open Set Complex
namespace NLS.ZakharovShabat

/-- The actual gradient matrix has no nonzero real coefficient kernel vector. -/
theorem symmetricSignedGapGradientMatrix_real_kernel_eq_zero
    (φ : realTypeSourceSubmodule 2) (href : realSourceSpatialReflection φ = φ)
    (τ : Coeff 2) (hreal : ∀ n : ℤ, (τ n).im = 0)
    (hker : symmetricSignedGapGradientMatrix φ.val φ.property (congrArg Subtype.val href) τ = 0) :
    τ = 0 := by
  let a := sourceBoundaryDisplacement (by simp) (by norm_num) .neumann φ.val
  let h := symmetricSignedGapKernelRootDirection φ τ
  have ha : a ∈ sourcePeriodicGapRootSet (by simp) (by norm_num) φ.val := by
    intro n
    rw [show displacedRoots a n = canonicalPeriodOneBoundaryRoots
      (by simp) (by norm_num) .neumann φ.val n from
        displacedRoots_sourceBoundaryDisplacement (by simp) (by norm_num) .neumann φ.val n]
    exact canonicalPeriodOneBoundaryRoots_mem_sourcePeriodicSegment_of_realType
      (by simp) (by norm_num) .neumann φ.val φ.property n
  have hr (n : ℤ) : (displacedRoots a n).im = 0 := by
    simpa only [a, displacedRoots_sourceBoundaryDisplacement] using
      canonicalPeriodOneBoundaryRoots_im_eq_zero
        (by simp) (by norm_num) .neumann φ.val φ.property n
  have hh (n : ℤ) : (h n).im = 0 :=
    sourceBoundaryNormalizedRootDirection_im_eq_zero (by simp) (by norm_num)
      .neumann φ.val φ.property (sourceGapLevelWeightedDirection τ)
      (sourceGapLevelWeightedDirection_im_eq_zero τ hreal) n
  have hop (n : ℤ) :
      sourcePsiFullProductVariation a h (canonicalPeriodOneBoundaryRoots
        (by simp) (by norm_num) .dirichlet φ.val n) =
      -sourcePsiFullProductVariation a h (canonicalPeriodOneBoundaryRoots
        (by simp) (by norm_num) .neumann φ.val n) := by
    have hd := symmetricSignedGapKernelVariation_at_dirichletRoot φ href τ n
    have hn := symmetricSignedGapKernelVariation_at_neumannRoot φ τ n
    rw [hker] at hd
    simp only [lp.coeFn_zero, Pi.zero_apply, sub_zero] at hd
    apply mul_left_cancel₀ (by norm_num : (-1/2 : ℂ) ≠ 0)
    change symmetricSignedGapKernelVariation φ τ _ = (-1/2 : ℂ) * -_
    rw [mul_neg]
    change symmetricSignedGapKernelVariation φ τ _ = -symmetricSignedGapKernelVariation φ τ _
    rw [hd, hn, neg_neg]
  have hz : h = 0 := sourcePsiFullProductVariation_direction_zero_of_opposite_boundary_values
    (by simp) (by norm_num) φ.val φ.property a h ha hr hh hop
  have hi : Function.Injective (symmetricSignedGapKernelRootDirection φ) :=
    (sourceBoundaryNormalizedRootDirection_injective (by simp) (by norm_num)
      .neumann φ.val φ.property).comp sourceGapLevelWeightedDirection_injective
  have hzero : symmetricSignedGapKernelRootDirection φ 0 = 0 := by
    ext n
    change (2 * sourceAbelianGapSign n * (0 : ℂ)) / _ = 0
    simp
  exact hi (hz.trans hzero.symm)

/-- The actual complex gradient matrix is injective at every symmetric real Hilbert source. -/
theorem symmetricSignedGapGradientMatrix_injective (a : RealCoeff 2) :
    Function.Injective (symmetricSignedGapGradientMatrix
      (symmetricSourceCoefficients 2 a) (symmetricSourceCoefficients_realType a)
      (congrArg Subtype.val (symmetricRealSourceCoefficients_reflection_fixed a))) := by
  apply (symmetricSignedGapGradientMatrix_injective_iff_realKernelZero a).mpr
  intro τ hτ
  have hz := symmetricSignedGapGradientMatrix_real_kernel_eq_zero
    (symmetricRealSourceCoefficients 2 a) (symmetricRealSourceCoefficients_reflection_fixed a)
    (RealCoeff.complexCLM 2 τ) (fun _ => rfl) hτ
  simpa only [RealCoeff.reCLM_complexCLM, map_zero] using congrArg (Coeff.reCLM 2) hz

/-- Every actual real signed-gap derivative is bijective in the Hilbert source coordinates. -/
theorem bijective_fderiv_symmetricSourceSignedGapMap (a : RealCoeff 2) :
    Function.Bijective
      (fderiv ℝ (symmetricSourceSignedGapMap (p := 2) (by simp) (by norm_num)) a) :=
  bijective_fderiv_symmetricSourceSignedGapMap_of_gradientMatrix_injective a
    (symmetricSignedGapGradientMatrix_injective a)

/-- The actual Hilbert signed-gap map is globally open. Global injectivity is a separate step. -/
theorem isOpenMap_symmetricSourceSignedGapMap :
    IsOpenMap (symmetricSourceSignedGapMap (p := 2) (by simp) (by norm_num)) :=
  isOpenMap_symmetricSourceSignedGapMap_of_gradientMatrix_injective
    symmetricSignedGapGradientMatrix_injective

end NLS.ZakharovShabat
