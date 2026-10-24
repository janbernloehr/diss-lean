import NLS.ZakharovShabat.SymmetricSignedGapMatrixCompact
import NLS.SequenceSpaces.HilbertMatrixTransposeFredholm
import NLS.ZakharovShabat.SymmetricSignedGapFredholm

/-! # The transpose-oriented signed-gap gradient matrix

The gradient matrix has Dirichlet-direction rows and gap-gradient columns.
It is the ordinary bilinear transpose of the bounded signed-gap derivative
in Dirichlet coordinates. Its coordinate series converge absolutely.
Vanishing of this transpose kernel would imply invertibility of the actual
real signed-gap derivative; kernel vanishing is an explicit hypothesis.
-/
noncomputable section
open Set Complex
namespace NLS.ZakharovShabat

/-- Row `m` is the Dirichlet dual direction, column `n` the signed-gap gradient. -/
def symmetricSignedGapGradientMatrix (φ : CoeffPair 2)
    (hφ : IsRealType (CoeffPair.toMax 2 φ)) (href : sourceSpatialReflection φ = φ) :
    Coeff 2 →L[ℂ] Coeff 2 :=
  Coeff.hilbertMatrixTranspose (symmetricSignedGapDerivativeMatrix φ hφ href)

theorem symmetricSignedGapGradientMatrix_apply (φ : CoeffPair 2)
    (hφ : IsRealType (CoeffPair.toMax 2 φ)) (href : sourceSpatialReflection φ = φ)
    (τ : Coeff 2) (m : ℤ) :
    symmetricSignedGapGradientMatrix φ hφ href τ m =
      ∑' n : ℤ, τ n * symmetricSignedGapDerivativeMatrix φ hφ href (lp.single 2 m 1) n :=
  Coeff.hilbertMatrixTranspose_apply _ _ _

theorem summable_norm_symmetricSignedGapGradientMatrix_apply (φ : CoeffPair 2)
    (hφ : IsRealType (CoeffPair.toMax 2 φ)) (href : sourceSpatialReflection φ = φ)
    (τ : Coeff 2) (m : ℤ) :
    Summable (fun n : ℤ =>
      ‖τ n * symmetricSignedGapDerivativeMatrix φ hφ href (lp.single 2 m 1) n‖) :=
  Coeff.summable_norm_hilbertMatrixTranspose_apply _ _ _

/-- The column convention is the transpose of the derivative matrix convention. -/
theorem symmetricSignedGapGradientMatrix_single (φ : CoeffPair 2)
    (hφ : IsRealType (CoeffPair.toMax 2 φ)) (href : sourceSpatialReflection φ = φ)
    (n m : ℤ) :
    symmetricSignedGapGradientMatrix φ hφ href (lp.single 2 n 1) m =
      symmetricSignedGapDerivativeMatrix φ hφ href (lp.single 2 m 1) n :=
  Coeff.hilbertMatrixTranspose_single _ _ _

/-- The homogeneous gradient-matrix equations are exact absolutely convergent series. -/
theorem symmetricSignedGapGradientMatrix_eq_zero_iff (φ : CoeffPair 2)
    (hφ : IsRealType (CoeffPair.toMax 2 φ)) (href : sourceSpatialReflection φ = φ)
    (τ : Coeff 2) :
    symmetricSignedGapGradientMatrix φ hφ href τ = 0 ↔
      ∀ m : ℤ, ∑' n : ℤ,
        τ n * symmetricSignedGapDerivativeMatrix φ hφ href (lp.single 2 m 1) n = 0 := by
  constructor
  · intro h m
    rw [← symmetricSignedGapGradientMatrix_apply, h]
    rfl
  · intro h
    ext m
    rw [symmetricSignedGapGradientMatrix_apply, h]
    rfl

/-- The transpose-kernel criterion gives the actual real derivative a bounded inverse.
The premise is the remaining kernel theorem, not a consequence of compactness alone. -/
theorem bijective_fderiv_symmetricSourceSignedGapMap_of_gradientMatrix_injective
    (a : RealCoeff 2)
    (ht : Function.Injective (symmetricSignedGapGradientMatrix
      (symmetricSourceCoefficients 2 a) (symmetricSourceCoefficients_realType a)
      (congrArg Subtype.val (symmetricRealSourceCoefficients_reflection_fixed a)))) :
    Function.Bijective
      (fderiv ℝ (symmetricSourceSignedGapMap (p := 2) (by simp) (by norm_num)) a) := by
  let φ := symmetricSourceCoefficients 2 a
  have hφ := symmetricSourceCoefficients_realType a
  have href : sourceSpatialReflection φ = φ :=
    congrArg Subtype.val (symmetricRealSourceCoefficients_reflection_fixed a)
  let e := symmetricDirichletDerivativeEquiv φ hφ href
  have hm := Coeff.bijective_of_injective_hilbertMatrixTranspose_compact_sub_smul
    (symmetricSignedGapDerivativeMatrix φ hφ href) (c := (2 : ℂ)) (by norm_num)
    (isCompactOperator_symmetricSignedGapDerivativeMatrix_sub_two_id a) ht
  have hi : Function.Injective (complexSymmetricSignedGapDerivative φ) := by
    intro x y hxy
    apply e.injective
    apply hm.1
    change complexSymmetricSignedGapDerivative φ (e.symm (e x)) =
      complexSymmetricSignedGapDerivative φ (e.symm (e y))
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hxy
  apply (bijective_fderiv_symmetricSourceSignedGapMap_iff_injective a).mpr
  intro x y hxy
  have hr := complexSymmetricSignedGapDerivative_real_restriction a
  have hx := congrArg (fun L : RealCoeff 2 →L[ℝ] Coeff 2 => L x) hr
  have hy := congrArg (fun L : RealCoeff 2 →L[ℝ] Coeff 2 => L y) hr
  change complexSymmetricSignedGapDerivative φ (RealCoeff.complexCLM 2 x) =
    RealCoeff.complexCLM 2
      (fderiv ℝ (symmetricSourceSignedGapMap (p := 2) (by simp) (by norm_num)) a x) at hx
  change complexSymmetricSignedGapDerivative φ (RealCoeff.complexCLM 2 y) =
    RealCoeff.complexCLM 2
      (fderiv ℝ (symmetricSourceSignedGapMap (p := 2) (by simp) (by norm_num)) a y) at hy
  have he := hi (hx.trans ((congrArg (RealCoeff.complexCLM 2) hxy).trans hy.symm))
  simpa only [RealCoeff.reCLM_complexCLM] using congrArg (Coeff.reCLM 2) he

/-- If every gradient-matrix kernel vanishes, the actual signed-gap map is open. -/
theorem isOpenMap_symmetricSourceSignedGapMap_of_gradientMatrix_injective
    (ht : ∀ a : RealCoeff 2, Function.Injective (symmetricSignedGapGradientMatrix
      (symmetricSourceCoefficients 2 a) (symmetricSourceCoefficients_realType a)
      (congrArg Subtype.val (symmetricRealSourceCoefficients_reflection_fixed a)))) :
    IsOpenMap (symmetricSourceSignedGapMap (p := 2) (by simp) (by norm_num)) :=
  isOpenMap_symmetricSourceSignedGapMap_of_derivative_injective
    (fun a => (bijective_fderiv_symmetricSourceSignedGapMap_of_gradientMatrix_injective a (ht a)).1)

end NLS.ZakharovShabat
