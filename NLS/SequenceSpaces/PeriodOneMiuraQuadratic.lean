import NLS.SequenceSpaces.PeriodOneMassResolvent
import NLS.SequenceSpaces.YoungConvolution
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! # The distributional quadratic Miura term

The convolution of two L2 Fourier sequences is bounded. Multiplication
by the inverse bracket puts it in H^-1. After the massive first-order
inverse its bilinear bound is the L2 norm of the resolvent kernel,
which tends to zero. All formulas use period-one Fourier coordinates.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS

theorem youngRelation_two_two_top : YoungRelation 2 2 ⊤ := by
  simpa only [YoungRelation,ENNReal.inv_top,add_zero] using ENNReal.inv_two_add_inv_two.symm

/-- The inclusion preserves the raw Fourier coefficients of a bounded sequence. -/
def boundedCoefficientsHminusOne : Coeff ⊤ →L[ℂ] PeriodOneHminusOne :=
  (WeightedCoeff.weightIsometry (Weight.sobolev (-1)) 2).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (Coeff.holderProduct (p := 2) (r := ⊤) (q := 2) inverseBracketCoefficients)

@[simp] theorem boundedCoefficientsHminusOne_apply (b : Coeff ⊤) (k : ℤ) :
    (boundedCoefficientsHminusOne b).val k = b k := by
  change ((Weight.sobolev 1 k : ℂ)⁻¹*b k)/(Weight.sobolev (-1) k : ℂ) = _
  have he : (Weight.sobolev (-1) k : ℂ) = (Weight.sobolev 1 k : ℂ)⁻¹ := by
    simp [Weight.sobolev_apply,Real.rpow_neg_one]
  rw [he]
  exact mul_div_cancel_left₀ _ (inv_ne_zero (Weight.complex_ne_zero _ k))

/-- The actual distributional product, with its absolutely convergent coefficient sum. -/
def periodOneMiuraProduct : Coeff 2 →L[ℂ] Coeff 2 →L[ℂ] PeriodOneHminusOne :=
  (ContinuousLinearMap.compL ℂ (Coeff 2) (Coeff ⊤) PeriodOneHminusOne
    boundedCoefficientsHminusOne).comp (Coeff.youngConvolutionCLM youngRelation_two_two_top)

@[simp] theorem periodOneMiuraProduct_apply (a b : Coeff 2) (k : ℤ) :
    (periodOneMiuraProduct a b).val k = ∑' j : ℤ, a (k-j)*b j := by
  change (boundedCoefficientsHminusOne (Coeff.youngConvolution youngRelation_two_two_top a b)).val k = _
  rw [boundedCoefficientsHminusOne_apply,Coeff.youngConvolution_apply]

theorem periodOneMiuraProduct_comm (a b : Coeff 2) :
    periodOneMiuraProduct a b = periodOneMiuraProduct b a := by
  change boundedCoefficientsHminusOne (Coeff.youngConvolution youngRelation_two_two_top a b) = _
  rw [Coeff.youngConvolution_comm]
  rfl

/-- The quadratic term after the actual H^-1-to-L2 inverse. -/
def periodOneResolvedProduct (m : ℕ) : Coeff 2 →L[ℂ] Coeff 2 →L[ℂ] Coeff 2 :=
  (ContinuousLinearMap.compL ℂ (Coeff 2) PeriodOneHminusOne (Coeff 2)
    (periodOneMassInverse m)).comp periodOneMiuraProduct

theorem periodOneResolvedProduct_eq (m : ℕ) (a b : Coeff 2) :
    periodOneResolvedProduct m a b =
      Coeff.holderProduct (q := 2) (periodOneMassKernel m)
        (Coeff.youngConvolution youngRelation_two_two_top a b) := by
  ext k
  change periodOneMassInverse m (periodOneMiuraProduct a b) k = _
  rw [periodOneMassInverse_apply,periodOneMiuraProduct_apply,
    Coeff.holderProduct_apply,periodOneMassKernel_apply,Coeff.youngConvolution_apply]

theorem norm_periodOneResolvedProduct_le (m : ℕ) (a b : Coeff 2) :
    ‖periodOneResolvedProduct m a b‖ ≤ ‖periodOneMassKernel m‖*‖a‖*‖b‖ := by
  rw [periodOneResolvedProduct_eq]
  exact (Coeff.norm_holderProduct_le _ _).trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (Coeff.norm_youngConvolution_le youngRelation_two_two_top a b)
      (norm_nonneg (periodOneMassKernel m)))

/-- The shifted Miura map is v' + (m+1)v + v², as an H^-1 potential. -/
def periodOneShiftedMiura (m : ℕ) (v : Coeff 2) : PeriodOneHminusOne :=
  periodOneMassOperator m v + periodOneMiuraProduct v v

@[simp] theorem periodOneShiftedMiura_apply (m : ℕ) (v : Coeff 2) (k : ℤ) :
    (periodOneShiftedMiura m v).val k =
      periodOneMassSymbol m k*v k + ∑' j : ℤ, v (k-j)*v j := by
  exact congrArg₂ (· + ·) (periodOneMassOperator_apply m v k) (periodOneMiuraProduct_apply v v k)

theorem analyticAt_periodOneShiftedMiura (m : ℕ) (v : Coeff 2) :
    AnalyticAt ℂ (periodOneShiftedMiura m) v :=
  ((periodOneMassOperator m).analyticAt v).add
    ((periodOneMiuraProduct.analyticAt_bilinear _).comp₂ analyticAt_id analyticAt_id)

theorem periodOneMassInverse_shiftedMiura (m : ℕ) (v : Coeff 2) :
    periodOneMassInverse m (periodOneShiftedMiura m v) = v+periodOneResolvedProduct m v v := by
  rw [periodOneShiftedMiura,map_add,periodOneMassInverse_operator]
  rfl

end NLS
