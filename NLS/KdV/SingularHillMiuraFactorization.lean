import NLS.KdV.SingularHillPhysical
import NLS.Fourier.PeriodicSingularMultiplicationFamily
import NLS.SequenceSpaces.PeriodOneMiuraShift
import NLS.SequenceSpaces.YoungConvolutionModule
import NLS.SequenceSpaces.WeakFirstOrderRegularity

/-! Distributional Miura factorization on the unchanged original period-two
H1/H-minus-one spaces. The Miura input is any original period-two L2
sequence. No derivative or boundedness of that input is assumed. -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue
open NLS.ZakharovShabat

/-- Original period-two L2 coefficients realized in the native H-minus-one space. -/
def l2OriginalHminus : Coeff 2 →L[ℂ] FourierLebesgueSpace (2:ℝ) (-1) 2 :=
  (sobolevCoefficients (-1) 2).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    periodOneL2Inclusion

theorem l2OriginalHminus_coefficient (u : Coeff 2) (n : ℤ) :
    (l2OriginalHminus u).val (mode (-n)) = u n := by
  change ((sobolevCoefficients (-1) 2) ((sobolevCoefficients (-1) 2).symm _)).val n = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact periodOneL2Inclusion_apply u n

/-- The original period-two distributional derivative of arbitrary L2 coefficients. -/
def l2DerivativeOriginalHminus : Coeff 2 →L[ℂ] FourierLebesgueSpace (2:ℝ) (-1) 2 :=
  (sobolevCoefficients (-1) 2).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((1/2:ℂ) • (periodOneMassOperator 0-periodOneL2Inclusion))

theorem l2DerivativeOriginalHminus_coefficient (u : Coeff 2) (n : ℤ) :
    (l2DerivativeOriginalHminus u).val (mode (-n)) = I*(Real.pi:ℂ)*n*u n := by
  change ((sobolevCoefficients (-1) 2) ((sobolevCoefficients (-1) 2).symm _)).val n = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  change (1/2:ℂ)*((periodOneMassOperator 0 u).val n-(periodOneL2Inclusion u).val n) = _
  rw [periodOneMassOperator_apply, periodOneL2Inclusion_apply]
  simp only [periodOneMassSymbol, Nat.cast_zero, zero_add, ofReal_one]
  ring

/-- The actual L2 by L2 product as an original H-minus-one distribution. -/
def l2ProductOriginalHminus (u : Coeff 2) : Coeff 2 →L[ℂ] FourierLebesgueSpace (2:ℝ) (-1) 2 :=
  (sobolevCoefficients (-1) 2).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (periodOneMiuraProduct u)

theorem l2ProductOriginalHminus_coefficient (u v : Coeff 2) (n : ℤ) :
    (l2ProductOriginalHminus u v).val (mode (-n)) = ∑' k : ℤ, u (n-k)*v k := by
  change ((sobolevCoefficients (-1) 2) ((sobolevCoefficients (-1) 2).symm _)).val n = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact periodOneMiuraProduct_apply u v n

/-- The native original H1 vector represented by the same raw domain coefficients. -/
def scalarDomainOriginalH1 (f : ScalarDomain 2) : FourierLebesgueSpace (2:ℝ) 1 2 :=
  (sobolevCoefficients 1 2).symm f

theorem scalarDomainOriginalH1_coefficient (f : ScalarDomain 2) (n : ℤ) :
    (scalarDomainOriginalH1 f).val (mode (-n)) = f.val n := by
  change ((sobolevCoefficients 1 2) ((sobolevCoefficients 1 2).symm f)).val n = _
  rw [LinearIsometryEquiv.apply_symm_apply]

/-- Distributional Leibniz rule for a rough L2 factor and a full original
H1 factor, with all resulting terms in the native H-minus-one space. -/
theorem l2DerivativeOriginalHminus_product (u : Coeff 2) (f : ScalarDomain 2) :
    l2DerivativeOriginalHminus (potentialMul (by norm_num) u f) =
      hminusOneProduct (l2DerivativeOriginalHminus u) (scalarDomainOriginalH1 f)+
        l2ProductOriginalHminus u (derivative f) := by
  apply Subtype.ext
  apply Distribution.ext_coefficients
  intro n
  change _ = (hminusOneProduct _ _).val (mode (-n)) + (l2ProductOriginalHminus _ _).val (mode (-n))
  rw [l2DerivativeOriginalHminus_coefficient, potentialMul_apply, hminusOneProduct_coefficient,
    l2ProductOriginalHminus_coefficient]
  simp only [l2DerivativeOriginalHminus_coefficient, scalarDomainOriginalH1_coefficient,
    ZakharovShabat.derivative_apply]
  have hs₁ := (summable_norm_hminusOneProduct_terms (l2DerivativeOriginalHminus u)
    (scalarDomainOriginalH1 f) n).of_norm
  simp only [l2DerivativeOriginalHminus_coefficient, scalarDomainOriginalH1_coefficient] at hs₁
  have hs₂ := (Coeff.summable_norm_youngConvolution_terms youngRelation_two_two_top u (derivative f) n).of_norm
  simp only [ZakharovShabat.derivative_apply] at hs₂
  rw [← hs₁.tsum_add hs₂, ← tsum_mul_left]
  apply tsum_congr
  intro k
  push_cast
  ring

/-- Associativity of the actual weak product with an H1 multiplier. -/
theorem l2ProductOriginalHminus_product (u v : Coeff 2) (f : ScalarDomain 2) :
    hminusOneProduct (l2ProductOriginalHminus u v) (scalarDomainOriginalH1 f) =
      l2ProductOriginalHminus u (potentialMul (by norm_num) v f) := by
  apply Subtype.ext
  apply Distribution.ext_coefficients
  intro n
  rw [hminusOneProduct_coefficient, l2ProductOriginalHminus_coefficient]
  simp only [l2ProductOriginalHminus_coefficient, scalarDomainOriginalH1_coefficient]
  have he := congrArg (fun a : Coeff ⊤ => a n)
    (Coeff.youngConvolution_convolution_right youngRelation_two_two_top u v
      (WeightedCoeff.sobolevToL1CLM 2 (by norm_num) f))
  simpa only [Coeff.youngConvolution_apply, Coeff.convolution_apply,
    WeightedCoeff.sobolevToL1CLM_apply, potentialMul_apply] using he.symm

/-- The free second-order term is minus the derivative of the actual first derivative. -/
theorem singularHillLaplacian_eq_derivative (f : ScalarDomain 2) :
    singularHillLaplacian (scalarDomainOriginalH1 f) = -l2DerivativeOriginalHminus (derivative f) := by
  apply Subtype.ext
  apply Distribution.ext_coefficients
  intro n
  change _ = -(l2DerivativeOriginalHminus (derivative f)).val (mode (-n))
  rw [singularHillLaplacian_coefficient, scalarDomainOriginalH1_coefficient,
    l2DerivativeOriginalHminus_coefficient, ZakharovShabat.derivative_apply]
  simp only [freeHillValue, ofReal_mul, ofReal_pow]
  push_cast
  ring_nf
  simp only [I_sq]
  ring

/-- The literal native Miura potential u'+u² for any original L2 input. -/
def singularHillMiuraPotential (u : Coeff 2) : FourierLebesgueSpace (2:ℝ) (-1) 2 :=
  l2DerivativeOriginalHminus u+l2ProductOriginalHminus u u

/-- The quasi-derivative is a genuine L2 sequence before any eigen-equation is used. -/
def singularHillQuasiDerivative (u : Coeff 2) (f : ScalarDomain 2) : Coeff 2 :=
  derivative f-potentialMul (by norm_num) u f

/-- Exact original-domain Miura factorization, valid for every complex L2
Miura input and every original H1 domain vector. -/
theorem singularHillOperator_miura_factorization (u : Coeff 2) (f : ScalarDomain 2) :
    singularHillOperator (singularHillMiuraPotential u) (scalarDomainOriginalH1 f) =
      -l2DerivativeOriginalHminus (singularHillQuasiDerivative u f)-
        l2ProductOriginalHminus u (singularHillQuasiDerivative u f) := by
  have hprod := l2DerivativeOriginalHminus_product u f
  change singularHillLaplacian (scalarDomainOriginalH1 f)+
    hminusOneProduct (l2DerivativeOriginalHminus u+l2ProductOriginalHminus u u)
      (scalarDomainOriginalH1 f) = _
  rw [hminusOneProduct_add_left, l2ProductOriginalHminus_product,
    singularHillLaplacian_eq_derivative]
  rw [eq_sub_of_add_eq hprod.symm]
  simp only [singularHillQuasiDerivative, map_sub]
  abel

/-- The coefficient realization covers the entire original domain. -/
theorem scalarDomainOriginalH1_sobolevCoefficients (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    scalarDomainOriginalH1 (sobolevCoefficients 1 2 f) = f :=
  (sobolevCoefficients 1 2).symm_apply_apply f

/-- Domain inclusion and the genuine L2 inclusion represent the same entire distribution. -/
theorem l2OriginalHminus_scalarInclusion (f : ScalarDomain 2) :
    l2OriginalHminus (scalarInclusion f) = singularHillDomainInclusion (scalarDomainOriginalH1 f) := by
  apply Subtype.ext
  apply Distribution.ext_coefficients
  intro n
  rw [l2OriginalHminus_coefficient, singularHillDomainInclusion_coefficient,
    scalarDomainOriginalH1_coefficient, scalarInclusion_apply]

/-- The inhomogeneous physical Hill equation forces the L2 quasi-derivative
to solve the exact weak first-order equation with L2 forcing. -/
theorem singularHillQuasiDerivative_weak_equation (u b : Coeff 2) (f : ScalarDomain 2)
    (h : singularHillOperator (singularHillMiuraPotential u) (scalarDomainOriginalH1 f) =
      l2OriginalHminus b) (n : ℤ) :
    I*(Real.pi:ℂ)*n*singularHillQuasiDerivative u f n =
      (∑' k : ℤ, (-u) (n-k)*singularHillQuasiDerivative u f k)+(-b) n := by
  have he := (singularHillOperator_miura_factorization u f).symm.trans h
  have hn := congrArg (fun q : FourierLebesgueSpace (2:ℝ) (-1) 2 => q.val (mode (-n))) he
  change -(l2DerivativeOriginalHminus (singularHillQuasiDerivative u f)).val (mode (-n))-
    (l2ProductOriginalHminus u (singularHillQuasiDerivative u f)).val (mode (-n)) =
      (l2OriginalHminus b).val (mode (-n)) at hn
  rw [l2DerivativeOriginalHminus_coefficient, l2ProductOriginalHminus_coefficient,
    l2OriginalHminus_coefficient] at hn
  simp only [lp.coeFn_neg, Pi.neg_apply, neg_mul, tsum_neg]
  linear_combination -hn

/-- Every L2-forced original Hill equation recovers a full H1 quasi-derivative. -/
theorem singularHillQuasiDerivative_memlp_sobolev_one (u b : Coeff 2) (f : ScalarDomain 2)
    (h : singularHillOperator (singularHillMiuraPotential u) (scalarDomainOriginalH1 f) =
      l2OriginalHminus b) :
    Memℓp (fun n => (Weight.sobolev 1 n : ℂ)*singularHillQuasiDerivative u f n) 2 :=
  weakFirstOrder_memlp_sobolev_one (-u) (singularHillQuasiDerivative u f) (-b)
    (singularHillQuasiDerivative_weak_equation u b f h)

/-- The actual H1 quasi-derivative recovered from the full inhomogeneous equation. -/
def singularHillQuasiDerivativeLift (u b : Coeff 2) (f : ScalarDomain 2)
    (h : singularHillOperator (singularHillMiuraPotential u) (scalarDomainOriginalH1 f) =
      l2OriginalHminus b) : ScalarDomain 2 :=
  weakFirstOrderLift (-u) (singularHillQuasiDerivative u f) (-b)
    (singularHillQuasiDerivative_weak_equation u b f h)

/-- Recovery preserves every actual raw quasi-derivative coefficient. -/
theorem scalarInclusion_singularHillQuasiDerivativeLift (u b : Coeff 2) (f : ScalarDomain 2)
    (h : singularHillOperator (singularHillMiuraPotential u) (scalarDomainOriginalH1 f) =
      l2OriginalHminus b) :
    scalarInclusion (singularHillQuasiDerivativeLift u b f h) = singularHillQuasiDerivative u f :=
  scalarInclusion_weakFirstOrderLift _ _ _ _

/-- The recovered first-order system is a literal equation in the original L2 space. -/
theorem derivative_singularHillQuasiDerivativeLift (u b : Coeff 2) (f : ScalarDomain 2)
    (h : singularHillOperator (singularHillMiuraPotential u) (scalarDomainOriginalH1 f) =
      l2OriginalHminus b) :
    ZakharovShabat.derivative (singularHillQuasiDerivativeLift u b f h) =
      -potentialMul (by norm_num) u (singularHillQuasiDerivativeLift u b f h)-b := by
  have he := derivative_weakFirstOrderLift (-u) (singularHillQuasiDerivative u f) (-b)
    (singularHillQuasiDerivative_weak_equation u b f h)
  change ZakharovShabat.derivative (singularHillQuasiDerivativeLift u b f h) = _ at he
  rw [he]
  ext n
  simp only [potentialMul_apply, lp.coeFn_add, lp.coeFn_neg, Pi.add_apply,
    Pi.neg_apply, neg_mul, tsum_neg, sub_eq_add_neg, singularHillQuasiDerivativeLift]

end NLS.KdV
