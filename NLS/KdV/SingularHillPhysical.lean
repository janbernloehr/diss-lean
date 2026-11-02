import NLS.KdV.FreeHill
import NLS.Fourier.PeriodicH1Multiplication
import NLS.Fourier.SmoothPeriodicDistributionDerivative

/-! # The singular periodic Hill operator on its original H1 domain

The operator acts from original period-two H1 distributions to original
H-minus-one distributions. Its free part is minus the actual second
distributional derivative and its potential part is multiplication defined
by physical H1 duality. The Fourier eigen-equation is proved equivalent to
this operator equation. No spectral enumeration or localization is assumed.
-/
noncomputable section
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue

/-- The free positive Hill symbol defines a bounded map H1 to H-minus-one. -/
theorem singularHillLaplacian_weight_bound (k : ℤ) :
    Weight.sobolev (-1) k * ‖(freeHillValue k:ℂ)‖ ≤ Real.pi^2 * Weight.sobolev 1 k := by
  have hv : 0 ≤ freeHillValue k := by unfold freeHillValue; positivity
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv]
  simp only [Weight.sobolev_apply, Real.rpow_neg_one, Real.rpow_one, freeHillValue]
  rw [mul_comm ((1+|(k:ℝ)|)⁻¹), ← div_eq_mul_inv]
  apply (div_le_iff₀ (by positivity : 0 < 1+|(k:ℝ)|)).mpr
  calc
    _ ≤ Real.pi^2*(1+|(k:ℝ)|)^2 := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg Real.pi)
      nlinarith [sq_abs (k:ℝ), abs_nonneg (k:ℝ)]
    _ = _ := by ring

/-- The free operator on the original full H1 domain. -/
def singularHillLaplacian : FourierLebesgueSpace (2:ℝ) 1 2 →L[ℂ]
    FourierLebesgueSpace (2:ℝ) (-1) 2 :=
  (sobolevCoefficients (-1) 2).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((WeightedCoeff.weightedMultiplierCLM _ _ (fun k => (freeHillValue k:ℂ))
      (Real.pi^2) (by positivity) singularHillLaplacian_weight_bound).comp
        (sobolevCoefficients 1 2).toContinuousLinearEquiv.toContinuousLinearMap)

/-- The exact free symbol in the original normalized Fourier convention. -/
theorem singularHillLaplacian_coefficient (f : FourierLebesgueSpace (2:ℝ) 1 2) (k : ℤ) :
    (singularHillLaplacian f).val (mode (-k)) =
      (freeHillValue k:ℂ) * f.val (mode (-k)) := by
  change ((sobolevCoefficients (-1) 2) ((sobolevCoefficients (-1) 2).symm _)).val k = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

/-- The free operator is minus the genuine second derivative on all original
smooth tests, with period two and the factor pi squared retained. -/
theorem singularHillLaplacian_val (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    (singularHillLaplacian f).val = -f.val.derivative.derivative := by
  apply Distribution.ext_coefficients
  intro k
  rw [singularHillLaplacian_coefficient]
  change _ = -(f.val.derivative.derivative (mode (-k)))
  rw [Distribution.derivative_coefficient, Distribution.derivative_coefficient]
  simp only [freeHillValue, Complex.ofReal_mul, Complex.ofReal_pow]
  push_cast
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- Inclusion of the H1 domain in the underlying H-minus-one space. -/
def singularHillDomainInclusion : FourierLebesgueSpace (2:ℝ) 1 2 →L[ℂ]
    FourierLebesgueSpace (2:ℝ) (-1) 2 :=
  (sobolevCoefficients (-1) 2).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((WeightedCoeff.sobolevInclusion (by norm_num : (-1:ℝ) ≤ 1)).comp
      (sobolevCoefficients 1 2).toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem singularHillDomainInclusion_coefficient
    (f : FourierLebesgueSpace (2:ℝ) 1 2) (k : ℤ) :
    (singularHillDomainInclusion f).val (mode (-k)) = f.val (mode (-k)) := by
  change ((sobolevCoefficients (-1) 2) ((sobolevCoefficients (-1) 2).symm _)).val k = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact WeightedCoeff.sobolevInclusion_apply (by norm_num : (-1:ℝ) ≤ 1)
    (sobolevCoefficients 1 2 f) k

/-- Inclusion keeps the whole original distribution unchanged. -/
theorem singularHillDomainInclusion_val (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    (singularHillDomainInclusion f).val = f.val := by
  apply Distribution.ext_coefficients
  exact singularHillDomainInclusion_coefficient f

/-- The actual singular Hill operator -d²/dx²+q on the original H1 domain. -/
def singularHillOperator (q : FourierLebesgueSpace (2:ℝ) (-1) 2) :
    FourierLebesgueSpace (2:ℝ) 1 2 →L[ℂ] FourierLebesgueSpace (2:ℝ) (-1) 2 :=
  singularHillLaplacian + hminusOneMultiplication q

/-- The operator equals the genuine distributional expression. -/
theorem singularHillOperator_val (q : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    (singularHillOperator q f).val =
      -f.val.derivative.derivative + (hminusOneProduct q f).val := by
  change (singularHillLaplacian f).val + (hminusOneProduct q f).val = _
  rw [singularHillLaplacian_val]

/-- The physical singular operator has the full convergent Fourier formula. -/
theorem singularHillOperator_coefficient (q : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (f : FourierLebesgueSpace (2:ℝ) 1 2) (m : ℤ) :
    (singularHillOperator q f).val (mode (-m)) =
      (freeHillValue m:ℂ)*f.val (mode (-m)) +
        ∑' k : ℤ, q.val (mode (-(m-k)))*f.val (mode (-k)) := by
  change (singularHillLaplacian f).val (mode (-m)) +
    (hminusOneProduct q f).val (mode (-m)) = _
  rw [singularHillLaplacian_coefficient, hminusOneProduct_coefficient]

/-- Equality in the original H-minus-one space is equivalent to the source's
Fourier eigen-equation for an actual original H1 domain element. -/
theorem singularHillOperator_eigen_iff (q : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (z : ℂ) (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    singularHillOperator q f = z • singularHillDomainInclusion f ↔
      ∀ m : ℤ, (z-(freeHillValue m:ℂ))*f.val (mode (-m)) =
        ∑' k : ℤ, q.val (mode (-(m-k)))*f.val (mode (-k)) := by
  constructor
  · intro he m
    have hm := congrArg (fun u : FourierLebesgueSpace (2:ℝ) (-1) 2 => u.val (mode (-m))) he
    change (singularHillOperator q f).val (mode (-m)) =
      z*(singularHillDomainInclusion f).val (mode (-m)) at hm
    rw [singularHillOperator_coefficient, singularHillDomainInclusion_coefficient] at hm
    linear_combination -hm
  · intro he
    apply Subtype.ext
    apply Distribution.ext_coefficients
    intro m
    change (singularHillOperator q f).val (mode (-m)) =
      z*(singularHillDomainInclusion f).val (mode (-m))
    rw [singularHillOperator_coefficient, singularHillDomainInclusion_coefficient]
    linear_combination -(he m)

end NLS.KdV
