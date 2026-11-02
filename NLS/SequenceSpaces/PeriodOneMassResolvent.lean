import NLS.SequenceSpaces.WeightedMultiplier
import NLS.SequenceSpaces.HolderEmbedding
import NLS.SequenceSpaces.DominatedConvergence
import Mathlib.Analysis.Real.Pi.Bounds

/-! # The massive first-order resolvent in period-one Fourier coordinates

The symbol is (m+1+2*pi*i*n)^(-1). It gives a uniformly bounded inverse
from H^-1 to L2. Its coefficient sequence, rather than its H^-1-to-L2
operator norm, tends to zero in L2 as the positive mass tends to infinity.
This is the smallness needed for the quadratic Riccati term.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS

abbrev PeriodOneHminusOne := WeightedCoeff (Weight.sobolev (-1)) 2

def periodOneMassSymbol (m : ℕ) (k : ℤ) : ℂ :=
  ((m : ℝ)+1 : ℝ)+2*I*(Real.pi : ℂ)*k

theorem periodOneMassSymbol_ne_zero (m : ℕ) (k : ℤ) : periodOneMassSymbol m k ≠ 0 := by
  intro he
  have hre := congrArg Complex.re he
  have hp : (periodOneMassSymbol m k).re = (m : ℝ)+1 := by simp [periodOneMassSymbol]
  rw [hp] at hre
  simp only [zero_re] at hre
  have hm : (0 : ℝ) ≤ m := by positivity
  linarith

theorem periodOneMassSymbol_re_lower (m : ℕ) (k : ℤ) :
    (m : ℝ)+1 ≤ ‖periodOneMassSymbol m k‖ := by
  have h := re_le_norm (periodOneMassSymbol m k)
  simpa [periodOneMassSymbol] using h

theorem periodOneMassSymbol_frequency_lower (m : ℕ) (k : ℤ) :
    |(k : ℝ)| ≤ ‖periodOneMassSymbol m k‖ := by
  have h := abs_im_le_norm (periodOneMassSymbol m k)
  have he : (periodOneMassSymbol m k).im = 2*Real.pi*(k : ℝ) := by
    simp [periodOneMassSymbol]
  rw [he,abs_mul,abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2),abs_of_pos Real.pi_pos] at h
  nlinarith [Real.pi_gt_three,abs_nonneg (k : ℝ)]

theorem norm_periodOneMassSymbol_inv_le_bracket (m : ℕ) (k : ℤ) :
    ‖(periodOneMassSymbol m k)⁻¹‖ ≤ 2/(1+|(k : ℝ)|) := by
  have hlow : (1+|(k : ℝ)|)/2 ≤ ‖periodOneMassSymbol m k‖ := by
    linarith [periodOneMassSymbol_re_lower m k,periodOneMassSymbol_frequency_lower m k,
      show (0 : ℝ) ≤ m by positivity]
  rw [norm_inv]
  calc
    _ = 1/‖periodOneMassSymbol m k‖ := by rw [one_div]
    _ ≤ 1/((1+|(k : ℝ)|)/2) := one_div_le_one_div_of_le (by positivity) hlow
    _ = 2/(1+|(k : ℝ)|) := by field_simp

def inverseBracketCoefficients : Coeff 2 :=
  ⟨fun k => (Weight.sobolev 1 k : ℂ)⁻¹,Weight.inverse_sobolev_one_memlp (by norm_num)⟩

theorem norm_inverseBracketCoefficients_apply (k : ℤ) :
    ‖inverseBracketCoefficients k‖ = (1+|(k : ℝ)|)⁻¹ := by
  change ‖(Weight.sobolev 1 k : ℂ)⁻¹‖ = _
  rw [norm_inv,Complex.norm_real,Weight.sobolev_apply,Real.rpow_one,
    Real.norm_eq_abs,abs_of_pos (by positivity : (0 : ℝ) < 1+|(k : ℝ)|)]

def periodOneMassKernel (m : ℕ) : Coeff 2 :=
  ⟨fun k => (periodOneMassSymbol m k)⁻¹,by
    apply ((lp.memℓp inverseBracketCoefficients).norm.const_mul (2 : ℝ)).mono
    intro k
    change ‖(periodOneMassSymbol m k)⁻¹‖ ≤ 2 * ‖inverseBracketCoefficients k‖
    rw [norm_inverseBracketCoefficients_apply]
    simpa only [div_eq_mul_inv] using norm_periodOneMassSymbol_inv_le_bracket m k⟩

@[simp] theorem periodOneMassKernel_apply (m : ℕ) (k : ℤ) :
    periodOneMassKernel m k = (periodOneMassSymbol m k)⁻¹ := rfl

theorem tendsto_periodOneMassKernel_zero :
    Tendsto periodOneMassKernel atTop (𝓝 (0 : Coeff 2)) := by
  apply Coeff.tendsto_zero_of_dominated (by simp) periodOneMassKernel ((2 : ℂ) • inverseBracketCoefficients)
  · apply Eventually.of_forall
    intro m k
    change ‖(periodOneMassSymbol m k)⁻¹‖ ≤ ‖(2 : ℂ) * inverseBracketCoefficients k‖
    rw [norm_mul,Complex.norm_ofNat,norm_inverseBracketCoefficients_apply]
    simpa only [div_eq_mul_inv] using norm_periodOneMassSymbol_inv_le_bracket m k
  · intro k
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have ht : Tendsto (fun m : ℕ => (m : ℝ)+1) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have hi := tendsto_inv_atTop_zero.comp ht
    apply squeeze_zero (fun m => norm_nonneg (periodOneMassKernel m k)) (fun m => ?_) hi
    change ‖(periodOneMassSymbol m k)⁻¹‖ ≤ ((m : ℝ)+1)⁻¹
    rw [norm_inv]
    simpa only [one_div] using one_div_le_one_div_of_le
      (by positivity : (0 : ℝ) < (m : ℝ)+1) (periodOneMassSymbol_re_lower m k)

private theorem norm_mass_weighted (m : ℕ) (k : ℤ) :
    Weight.sobolev (-1) k*‖periodOneMassSymbol m k‖ ≤ ((m : ℝ)+1+2*Real.pi)*Weight.one k := by
  have hb := norm_add_le (((m : ℝ)+1 : ℝ) : ℂ) (2*I*(Real.pi : ℂ)*k)
  have he : ‖(((m : ℝ)+1 : ℝ) : ℂ)‖ = (m : ℝ)+1 := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity)]
  have hk : ‖(2 : ℂ)*I*(Real.pi : ℂ)*k‖ = 2*Real.pi*|(k : ℝ)| := by simp [abs_of_pos Real.pi_pos]
  rw [he,hk] at hb
  simp only [Weight.sobolev_apply,Real.rpow_neg_one,Weight.one_apply,mul_one]
  apply (mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ (1+|(k : ℝ)|)⁻¹)).trans
  rw [inv_mul_eq_div]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 1+|(k : ℝ)|)).mpr
  nlinarith [mul_nonneg (show 0 ≤ (m : ℝ)+1 by positivity) (abs_nonneg (k : ℝ)),Real.pi_pos]

private theorem norm_mass_inverse_weighted (m : ℕ) (k : ℤ) :
    Weight.one k*‖(periodOneMassSymbol m k)⁻¹‖ ≤ 2*Weight.sobolev (-1) k := by
  simpa only [Weight.one_apply,one_mul,Weight.sobolev_apply,Real.rpow_neg_one,div_eq_mul_inv] using
    norm_periodOneMassSymbol_inv_le_bracket m k

/-- The actual period-one first derivative plus the positive mass m+1. -/
def periodOneMassOperator (m : ℕ) : Coeff 2 →L[ℂ] PeriodOneHminusOne :=
  (WeightedCoeff.weightedMultiplierCLM Weight.one (Weight.sobolev (-1)) (periodOneMassSymbol m)
    ((m : ℝ)+1+2*Real.pi) (by positivity) (norm_mass_weighted m)).comp
      (WeightedCoeff.weightIsometry Weight.one 2).symm.toContinuousLinearEquiv.toContinuousLinearMap

/-- The inverse acts in the genuine H^-1 norm, with a uniform bound. -/
def periodOneMassInverse (m : ℕ) : PeriodOneHminusOne →L[ℂ] Coeff 2 :=
  (WeightedCoeff.weightIsometry Weight.one 2).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (WeightedCoeff.weightedMultiplierCLM (Weight.sobolev (-1)) Weight.one
      (fun k => (periodOneMassSymbol m k)⁻¹) 2 (by norm_num) (norm_mass_inverse_weighted m))

@[simp] theorem periodOneMassOperator_apply (m : ℕ) (a : Coeff 2) (k : ℤ) :
    (periodOneMassOperator m a).val k = periodOneMassSymbol m k*a k := by
  change periodOneMassSymbol m k*(a k/(Weight.one k : ℂ)) = _
  simp only [Weight.one_apply,ofReal_one,div_one]

@[simp] theorem periodOneMassInverse_apply (m : ℕ) (q : PeriodOneHminusOne) (k : ℤ) :
    periodOneMassInverse m q k = (periodOneMassSymbol m k)⁻¹*q.val k := by
  change (Weight.one k : ℂ)*((periodOneMassSymbol m k)⁻¹*q.val k) = _
  simp only [Weight.one_apply,ofReal_one,one_mul]

theorem norm_periodOneMassInverse_le (m : ℕ) (q : PeriodOneHminusOne) :
    ‖periodOneMassInverse m q‖ ≤ 2*‖q‖ := by
  change ‖(WeightedCoeff.weightIsometry Weight.one 2)
    (WeightedCoeff.weightedMultiplier _ _ _ 2 (norm_mass_inverse_weighted m) q)‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact WeightedCoeff.norm_weightedMultiplier_le _ _ _ 2 (by norm_num) _ q

@[simp] theorem periodOneMassOperator_inverse (m : ℕ) (q : PeriodOneHminusOne) :
    periodOneMassOperator m (periodOneMassInverse m q) = q := by
  apply Subtype.ext
  funext k
  rw [periodOneMassOperator_apply,periodOneMassInverse_apply,← mul_assoc,
    mul_inv_cancel₀ (periodOneMassSymbol_ne_zero m k),one_mul]

@[simp] theorem periodOneMassInverse_operator (m : ℕ) (a : Coeff 2) :
    periodOneMassInverse m (periodOneMassOperator m a) = a := by
  ext k
  rw [periodOneMassInverse_apply,periodOneMassOperator_apply,← mul_assoc,
    inv_mul_cancel₀ (periodOneMassSymbol_ne_zero m k),one_mul]

theorem periodOneMassInverse_injective (m : ℕ) : Function.Injective (periodOneMassInverse m) :=
  Function.LeftInverse.injective (periodOneMassOperator_inverse m)

def periodOneMassEquiv (m : ℕ) : Coeff 2 ≃L[ℂ] PeriodOneHminusOne where
  toLinearEquiv :=
    { toLinearMap := (periodOneMassOperator m).toLinearMap
      invFun := periodOneMassInverse m
      left_inv := periodOneMassInverse_operator m
      right_inv := periodOneMassOperator_inverse m }
  continuous_toFun := (periodOneMassOperator m).continuous
  continuous_invFun := (periodOneMassInverse m).continuous

end NLS
