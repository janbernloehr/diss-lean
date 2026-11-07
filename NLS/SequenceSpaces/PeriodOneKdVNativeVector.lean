import NLS.SequenceSpaces.PeriodOneSobolevMiuraMap

/-! # The literal period-one native KdV vector H4 to H1

The conservative nonlinear term is 3 times the derivative of the
actual quadratic product, with raw multiplier 2*pi*i*n.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS

theorem periodOneDerivativePower_weight_bound (s : ℝ) (m : ℕ) (n : ℤ) :
    Weight.sobolev s n*‖(2*I*(Real.pi : ℂ)*n)^m‖≤
      (2*Real.pi)^m*Weight.sobolev (s+(m : ℝ)) n := by
  rw [Weight.sobolev_add]
  simp only [norm_pow,norm_mul,Complex.norm_ofNat,Complex.norm_I,mul_one,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos Real.pi_pos,Complex.norm_intCast,Weight.sobolev_apply,Real.rpow_natCast]
  have hp : |(n : ℝ)|^m≤(1+|(n : ℝ)|)^m :=
    pow_le_pow_left₀ (abs_nonneg _) (by linarith) m
  rw [mul_pow]
  calc
    _ = ((2*Real.pi)^m*((1+|(n : ℝ)|)^s))*|(n : ℝ)|^m := by ring
    _ ≤ ((2*Real.pi)^m*((1+|(n : ℝ)|)^s))*(1+|(n : ℝ)|)^m :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by ring

def periodOneSobolevDerivativePower (s : ℝ) (m : ℕ) (p : ℝ≥0∞) [Fact (1≤p)] :
    WeightedCoeff (Weight.sobolev (s+(m : ℝ))) p →L[ℂ] WeightedCoeff (Weight.sobolev s) p :=
  WeightedCoeff.weightedMultiplierCLM _ _ (fun n => (2*I*(Real.pi : ℂ)*n)^m)
    ((2*Real.pi)^m) (by positivity) (periodOneDerivativePower_weight_bound s m)

@[simp] theorem periodOneSobolevDerivativePower_apply (s : ℝ) (m : ℕ) (p : ℝ≥0∞) [Fact (1≤p)]
    (a : WeightedCoeff (Weight.sobolev (s+(m : ℝ))) p) (n : ℤ) :
    (periodOneSobolevDerivativePower s m p a).val n=(2*I*(Real.pi : ℂ)*n)^m*a.val n := rfl

def periodOneKdVThirdDerivative :
    WeightedCoeff (Weight.sobolev 4) 2 →L[ℂ] WeightedCoeff (Weight.sobolev 1) 2 :=
  (periodOneSobolevDerivativePower 1 3 2).comp
    (WeightedCoeff.sobolevInclusion (by norm_num : (1 : ℝ)+(3 : ℕ)≤4))

def periodOneKdVFluxDerivative :
    WeightedCoeff (Weight.sobolev (3-1)) 2 →L[ℂ] WeightedCoeff (Weight.sobolev 1) 2 :=
  (periodOneSobolevDerivativePower 1 1 2).comp
    (WeightedCoeff.sobolevInclusion (by norm_num : (1 : ℝ)+(1 : ℕ)≤3-1))

def periodOneKdVNativeVector (a : WeightedCoeff (Weight.sobolev 4) 2) :
    WeightedCoeff (Weight.sobolev 1) 2 :=
  -(periodOneKdVThirdDerivative a)+(3 : ℂ) • periodOneKdVFluxDerivative
    (periodOneSobolevMiuraProductCLM 3 (by norm_num)
      (WeightedCoeff.sobolevInclusion (by norm_num : (3 : ℝ)≤4) a)
      (WeightedCoeff.sobolevInclusion (by norm_num : (3 : ℝ)≤4) a))

theorem analyticAt_periodOneKdVNativeVector (a : WeightedCoeff (Weight.sobolev 4) 2) :
    AnalyticAt ℂ periodOneKdVNativeVector a := by
  let L : WeightedCoeff (Weight.sobolev 4) 2 →L[ℂ] WeightedCoeff (Weight.sobolev 3) 2 :=
    WeightedCoeff.sobolevInclusion (by norm_num)
  have hprod := ((periodOneSobolevMiuraProductCLM 3 (by norm_num)).analyticAt_bilinear _).comp₂
    (L.analyticAt a) (L.analyticAt a)
  exact (periodOneKdVThirdDerivative.analyticAt a).neg.add
    (((periodOneKdVFluxDerivative.analyticAt _).comp hprod).const_smul (c := (3 : ℂ)))

theorem periodOneKdVNativeVector_apply (a : WeightedCoeff (Weight.sobolev 4) 2) (n : ℤ) :
    (periodOneKdVNativeVector a).val n=
      -(2*I*(Real.pi : ℂ)*n)^3*a.val n+
        3*(2*I*(Real.pi : ℂ)*n)*(∑' j : ℤ, a.val (n-j)*a.val j) := by
  change -(periodOneSobolevDerivativePower 1 3 2
    (WeightedCoeff.sobolevInclusion _ a)).val n+
      (3 : ℂ)*(periodOneSobolevDerivativePower 1 1 2 (WeightedCoeff.sobolevInclusion _
        (periodOneSobolevMiuraProductCLM 3 (by norm_num)
          (WeightedCoeff.sobolevInclusion _ a) (WeightedCoeff.sobolevInclusion _ a)))).val n=_
  simp only [periodOneSobolevDerivativePower_apply,WeightedCoeff.sobolevInclusion_apply,
    periodOneSobolevMiuraProductCLM_apply,periodOneSobolevMiuraProduct_apply,pow_one]
  ring

@[simp] theorem periodOneKdVNativeVector_zero_mode (a : WeightedCoeff (Weight.sobolev 4) 2) :
    (periodOneKdVNativeVector a).val 0=0 := by
  rw [periodOneKdVNativeVector_apply]
  simp only [Int.cast_zero,mul_zero,zero_pow (by norm_num : (3 : ℕ)≠0),neg_zero,zero_mul,add_zero]

end NLS
