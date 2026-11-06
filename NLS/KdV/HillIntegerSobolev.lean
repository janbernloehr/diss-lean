import NLS.KdV.HillSobolevHierarchy
import NLS.KdV.HillPeriodOnePotential

/-! # Coefficient-preserving inverse bounded maps for every native period-one integer Sobolev domain. -/

noncomputable section
set_option autoImplicit false
open Complex NLS.Fourier NLS.ZakharovShabat
namespace NLS.KdV

def hillIntegerWeight (m : ℕ) : SpectralWeight := SpectralWeight.piSobolev m (Nat.cast_nonneg m)

theorem hillIntegerWeight_apply (m : ℕ) (k : ℤ) :
    hillIntegerWeight m (2*k) = (1+2*Real.pi*|(k : ℝ)|)^m := by
  simp [hillIntegerWeight, SpectralWeight.piSobolev_apply, Real.rpow_natCast,
    abs_mul, abs_of_pos Real.pi_pos, mul_comm, mul_left_comm]

theorem hillIntegerWeight_dominate_scalar (m : ℕ) (k : ℤ) :
    Weight.sobolev m k ≤ (hillIntegerWeight m).doubleIndex.toWeight k := by
  rw [Weight.sobolev_apply, Real.rpow_natCast, SpectralWeight.toWeight_apply,
    SpectralWeight.doubleIndex_apply, hillIntegerWeight_apply]
  apply pow_le_pow_left₀ (by positivity)
  nlinarith [Real.pi_gt_three, abs_nonneg (k : ℝ)]

def hillNativeIntegerToScalar (m : ℕ) :
    WeightedCoeff (hillIntegerWeight m).doubleIndex.toWeight 2 →L[ℂ] ScalarSobolev m :=
  WeightedCoeff.inclusionCLM _ _ (hillIntegerWeight_dominate_scalar m)

@[simp] theorem hillNativeIntegerToScalar_apply (m : ℕ)
    (p : WeightedCoeff (hillIntegerWeight m).doubleIndex.toWeight 2) (k : ℤ) :
    (hillNativeIntegerToScalar m p).val k = p.val k :=
  WeightedCoeff.inclusionCLM_apply _ _ _ p k

theorem hillIntegerWeight_le_scalar_scaled (m : ℕ) (k : ℤ) :
    (hillIntegerWeight m).doubleIndex.toWeight k ≤ (2*Real.pi)^m * Weight.sobolev m k := by
  rw [SpectralWeight.toWeight_apply, SpectralWeight.doubleIndex_apply, hillIntegerWeight_apply,
    Weight.sobolev_apply, Real.rpow_natCast]
  calc
    _ ≤ ((2*Real.pi)*(1+|(k : ℝ)|))^m := by
      apply pow_le_pow_left₀ (by positivity)
      nlinarith [Real.pi_gt_three]
    _ = _ := mul_pow _ _ _

def hillScalarToNativeInteger (m : ℕ) :
    ScalarSobolev m →L[ℂ] WeightedCoeff (hillIntegerWeight m).doubleIndex.toWeight 2 :=
  WeightedCoeff.weightedMultiplierCLM _ _ (fun _ => 1) ((2*Real.pi)^m) (by positivity)
    (fun k => by simpa only [norm_one, mul_one] using hillIntegerWeight_le_scalar_scaled m k)

@[simp] theorem hillScalarToNativeInteger_apply (m : ℕ) (a : ScalarSobolev m) (k : ℤ) :
    (hillScalarToNativeInteger m a).val k = a.val k := by
  change (1 : ℂ)*a.val k = a.val k
  exact one_mul _

@[simp] theorem hillNativeIntegerToScalar_scalarToNativeInteger (m : ℕ) (a : ScalarSobolev m) :
    hillNativeIntegerToScalar m (hillScalarToNativeInteger m a) = a := by
  apply Subtype.ext
  funext k
  rw [hillNativeIntegerToScalar_apply, hillScalarToNativeInteger_apply]

@[simp] theorem hillScalarToNativeInteger_nativeIntegerToScalar (m : ℕ)
    (p : WeightedCoeff (hillIntegerWeight m).doubleIndex.toWeight 2) :
    hillScalarToNativeInteger m (hillNativeIntegerToScalar m p) = p := by
  apply Subtype.ext
  funext k
  rw [hillScalarToNativeInteger_apply, hillNativeIntegerToScalar_apply]

theorem hillIntegerWeight_growth (m n : ℕ) : (n : ℝ)^m ≤ hillIntegerWeight m (2*(n : ℤ)) := by
  rw [hillIntegerWeight_apply]
  apply pow_le_pow_left₀ (Nat.cast_nonneg n)
  rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg n)]
  nlinarith [Real.pi_gt_three, Nat.cast_nonneg (α := ℝ) n]

end NLS.KdV
