import NLS.MKdV.MiuraSobolevNormalizedCartesian
import NLS.MKdV.MiuraNativeHamiltonianActionFlow
import NLS.ComplexAnalysis.CartesianPlaneRotationScalar

/-! # Complete physical action rotations in normalized native Cartesian coordinates -/
noncomputable section
open Set Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem miuraPositiveSobolevWeightEquiv_eval (s : ℕ) (z : MiuraPositiveSobolevTarget s) (n : ℤ) :
    miuraPositiveCartesianEval n (miuraPositiveSobolevWeightEquiv s z) =
      (Weight.sobolev (s : ℝ) n : ℂ) • miuraSobolevPositiveEval s n z := by
  apply Prod.ext
  · change ((miuraCartesianWeight s n : ℂ)*z.1.1.val.val n)/(Weight.sobolev (1/2) n : ℂ) =
      (Weight.sobolev (s : ℝ) n : ℂ)*z.1.1.val.val n
    rw [miuraCartesianWeight_factor]
    push_cast
    rw [mul_right_comm]
    exact mul_div_cancel_right₀ _ ((Weight.sobolev (1/2)).complex_ne_zero n)
  · change ((miuraCartesianWeight s n : ℂ)*z.1.2.val.val n)/(Weight.sobolev (1/2) n : ℂ) =
      (Weight.sobolev (s : ℝ) n : ℂ)*z.1.2.val.val n
    rw [miuraCartesianWeight_factor]
    push_cast
    rw [mul_right_comm]
    exact mul_div_cancel_right₀ _ ((Weight.sobolev (1/2)).complex_ne_zero n)

theorem miuraSobolevNormalizedCartesianMap_eval (s : ℕ) (a : ScalarSobolev s) (n : ℤ) :
    miuraPositiveCartesianEval n (miuraSobolevNormalizedCartesianMap s a) =
      (Weight.sobolev (s : ℝ) n : ℂ) • miuraSobolevPositiveEval s n (miuraSobolevPositiveCartesianMap s a) :=
  miuraPositiveSobolevWeightEquiv_eval s _ n

theorem miuraSobolevNormalizedCartesianMap_mean (s : ℕ) (a : ScalarSobolev s) :
    (miuraSobolevNormalizedCartesianMap s a).2 = a.val 0 :=
  miuraPositiveSobolevWeightEquiv_mean s _

/-- The actual physical H^s action flow is the standard selected-plane
rotation after normalization, as equality in the entire native target. -/
theorem miuraSobolevNormalizedCartesianMap_actionFlow (s : ℕ) (a : ScalarSobolev s)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    miuraSobolevNormalizedCartesianMap s (miuraActionFlow s a ha n t) =
      miuraCartesianRotation n t (miuraSobolevNormalizedCartesianMap s a) := by
  apply WeightedCoeff.positivePairMean_ext
  · intro k hk
    have hi : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk.le
    have hnat : 1 ≤ k.toNat := by omega
    have he := miuraSobolevPositiveCartesianMap_actionFlow_eval s a ha k.toNat n hnat hn t
    rw [hi] at he
    change miuraPositiveCartesianEval k (miuraSobolevNormalizedCartesianMap s (miuraActionFlow s a ha n t)) =
      miuraPositiveCartesianEval k (miuraCartesianRotation n t (miuraSobolevNormalizedCartesianMap s a))
    rw [miuraCartesianRotation_eval,miuraSobolevNormalizedCartesianMap_eval,
      miuraSobolevNormalizedCartesianMap_eval,he]
    by_cases hkn : k.toNat = n
    · have hkn' : k = (n : ℤ) := by omega
      rw [if_pos hkn,if_pos hkn',cartesianPlaneRotation_smul]
    · have hkn' : k ≠ (n : ℤ) := by omega
      rw [if_neg hkn,if_neg hkn']
  · rw [miuraCartesianRotation_mean,miuraSobolevNormalizedCartesianMap_mean,miuraSobolevNormalizedCartesianMap_mean]
    exact miuraActionFlow_mean_allSobolev s a ha n t

end NLS.MKdV
