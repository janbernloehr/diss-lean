import NLS.MKdV.MiuraNativeActionMeanParameters
import NLS.MKdV.MiuraCartesianRealActionData
import NLS.MKdV.MiuraExponentialActionEncoding

/-! # Every nonnegative encoded native action datum has a real profile

Native normalization makes every nonnegative l1 datum admissible at the
chosen Sobolev order. The auxiliary exponential coordinate decodes the
literal signed mean. No finite-support restriction is needed here.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV
local instance : (2 : ℝ≥0∞).HolderTriple 2 1 := (ENNReal.holderTriple_iff _ _ _).mpr (by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_add])

theorem miuraLogActionParameters_exponential_cartesian (z : MiuraRealCartesianTarget) :
    miuraLogActionParameters (miuraExponentialActionParameters (miuraPositiveCartesianActionMean z.val)) =
      miuraPositiveCartesianActionMean z.val :=
  miuraLogActionParameters_exponential _ (miuraCartesian_actionMean_nonpositive z.val) z.property.2

theorem miuraExponentialActionParameters_cartesian_slitPlane (z : MiuraRealCartesianTarget) :
    miuraExponentialActionParameters (miuraPositiveCartesianActionMean z.val) 0 ∈ Complex.slitPlane := by
  rw [miuraExponentialActionParameters_zero]
  have hreal : (miuraPositiveCartesianActionMean z.val).2 = ((miuraPositiveCartesianActionMean z.val).2.re : ℂ) := by
    apply Complex.ext
    · rfl
    · change z.val.2.im = 0
      exact z.property.2
  rw [hreal,← Complex.ofReal_exp]
  exact Complex.ofReal_mem_slitPlane.mpr (Real.exp_pos _)

theorem miuraExponentialActionParameters_cartesian_nonnegative (z : MiuraRealCartesianTarget) :
    miuraExponentialActionParameters (miuraPositiveCartesianActionMean z.val) ∈ Coeff.nonnegativeLocus 1 := by
  intro n
  rw [miuraExponentialActionParameters_apply]
  by_cases hn : 0 < n
  · rw [if_pos hn]
    exact miuraCartesian_normalized_actions_nonnegative z n
  · rw [if_neg hn]
    by_cases hz : n = 0
    · rw [if_pos hz]
      have hm : (miuraPositiveCartesianActionMean z.val).2.im = 0 := z.property.2
      simp only [Complex.exp_re,Complex.exp_im,hm,Real.cos_zero,Real.sin_zero,mul_one,mul_zero]
      exact ⟨trivial,(Real.exp_pos _).le⟩
    · simp only [if_neg hz,Complex.zero_im,Complex.zero_re,le_refl,and_self]

theorem exists_native_profile_of_normalized_Cartesian (s : ℕ) (hs : 1 ≤ s) (z : MiuraRealCartesianTarget) :
    ∃ a : MiuraRealSobolevSource s, miuraSobolevNormalizedCartesianMap s a.val = z.val := by
  let E := miuraSobolevCartesianRealWeightEquiv s
  let a := miuraPhysicalSobolevCartesianInverse s hs (E.symm z)
  have h : miuraPhysicalSobolevNormalizedCartesianMap s a = z := by
    change E (miuraPhysicalSobolevCartesianMap s (miuraPhysicalSobolevCartesianInverse s hs (E.symm z))) = z
    rw [miuraPhysicalSobolevCartesianMap_inverse,ContinuousLinearEquiv.apply_symm_apply]
  refine ⟨a,?_⟩
  rw [← miuraPhysicalSobolevNormalizedCartesianMap_inclusion]
  exact congrArg Subtype.val h

theorem exists_real_Cartesian_of_nonnegative_encoded (q : Coeff 1) (hpos : q ∈ Coeff.nonnegativeLocus 1) :
    ∃ z : MiuraRealCartesianTarget, miuraPositiveCartesianActionMean z.val = miuraLogActionParameters q := by
  let b := miuraLogActionParameters q
  let J := WeightedCoeff.weightIsometry (Weight.sobolev 1) 1 b.1
  have hJ : J ∈ Coeff.nonnegativeLocus 1 := by
    intro n
    change (((Weight.sobolev 1 n : ℂ)*b.1.val n).im = 0) ∧
      0 ≤ ((Weight.sobolev 1 n : ℂ)*b.1.val n).re
    rw [miuraLogActionParameters_apply]
    by_cases hn : 0 < n
    · rw [if_pos hn,mul_div_cancel₀ _ ((Weight.sobolev 1).complex_ne_zero n)]
      exact hpos n
    · simp only [if_neg hn,mul_zero,Complex.zero_im,Complex.zero_re,le_refl,and_self]
  obtain ⟨u,hu,hquad,_⟩ := Coeff.exists_real_quadraticActions_lift (p := 2) (by simp) J hJ
  have hzero : ∀ n : ℤ, ¬0 < n → b.1.val n = 0 := by
    intro n hn
    rw [miuraLogActionParameters_apply,if_neg hn]
  have hlog : b.2.im = 0 := by
    have he : q 0 = ((q 0).re : ℂ) := by apply Complex.ext <;> simp [(hpos 0).1]
    change (Complex.log (q 0)).im = 0
    rw [he,← Complex.ofReal_log (hpos 0).2]
    rfl
  refine ⟨⟨miuraCartesianFromPairMean (u,b.2),miuraCartesianFromPairMean_real u hu b.2 hlog⟩,?_⟩
  exact miuraCartesianFromPairMean_action_of_quadratic_data u b hzero hquad

/-- Every nonnegative full encoded datum, with arbitrary infinite
support, is realized at every chosen native integer Sobolev order. -/
theorem exists_native_profile_of_nonnegative_encoded (s : ℕ) (hs : 1 ≤ s)
    (q : Coeff 1) (hpos : q ∈ Coeff.nonnegativeLocus 1) :
    ∃ a : MiuraRealSobolevSource s, miuraNormalizedNativeActionMeanMap s a.val = miuraLogActionParameters q := by
  obtain ⟨z,hz⟩ := exists_real_Cartesian_of_nonnegative_encoded q hpos
  obtain ⟨a,ha⟩ := exists_native_profile_of_normalized_Cartesian s hs z
  refine ⟨a,?_⟩
  rw [← miuraNormalizedCartesian_actionMean s a.val a.property,ha]
  exact hz

end NLS.MKdV
