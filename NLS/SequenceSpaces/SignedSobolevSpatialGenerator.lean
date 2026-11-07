import NLS.SequenceSpaces.SignedSobolevWeight

/-! The original physical2*pi spatial generator drops one full signed
Sobolev order, with literal max(1,abs(k)) weights at every real order. -/
noncomputable section
open Complex
open scoped ENNReal
namespace NLS.Weight

theorem signedSobolev_spatialGenerator_bound (s : ℝ) (k : ℤ) :
    signedSobolev s k*‖I*((2*Real.pi*k:ℝ):ℂ)‖ ≤ (2*Real.pi)*signedSobolev (s+1) k := by
  have hb : 0<max (1:ℝ) |(k:ℝ)| := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hn : ‖I*((2*Real.pi*k:ℝ):ℂ)‖=(2*Real.pi)*|(k:ℝ)| := by
    rw [norm_mul,norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_mul,
      abs_of_pos (by norm_num : (0:ℝ)<2),abs_of_pos Real.pi_pos]
  rw [hn]
  change (max (1:ℝ) |(k:ℝ)|)^s*((2*Real.pi)*|(k:ℝ)|) ≤
    (2*Real.pi)*(max (1:ℝ) |(k:ℝ)|)^(s+1)
  rw [Real.rpow_add hb,Real.rpow_one]
  have hw : 0 ≤ (max (1:ℝ) |(k:ℝ)|)^s := (Real.rpow_pos_of_pos hb s).le
  calc
    _ = (2*Real.pi)*((max (1:ℝ) |(k:ℝ)|)^s * |(k:ℝ)|) := by ring
    _ ≤ (2*Real.pi)*((max (1:ℝ) |(k:ℝ)|)^s*max (1:ℝ) |(k:ℝ)|) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (le_max_right (1:ℝ) |(k:ℝ)|) hw) (by positivity)

end NLS.Weight
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Exact physical spatial generator on the full signed weighted scale. -/
def signedSpatialGenerator (s : ℝ) :
    WeightedCoeff (Weight.signedSobolev (s+1)) p →L[ℂ] WeightedCoeff (Weight.signedSobolev s) p :=
  weightedMultiplierCLM _ _ (fun k => I*((2*Real.pi*k:ℝ):ℂ)) (2*Real.pi)
    (by positivity) (Weight.signedSobolev_spatialGenerator_bound s)

theorem signedSpatialGenerator_apply (s : ℝ)
    (a : WeightedCoeff (Weight.signedSobolev (s+1)) p) (k : ℤ) :
    (signedSpatialGenerator s a).val k=I*((2*Real.pi*k:ℝ):ℂ)*a.val k := rfl

theorem norm_signedSpatialGenerator_le (s : ℝ)
    (a : WeightedCoeff (Weight.signedSobolev (s+1)) p) :
    ‖signedSpatialGenerator s a‖ ≤ (2*Real.pi)*‖a‖ :=
  norm_weightedMultiplier_le _ _ _ _ (by positivity) (Weight.signedSobolev_spatialGenerator_bound s) a

end NLS.WeightedCoeff
