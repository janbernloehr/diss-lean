import NLS.KdV.PseudomeasureCoefficients

/-!
# Compatibility of the actual tail inverse with spectral-weight inclusions

All maps retain the raw coefficients and the entire original H-minus-one
distribution. Uniqueness identifies the weighted solved tails with the same
physical unit-weight tails; no weighted characteristic is substituted.
-/
noncomputable section
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue

/-- A norm-decreasing inclusion between two negative-order endpoint carriers. -/
def endpointWeightInclusion (w v : SpectralWeight) (h : ∀ k, v k ≤ w k) (r : ℝ) :
    WeightedCoeff (w.negativeSobolev r) ⊤ →L[ℂ] WeightedCoeff (v.negativeSobolev r) ⊤ :=
  WeightedCoeff.inclusionCLM _ _ (fun k => div_le_div_of_nonneg_right (h k)
    ((Weight.sobolev r).positive k).le)

@[simp] theorem endpointWeightInclusion_apply (w v : SpectralWeight) (h : ∀ k, v k ≤ w k)
    (r : ℝ) (q : WeightedCoeff (w.negativeSobolev r) ⊤) (k : ℤ) :
    (endpointWeightInclusion w v h r q).val k = q.val k :=
  WeightedCoeff.inclusionCLM_apply _ _ _ q k

theorem norm_endpointWeightInclusion_le (w v : SpectralWeight) (h : ∀ k, v k ≤ w k)
    (r : ℝ) (q : WeightedCoeff (w.negativeSobolev r) ⊤) :
    ‖endpointWeightInclusion w v h r q‖ ≤ ‖q‖ :=
  WeightedCoeff.norm_inclusionCLM_le _ _ _ q

/-- The original H-minus-one potential is literally unchanged by weight inclusion. -/
theorem endpointHillHminusOne_weightInclusion (w v : SpectralWeight) (h : ∀ k, v k ≤ w k)
    (r : ℝ) (hr1 : r < 1/2) (q : WeightedCoeff (w.negativeSobolev r) ⊤) :
    endpointHillHminusOne v r hr1 (endpointWeightInclusion w v h r q) =
      endpointHillHminusOne w r hr1 q := by
  apply Subtype.ext
  apply Distribution.ext_coefficients
  intro k
  rw [endpointHillHminusOne_coefficient, endpointHillHminusOne_coefficient,
    endpointWeightInclusion_apply]

/-- All reduced physical H1 resolvents are the same original distribution on included data. -/
theorem endpointReducedHillResolventH1Original_weightInclusion (w v : SpectralWeight)
    (h : ∀ k, v k ≤ w k) (r : ℝ) (hr1 : r < 1/2) (n : ℕ) (hn : 1 ≤ n)
    (z : ℂ) (hz : z ∈ reducedHillStrip n) (f : WeightedCoeff (w.negativeSobolev r) ⊤) :
    endpointReducedHillResolventH1Original v r hr1 n hn z hz (endpointWeightInclusion w v h r f) =
      endpointReducedHillResolventH1Original w r hr1 n hn z hz f := by
  apply Subtype.ext
  apply Distribution.ext_coefficients
  intro k
  rw [endpointReducedHillResolventH1Original_coefficient,
    endpointReducedHillResolventH1Original_coefficient, endpointWeightInclusion_apply]

/-- The actual Fourier perturbation commutes with every coefficient-preserving weight inclusion. -/
theorem unshiftedEndpointHillPerturbation_weightInclusion (w v : SpectralWeight)
    (h : ∀ k, v k ≤ w k) (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (q f : WeightedCoeff (w.negativeSobolev r) ⊤) :
    endpointWeightInclusion w v h r (unshiftedEndpointHillPerturbation w r hr hr1 n hn z hz q f) =
      unshiftedEndpointHillPerturbation v r hr hr1 n hn z hz
        (endpointWeightInclusion w v h r q) (endpointWeightInclusion w v h r f) := by
  apply Subtype.ext
  funext k
  simp only [endpointWeightInclusion_apply, unshiftedEndpointHillPerturbation_apply]

/-- An explicit contraction bound survives every norm-decreasing weight inclusion. -/
theorem endpointHill_small_weightInclusion (w v : SpectralWeight) (h : ∀ k, v k ≤ w k)
    (r : ℝ) (hr1 : r < 1/2) (n : ℕ) (q : WeightedCoeff (w.negativeSobolev r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) :
    endpointHillConstant r*(n:ℝ)^(r-1/2)*‖endpointWeightInclusion w v h r q‖ ≤ 1/2 :=
  (mul_le_mul_of_nonneg_left (norm_endpointWeightInclusion_le w v h r q)
    (by positivity [endpointHillConstant_pos r hr1])).trans hs

/-- Weighted and weaker-weight solved tails coincide coefficient by coefficient,
by uniqueness of the actual tail equation. -/
theorem endpointHillTailInverse_weightInclusion (w v : SpectralWeight) (h : ∀ k, v k ≤ w k)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2) (n : ℕ) (hn : 1 ≤ n)
    (z : ℂ) (hz : z ∈ reducedHillStrip n) (q : WeightedCoeff (w.negativeSobolev r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)
    (hv : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖endpointWeightInclusion w v h r q‖ ≤ 1/2)
    (f : WeightedCoeff (w.negativeSobolev r) ⊤) :
    endpointWeightInclusion w v h r (endpointHillTailInverse w r hr hr1 n hn z hz q hs f) =
      endpointHillTailInverse v r hr hr1 n hn z hz (endpointWeightInclusion w v h r q) hv
        (endpointWeightInclusion w v h r f) := by
  apply endpointHillTailInverse_unique v r hr hr1 n hn z hz _ hv
  have he := congrArg (endpointWeightInclusion w v h r)
    (endpointHillTailInverse_right w r hr hr1 n hn z hz q hs f)
  rwa [map_sub, unshiftedEndpointHillPerturbation_weightInclusion] at he

/-- Fourier modulation is preserved exactly by weight inclusion. -/
theorem negativeModulation_weightInclusion (w v : SpectralWeight) (h : ∀ k, v k ≤ w k)
    (r : ℝ) (hr : 0 ≤ r) (j : ℤ) (q : WeightedCoeff (w.negativeSobolev r) ⊤) :
    endpointWeightInclusion w v h r (w.negativeModulation r hr j q) =
      v.negativeModulation r hr j (endpointWeightInclusion w v h r q) := by
  apply Subtype.ext
  funext k
  simp only [endpointWeightInclusion_apply, SpectralWeight.negativeModulation_apply]

/-- The corrected resonant modes are the SAME solved physical coefficients in every weight. -/
theorem endpointHillCorrectedMode_weightInclusion (w v : SpectralWeight) (h : ∀ k, v k ≤ w k)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2) (n : ℕ) (hn : 1 ≤ n)
    (z : ℂ) (hz : z ∈ reducedHillStrip n) (q : WeightedCoeff (w.negativeSobolev r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)
    (hv : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖endpointWeightInclusion w v h r q‖ ≤ 1/2) (j : ℤ) :
    endpointWeightInclusion w v h r (endpointHillCorrectedMode w r hr hr1 n hn z hz q hs j) =
      endpointHillCorrectedMode v r hr hr1 n hn z hz (endpointWeightInclusion w v h r q) hv j := by
  unfold endpointHillCorrectedMode
  rw [endpointHillTailInverse_weightInclusion w v h r hr hr1 n hn z hz q hs hv,
    negativeModulation_weightInclusion]

end NLS.KdV
