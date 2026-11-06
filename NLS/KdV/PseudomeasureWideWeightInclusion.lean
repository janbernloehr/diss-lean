import NLS.KdV.PseudomeasureWideCoefficients

/-! Every weighted wide tail is the same original physical solved tail. -/
noncomputable section
open scoped ENNReal
namespace NLS.KdV

/-- The actual Fourier perturbation commutes with every coefficient-preserving weight inclusion. -/
theorem wideEndpointHillPerturbation_weightInclusion (w v : SpectralWeight)
    (h : ∀ k, v k ≤ w k) (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 2 ≤ n) (z : ℂ) (hz : z ∈ wideHillStrip n)
    (q f : WeightedCoeff (w.negativeSobolev r) ⊤) :
    endpointWeightInclusion w v h r (wideEndpointHillPerturbation w r hr hr1 n hn z hz q f) =
      wideEndpointHillPerturbation v r hr hr1 n hn z hz
        (endpointWeightInclusion w v h r q) (endpointWeightInclusion w v h r f) := by
  apply Subtype.ext
  funext k
  simp only [endpointWeightInclusion_apply, wideEndpointHillPerturbation_apply]

/-- An explicit contraction bound survives every norm-decreasing weight inclusion. -/
theorem wideEndpointHill_small_weightInclusion (w v : SpectralWeight) (h : ∀ k, v k ≤ w k)
    (r : ℝ) (hr1 : r < 1/2) (n : ℕ) (q : WeightedCoeff (w.negativeSobolev r) ⊤)
    (hs : 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) :
    13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖endpointWeightInclusion w v h r q‖ ≤ 1/2 :=
  (mul_le_mul_of_nonneg_left (norm_endpointWeightInclusion_le w v h r q)
    (by positivity [endpointHillConstant_pos r hr1])).trans hs

/-- Weighted and weaker-weight solved tails coincide coefficient by coefficient,
by uniqueness of the actual tail equation. -/
theorem wideEndpointHillTailInverse_weightInclusion (w v : SpectralWeight) (h : ∀ k, v k ≤ w k)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2) (n : ℕ) (hn : 2 ≤ n)
    (z : ℂ) (hz : z ∈ wideHillStrip n) (q : WeightedCoeff (w.negativeSobolev r) ⊤)
    (hs : 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)
    (hv : 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖endpointWeightInclusion w v h r q‖ ≤ 1/2)
    (f : WeightedCoeff (w.negativeSobolev r) ⊤) :
    endpointWeightInclusion w v h r (wideEndpointHillTailInverse w r hr hr1 n hn z hz q hs f) =
      wideEndpointHillTailInverse v r hr hr1 n hn z hz (endpointWeightInclusion w v h r q) hv
        (endpointWeightInclusion w v h r f) := by
  apply wideEndpointHillTailInverse_unique v r hr hr1 n hn z hz _ hv
  have he := congrArg (endpointWeightInclusion w v h r)
    (wideEndpointHillTailInverse_right w r hr hr1 n hn z hz q hs f)
  rwa [map_sub, wideEndpointHillPerturbation_weightInclusion] at he

/-- The corrected resonant modes are the SAME solved physical coefficients in every weight. -/
theorem wideEndpointHillCorrectedMode_weightInclusion (w v : SpectralWeight) (h : ∀ k, v k ≤ w k)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2) (n : ℕ) (hn : 2 ≤ n)
    (z : ℂ) (hz : z ∈ wideHillStrip n) (q : WeightedCoeff (w.negativeSobolev r) ⊤)
    (hs : 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)
    (hv : 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖endpointWeightInclusion w v h r q‖ ≤ 1/2) (j : ℤ) :
    endpointWeightInclusion w v h r (wideEndpointHillCorrectedMode w r hr hr1 n hn z hz q hs j) =
      wideEndpointHillCorrectedMode v r hr hr1 n hn z hz (endpointWeightInclusion w v h r q) hv j := by
  unfold wideEndpointHillCorrectedMode
  rw [wideEndpointHillTailInverse_weightInclusion w v h r hr hr1 n hn z hz q hs hv,
    negativeModulation_weightInclusion]

end NLS.KdV
