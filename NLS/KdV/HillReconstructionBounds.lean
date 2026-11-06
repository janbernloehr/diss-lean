import NLS.KdV.HillWeightedCoefficients

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal Classical

namespace NLS.KdV



/-- Forgetting the weight is contractive in every shifted norm. -/
theorem norm_toCoeff_le_hillShiftedNorm (w : SpectralWeight) {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (i : ℤ) (a : WeightedCoeff w.toWeight p) :
    ‖w.toCoeff a‖ ≤ w.shiftedNorm i a := by
  calc
    ‖w.toCoeff a‖ = ‖Coeff.shift i (w.toCoeff a)‖ := (Coeff.norm_shift i _).symm
    _ = ‖w.toCoeff (w.modulation i a)‖ := by rw [w.toCoeff_modulation]
    _ ≤ ‖w.modulation i a‖ := w.norm_toCoeff_le _
    _ = w.shiftedNorm i a := w.norm_modulation i a

variable (w : SpectralWeight) (q : WeightedCoeff w.toWeight 2)
  (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
  (hcut : 8*‖q‖ ≤ (n : ℝ))

/-- The corrected Fourier wave, before imposing the resonant equations. -/
def hillCorrectedWaveCoefficients (j : ℤ) : WeightedCoeff w.toWeight 1 :=
  WeightedCoeff.single w.toWeight j 1 +
    hillComplementToL1 w.toWeight n hn z hz (hillCorrectedMode w q n hn z hz hcut j)

/-- The correction has a summable shifted weighted norm, uniformly in its signed mode. -/
theorem shiftedNorm_hillCorrectedWave_error_le (j : ℤ) :
    w.shiftedNorm (-j) (hillCorrectedWaveCoefficients w q n hn z hz hcut j -
      WeightedCoeff.single w.toWeight j 1) ≤ 8*‖q‖/(n : ℝ) := by
  rw [hillCorrectedWaveCoefficients, add_sub_cancel_left]
  calc
    _ ≤ (4/(n : ℝ))*w.shiftedNorm (-j) (hillCorrectedMode w q n hn z hz hcut j) :=
      shiftedNorm_hillComplementToL1_le w (-j) n hn z hz _
    _ ≤ (4/(n : ℝ))*(2*‖q‖) :=
      mul_le_mul_of_nonneg_left (shiftedNorm_hillCorrectedMode_le w q n hn z hz hcut j)
        (by positivity)
    _ = _ := by ring

theorem norm_hillCorrectedWave_error_le (j : ℤ) :
    ‖w.toCoeff (hillCorrectedWaveCoefficients w q n hn z hz hcut j -
      WeightedCoeff.single w.toWeight j 1)‖ ≤ 8*‖q‖/(n : ℝ) :=
  (norm_toCoeff_le_hillShiftedNorm w (-j) _).trans
    (shiftedNorm_hillCorrectedWave_error_le w q n hn z hz hcut j)

theorem hillReconstruct_pos_eq_correctedWave :
    hillReconstruct w q n hn z hz hcut (1,0) =
      hillCorrectedWaveCoefficients w q n hn z hz hcut n := by
  change hillModes w.toWeight n (1,0) + _ = _
  rw [hillCorrectedWaveCoefficients, hillCorrectedMode_pos]
  congr 1
  apply Subtype.ext
  funext k
  simp [hillModes_apply, WeightedCoeff.single_val, Pi.single_apply]

theorem hillReconstruct_neg_eq_correctedWave :
    hillReconstruct w q n hn z hz hcut (0,1) =
      hillCorrectedWaveCoefficients w q n hn z hz hcut (-(n : ℤ)) := by
  change hillModes w.toWeight n (0,1) + _ = _
  rw [hillCorrectedWaveCoefficients, hillCorrectedMode_neg]
  congr 1
  apply Subtype.ext
  funext k
  simp [hillModes_apply, WeightedCoeff.single_val, Pi.single_apply]

/-- Absolute convergence of the reconstructed remainder, with no frequency weight loss. -/
theorem norm_hillReconstruct_error_le (u : ℂ × ℂ) :
    ‖w.toCoeff (hillReconstruct w q n hn z hz hcut u - hillModes w.toWeight n u)‖ ≤
      (8*‖q‖/(n : ℝ))*(‖u.1‖+‖u.2‖) := by
  let T := w.toCoeff.comp (hillReconstruct w q n hn z hz hcut - hillModes w.toWeight n)
  have hpos : ‖T (1,0)‖ ≤ 8*‖q‖/(n : ℝ) := by
    change ‖w.toCoeff (hillReconstruct w q n hn z hz hcut (1,0) -
      hillModes w.toWeight n (1,0))‖ ≤ _
    rw [hillReconstruct_pos_eq_correctedWave]
    have he : hillModes w.toWeight n (1,0) = WeightedCoeff.single w.toWeight (n : ℤ) 1 := by
      apply Subtype.ext
      funext k
      simp [hillModes_apply, WeightedCoeff.single_val, Pi.single_apply]
    rw [he]
    exact norm_hillCorrectedWave_error_le w q n hn z hz hcut n
  have hneg : ‖T (0,1)‖ ≤ 8*‖q‖/(n : ℝ) := by
    change ‖w.toCoeff (hillReconstruct w q n hn z hz hcut (0,1) -
      hillModes w.toWeight n (0,1))‖ ≤ _
    rw [hillReconstruct_neg_eq_correctedWave]
    have he : hillModes w.toWeight n (0,1) = WeightedCoeff.single w.toWeight (-(n : ℤ)) 1 := by
      apply Subtype.ext
      funext k
      simp [hillModes_apply, WeightedCoeff.single_val, Pi.single_apply]
    rw [he]
    exact norm_hillCorrectedWave_error_le w q n hn z hz hcut (-(n : ℤ))
  have hu : u = u.1 • ((1,0) : ℂ × ℂ) + u.2 • ((0,1) : ℂ × ℂ) := by
    ext <;> simp
  change ‖T u‖ ≤ _
  calc
    ‖T u‖ = ‖u.1 • T (1,0) + u.2 • T (0,1)‖ := by
      conv_lhs => rw [hu, map_add, map_smul, map_smul]
    _ ≤ ‖u.1 • T (1,0)‖ + ‖u.2 • T (0,1)‖ := norm_add_le _ _
    _ = ‖u.1‖*‖T (1,0)‖ + ‖u.2‖*‖T (0,1)‖ := by rw [norm_smul, norm_smul]
    _ ≤ ‖u.1‖*(8*‖q‖/(n : ℝ)) + ‖u.2‖*(8*‖q‖/(n : ℝ)) :=
      add_le_add (mul_le_mul_of_nonneg_left hpos (norm_nonneg _))
        (mul_le_mul_of_nonneg_left hneg (norm_nonneg _))
    _ = _ := by ring

end NLS.KdV
