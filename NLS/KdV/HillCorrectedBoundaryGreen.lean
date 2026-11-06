import NLS.KdV.HillFreeBoundaryGreen
import NLS.KdV.HillUnitWeightLift

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal Classical

namespace NLS.KdV



/-- The free boundary complement in the existing unit-weight reduction space. -/
def hillUnitFreeBoundaryGreen (n : ℕ) (r : ℤ) (z : ℂ) :
    WeightedCoeff SpectralWeight.one.toWeight 1 :=
  hillUnitWeightLift 1 (hillFreeBoundaryGreen n r z)

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2) (n : ℕ) (hn : 1 ≤ n)
  (r : ℤ) (z : ℂ) (hz : z ∈ reducedHillStrip n) (hcut : 8*‖q‖ ≤ (n : ℝ))

/-- Correct the potential of the summable free boundary source, not the
constant source itself, which is not an l2 vector. -/
def hillBoundaryGreenPotential : WeightedCoeff SpectralWeight.one.toWeight 2 :=
  hillTailInverse SpectralWeight.one q n hn z hz hcut
    (SpectralWeight.one.convolution q (hillUnitFreeBoundaryGreen n r z))

/-- The genuine complementary boundary Green vector for the perturbed operator. -/
def hillCorrectedBoundaryGreen : WeightedCoeff SpectralWeight.one.toWeight 1 :=
  hillUnitFreeBoundaryGreen n r z +
    hillComplementToL1 SpectralWeight.one.toWeight n hn z hz
      (hillBoundaryGreenPotential q n hn r z hz hcut)

/-- Its original potential is exactly the corrected potential constructed above. -/
theorem convolution_hillCorrectedBoundaryGreen :
    SpectralWeight.one.convolution q (hillCorrectedBoundaryGreen q n hn r z hz hcut) =
      hillBoundaryGreenPotential q n hn r z hz hcut := by
  have hh := hillTailInverse_right SpectralWeight.one q n hn z hz hcut
    (SpectralWeight.one.convolution q (hillUnitFreeBoundaryGreen n r z))
  change hillBoundaryGreenPotential q n hn r z hz hcut -
    SpectralWeight.one.convolution q
      (hillComplementToL1 SpectralWeight.one.toWeight n hn z hz
        (hillBoundaryGreenPotential q n hn r z hz hcut)) = _ at hh
  rw [hillCorrectedBoundaryGreen,SpectralWeight.convolution_add_right,← hh]
  abel

/-- Both actual resonant coefficients of the corrected Green vector vanish. -/
theorem hillModeCoordinates_correctedBoundaryGreen :
    hillModeCoordinates SpectralWeight.one.toWeight 1 n
      (hillCorrectedBoundaryGreen q n hn r z hz hcut) = 0 := by
  ext <;> simp [hillModeCoordinates_apply,hillCorrectedBoundaryGreen,
    hillUnitFreeBoundaryGreen,hillFreeBoundaryGreen_apply n hn r z hz,hillComplementToL1_apply]

/-- The complementary equation includes precisely the selected constant source. -/
theorem hillCorrectedBoundaryGreen_complement_equation (k : ℤ) (hk : k.natAbs ≠ n) :
    (z-(freeHillValue k : ℂ))*(hillCorrectedBoundaryGreen q n hn r z hz hcut).val k =
      (hillBoundaryGreenPotential q n hn r z hz hcut).val k +
        if k%2=r%2 then 1 else 0 := by
  simp only [hillCorrectedBoundaryGreen,WeightedCoeff.add_val,hillUnitFreeBoundaryGreen,
    hillUnitWeightLift_apply,hillComplementToL1_apply,if_neg hk,mul_add,
    ← mul_assoc,mul_inv_cancel₀ (freeHill_denominator_ne_zero hn hz hk),one_mul]
  rw [hillFreeBoundaryGreen_equation n hn r z hz,if_neg hk]
  exact add_comm _ _

/-- Uniform control of the corrected boundary potential. -/
theorem norm_hillBoundaryGreenPotential_le :
    ‖hillBoundaryGreenPotential q n hn r z hz hcut‖ ≤ 8*‖q‖ := by
  have hG : ‖hillUnitFreeBoundaryGreen n r z‖ ≤ 4 := by
    simpa only [hillUnitFreeBoundaryGreen,norm_hillUnitWeightLift] using norm_hillFreeBoundaryGreen_le n hn r z hz
  calc
    _ ≤ ‖hillTailInverse SpectralWeight.one q n hn z hz hcut‖ *
        ‖SpectralWeight.one.convolution q (hillUnitFreeBoundaryGreen n r z)‖ :=
      (hillTailInverse SpectralWeight.one q n hn z hz hcut).le_opNorm _
    _ ≤ 2*(‖q‖*4) := mul_le_mul (norm_hillTailInverse_le SpectralWeight.one q n hn z hz hcut)
      ((SpectralWeight.one.norm_convolution_le _ _).trans
        (mul_le_mul_of_nonneg_left hG (norm_nonneg _))) (norm_nonneg _) (by norm_num)
    _ = _ := by ring

theorem norm_hillCorrectedBoundaryGreen_sub_free_le :
    ‖hillCorrectedBoundaryGreen q n hn r z hz hcut-hillUnitFreeBoundaryGreen n r z‖ ≤
      32*‖q‖/(n : ℝ) := by
  rw [hillCorrectedBoundaryGreen,add_sub_cancel_left]
  calc
    _ ≤ (4/(n : ℝ))*‖hillBoundaryGreenPotential q n hn r z hz hcut‖ :=
      norm_hillComplementToL1_apply_le _ n hn z hz _
    _ ≤ (4/(n : ℝ))*(8*‖q‖) :=
      mul_le_mul_of_nonneg_left (norm_hillBoundaryGreenPotential_le q n hn r z hz hcut) (by positivity)
    _ = _ := by ring

/-- One explicit high-frequency cutoff controls every complex boundary block. -/
theorem norm_hillCorrectedBoundaryGreen_le :
    ‖hillCorrectedBoundaryGreen q n hn r z hz hcut‖ ≤ 8 := by
  have hG : ‖hillUnitFreeBoundaryGreen n r z‖ ≤ 4 := by
    simpa only [hillUnitFreeBoundaryGreen,norm_hillUnitWeightLift] using norm_hillFreeBoundaryGreen_le n hn r z hz
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hc : 32*‖q‖/(n : ℝ) ≤ 4 := (div_le_iff₀ hnpos).mpr (by linarith)
  have hh := norm_le_norm_sub_add (hillCorrectedBoundaryGreen q n hn r z hz hcut)
    (hillUnitFreeBoundaryGreen n r z)
  linarith [norm_hillCorrectedBoundaryGreen_sub_free_le q n hn r z hz hcut]

end NLS.KdV
