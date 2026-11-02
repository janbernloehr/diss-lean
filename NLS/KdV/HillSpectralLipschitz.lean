import NLS.KdV.HillWeightedCoefficients

/-!
# Spectral Lipschitz bounds for the Hill correction

The complementary resolvent identity gives a global Lipschitz bound on
each closed high-frequency strip. This controls the diagonal variation
needed for root separation without making a choice of a square-root branch.
-/

noncomputable section
open scoped ENNReal
namespace NLS.KdV

theorem shiftedNorm_weightedReducedHillResolvent_le (w : SpectralWeight) (i : ℤ)
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (a : WeightedCoeff w.toWeight 2) :
    w.shiftedNorm i (weightedReducedHillResolvent w.toWeight n hn z hz a) ≤
      (n : ℝ)⁻¹*w.shiftedNorm i a := by
  have he : w.toShift i (weightedReducedHillResolvent w.toWeight n hn z hz a) =
      weightedReducedHillResolvent (w.toWeight.shift i) n hn z hz (w.toShift i a) := by
    apply Subtype.ext
    funext k
    simp only [SpectralWeight.toShift_apply, weightedReducedHillResolvent_apply]
  change ‖w.toShift i _‖ ≤ _
  rw [he]
  exact norm_weightedReducedHillResolvent_apply_le _ n hn z hz _

/-- The actual complementary Fourier multiplier satisfies the resolvent identity. -/
theorem hillComplementToL1_sub (w : Weight) (n : ℕ) (hn : 1 ≤ n)
    (z y : ℂ) (hz : z ∈ reducedHillStrip n) (hy : y ∈ reducedHillStrip n)
    (a : WeightedCoeff w 2) :
    hillComplementToL1 w n hn z hz a-hillComplementToL1 w n hn y hy a =
      (y-z) • hillComplementToL1 w n hn z hz (weightedReducedHillResolvent w n hn y hy a) := by
  apply Subtype.ext
  funext k
  simp only [WeightedCoeff.sub_val, WeightedCoeff.smul_val, hillComplementToL1_apply,
    weightedReducedHillResolvent_apply]
  split_ifs with hk
  · simp
  · field_simp [freeHill_denominator_ne_zero hn hz hk, freeHill_denominator_ne_zero hn hy hk]
    ring

theorem shiftedNorm_hillComplementToL1_sub_le (w : SpectralWeight) (i : ℤ)
    (n : ℕ) (hn : 1 ≤ n) (z y : ℂ)
    (hz : z ∈ reducedHillStrip n) (hy : y ∈ reducedHillStrip n)
    (a : WeightedCoeff w.toWeight 2) :
    w.shiftedNorm i (hillComplementToL1 w.toWeight n hn z hz a-
      hillComplementToL1 w.toWeight n hn y hy a) ≤
      (4/(n : ℝ)^2)*‖z-y‖*w.shiftedNorm i a := by
  rw [hillComplementToL1_sub]
  change ‖w.toShift i ((y-z) • _)‖ ≤ _
  rw [map_smul, norm_smul, norm_sub_rev]
  calc
    _ ≤ ‖z-y‖*((4/(n : ℝ))*w.shiftedNorm i
        (weightedReducedHillResolvent w.toWeight n hn y hy a)) :=
      mul_le_mul_of_nonneg_left (shiftedNorm_hillComplementToL1_le w i n hn z hz _) (norm_nonneg _)
    _ ≤ ‖z-y‖*((4/(n : ℝ))*((n : ℝ)⁻¹*w.shiftedNorm i a)) := by
      gcongr
      exact shiftedNorm_weightedReducedHillResolvent_le w i n hn y hy a
    _ = _ := by ring

theorem shiftedNorm_hillTailPerturbation_sub_le (w : SpectralWeight) (i : ℤ)
    (q : WeightedCoeff w.toWeight 2) (n : ℕ) (hn : 1 ≤ n) (z y : ℂ)
    (hz : z ∈ reducedHillStrip n) (hy : y ∈ reducedHillStrip n)
    (a : WeightedCoeff w.toWeight 2) :
    w.shiftedNorm i (hillTailPerturbation w q n hn z hz a-
      hillTailPerturbation w q n hn y hy a) ≤
      (4*‖q‖/(n : ℝ)^2)*‖z-y‖*w.shiftedNorm i a := by
  change w.shiftedNorm i ((w.convolutionCLM q) _-(w.convolutionCLM q) _) ≤ _
  rw [← map_sub]
  apply (w.shiftedNorm_convolution_le i q _).trans
  calc
    _ ≤ ‖q‖*((4/(n : ℝ)^2)*‖z-y‖*w.shiftedNorm i a) :=
      mul_le_mul_of_nonneg_left (shiftedNorm_hillComplementToL1_sub_le w i n hn z y hz hy a)
        (norm_nonneg q)
    _ = _ := by ring

theorem hillTailInverse_sub (w : SpectralWeight) (q : WeightedCoeff w.toWeight 2)
    (n : ℕ) (hn : 1 ≤ n) (z y : ℂ)
    (hz : z ∈ reducedHillStrip n) (hy : y ∈ reducedHillStrip n)
    (hcut : 8*‖q‖ ≤ (n : ℝ)) (b : WeightedCoeff w.toWeight 2) :
    hillTailInverse w q n hn z hz hcut b-hillTailInverse w q n hn y hy hcut b =
      hillTailInverse w q n hn z hz hcut
        (hillTailPerturbation w q n hn z hz (hillTailInverse w q n hn y hy hcut b)-
          hillTailPerturbation w q n hn y hy (hillTailInverse w q n hn y hy hcut b)) := by
  apply hillTailInverse_unique
  rw [map_sub]
  have hz' := hillTailInverse_right w q n hn z hz hcut b
  have hy' := hillTailInverse_right w q n hn y hy hcut b
  calc
    _ = (hillTailInverse w q n hn z hz hcut b-
          hillTailPerturbation w q n hn z hz (hillTailInverse w q n hn z hz hcut b))-
        (hillTailInverse w q n hn y hy hcut b-
          hillTailPerturbation w q n hn y hy (hillTailInverse w q n hn y hy hcut b))+
        (hillTailPerturbation w q n hn z hz (hillTailInverse w q n hn y hy hcut b)-
          hillTailPerturbation w q n hn y hy (hillTailInverse w q n hn y hy hcut b)) := by abel
    _ = _ := by rw [hz', hy']; abel

/-- Uniform spectral variation of the corrected unit mode. -/
theorem shiftedNorm_hillCorrectedMode_sub_le (w : SpectralWeight)
    (q : WeightedCoeff w.toWeight 2) (n : ℕ) (hn : 1 ≤ n) (z y : ℂ)
    (hz : z ∈ reducedHillStrip n) (hy : y ∈ reducedHillStrip n)
    (hcut : 8*‖q‖ ≤ (n : ℝ)) (j : ℤ) :
    w.shiftedNorm (-j) (hillCorrectedMode w q n hn z hz hcut j-
      hillCorrectedMode w q n hn y hy hcut j) ≤ (16*‖q‖^2/(n : ℝ)^2)*‖z-y‖ := by
  unfold hillCorrectedMode
  rw [hillTailInverse_sub]
  apply (shiftedNorm_hillTailInverse_le w (-j) q n hn z hz hcut _).trans
  calc
    _ ≤ 2*((4*‖q‖/(n : ℝ)^2)*‖z-y‖*w.shiftedNorm (-j)
        (hillCorrectedMode w q n hn y hy hcut j)) := by
      gcongr
      exact shiftedNorm_hillTailPerturbation_sub_le w (-j) q n hn z y hz hy _
    _ ≤ 2*((4*‖q‖/(n : ℝ)^2)*‖z-y‖*(2*‖q‖)) := by
      gcongr
      exact shiftedNorm_hillCorrectedMode_le w q n hn y hy hcut j
    _ = _ := by ring

theorem hillDiagonal_sub_le (w : SpectralWeight) (q : WeightedCoeff w.toWeight 2)
    (n : ℕ) (hn : 1 ≤ n) (z y : ℂ)
    (hz : z ∈ reducedHillStrip n) (hy : y ∈ reducedHillStrip n)
    (hcut : 8*‖q‖ ≤ (n : ℝ)) :
    ‖hillDiagonal w q n hn z hz hcut-hillDiagonal w q n hn y hy hcut‖ ≤
      (16*‖q‖^2/(n : ℝ)^2)*‖z-y‖ := by
  have hc := shiftedNorm_coefficient_le w (-(n : ℤ)) n
    (hillCorrectedMode w q n hn z hz hcut n-hillCorrectedMode w q n hn y hy hcut n)
  simp only [add_neg_cancel, WeightedCoeff.sub_val] at hc
  have hb := mul_le_mul_of_nonneg_right (w.one_le 0)
    (norm_nonneg (hillDiagonal w q n hn z hz hcut-hillDiagonal w q n hn y hy hcut))
  simp only [one_mul] at hb
  exact (hb.trans hc).trans (shiftedNorm_hillCorrectedMode_sub_le w q n hn z y hz hy hcut n)

theorem hillDiagonal_sub_le_quarter (w : SpectralWeight) (q : WeightedCoeff w.toWeight 2)
    (n : ℕ) (hn : 1 ≤ n) (z y : ℂ)
    (hz : z ∈ reducedHillStrip n) (hy : y ∈ reducedHillStrip n)
    (hcut : 8*‖q‖ ≤ (n : ℝ)) :
    ‖hillDiagonal w q n hn z hz hcut-hillDiagonal w q n hn y hy hcut‖ ≤ (1/4 : ℝ)*‖z-y‖ := by
  apply (hillDiagonal_sub_le w q n hn z y hz hy hcut).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply (div_le_iff₀ (sq_pos_of_pos (show (0 : ℝ) < n by exact_mod_cast (show 0 < n by omega)))).mpr
  nlinarith [sq_nonneg ((n : ℝ)-8*‖q‖), mul_nonneg (sub_nonneg.mpr hcut)
    (show 0 ≤ (n : ℝ)+8*‖q‖ by positivity)]

end NLS.KdV
