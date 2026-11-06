import NLS.KdV.HillDirichletGreenBoundary
import NLS.SequenceSpaces.TwoPoleReciprocalDecay
import NLS.SequenceSpaces.ExponentEmbedding

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal Classical

namespace NLS.KdV



theorem hillFreeBoundaryGreen_norm_apply_le_envelope (n : ℕ) (hn : 1 ≤ n) (r : ℤ)
    (z : ℂ) (hz : z ∈ reducedHillStrip n) (k : ℤ) :
    ‖hillFreeBoundaryGreen n r z k‖ ≤
      ‖Coeff.twoPoleReciprocalEnvelope n k‖ := by
  rw [hillFreeBoundaryGreen_apply n hn r z hz]
  by_cases hk : k.natAbs=n
  · simp only [if_pos hk,norm_zero]
    exact norm_nonneg _
  rw [if_neg hk]
  by_cases hpar : k%2=r%2
  · rw [if_pos hpar,Coeff.twoPoleReciprocalEnvelope_apply,norm_mul,norm_inv,norm_inv,
      norm_inv,Complex.norm_intCast,Complex.norm_intCast]
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hpos : 0 < |(n : ℝ)^2-(k : ℝ)^2| :=
      lt_of_lt_of_le (by linarith) (two_mul_nat_sub_one_le_abs_sq_sub_sq hn hk)
    calc
      _ ≤ |(n : ℝ)^2-(k : ℝ)^2|⁻¹ :=
        inv_anti₀ hpos (freeHill_denominator_lower hn hz hk)
      _ = _ := by
        have he : |(n : ℝ)^2-(k : ℝ)^2| = |(k : ℝ)-(n : ℝ)| *|(k : ℝ)+(n : ℝ)| := by
          rw [← abs_mul,show (n : ℝ)^2-(k : ℝ)^2 = -(((k : ℝ)-(n : ℝ))*((k : ℝ)+(n : ℝ))) by ring,abs_neg]
        rw [he,mul_inv]
        simp only [Int.cast_sub,Int.cast_add,Int.cast_natCast]
  · simp only [if_neg hpar,norm_zero]
    exact norm_nonneg _

/-- The same separated reciprocal envelope controls every complex free
boundary block uniformly throughout the full energy strip. -/
theorem norm_hillFreeBoundaryGreen_le_envelope (n : ℕ) (hn : 1 ≤ n) (r : ℤ)
    (z : ℂ) (hz : z ∈ reducedHillStrip n) :
    ‖hillFreeBoundaryGreen n r z‖ ≤ ‖Coeff.twoPoleReciprocalEnvelope n‖ :=
  lp.norm_mono (by norm_num : (1 : ℝ≥0∞) ≠ 0)
    (hillFreeBoundaryGreen_norm_apply_le_envelope n hn r z hz)

/-- The literal boundary complement also has the sharp Hilbert gain. -/
theorem norm_hillFreeBoundaryGreen_two_le (n : ℕ) (hn : 1 ≤ n) (r : ℤ)
    (z : ℂ) (hz : z ∈ reducedHillStrip n) :
    ‖Coeff.exponentInclusion (by norm_num : (1 : ℝ≥0∞) ≤ 2) (hillFreeBoundaryGreen n r z)‖ ≤
      4/(n : ℝ) := by
  apply (lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0) ?_).trans
    (norm_reducedHillHilbertSymbol_le n hn z hz)
  intro k
  rw [Coeff.exponentInclusion_apply,hillFreeBoundaryGreen_apply n hn r z hz,
    reducedHillHilbertSymbol_apply]
  by_cases hk : k.natAbs=n
  · simp only [if_pos hk,norm_zero,le_refl]
  · rw [if_neg hk]
    split_ifs
    · exact le_rfl
    · simpa only [norm_zero] using norm_nonneg ((z-(freeHillValue k : ℂ))⁻¹)

/-- The l1 norm tends uniformly to zero, including every parity and complex
energy in the checked high strip. -/
theorem exists_hillFreeBoundaryGreen_uniform_small (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ r : ℤ, ∀ z : ℂ,
      ∀ _hz : z ∈ reducedHillStrip n, ‖hillFreeBoundaryGreen n r z‖ < ε := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    (Coeff.tendsto_norm_twoPoleReciprocalEnvelope_zero.eventually_lt_const hε)
  refine ⟨max N 1,le_max_right _ _,?_⟩
  intro n hn r z hz
  have hn1 : 1 ≤ n := (le_max_right N 1).trans hn
  exact (norm_hillFreeBoundaryGreen_le_envelope n hn1 r z hz).trans_lt
    (hN n ((le_max_left N 1).trans hn))

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2) (n : ℕ) (hn : 1 ≤ n)
  (r : ℤ) (z : ℂ) (hz : z ∈ reducedHillStrip n) (hcut : 8*‖q‖ ≤ (n : ℝ))

/-- The corrected boundary potential retains the vanishing free l1 factor. -/
theorem norm_hillBoundaryGreenPotential_le_free :
    ‖hillBoundaryGreenPotential q n hn r z hz hcut‖ ≤ 2*‖q‖*‖hillFreeBoundaryGreen n r z‖ := by
  calc
    _ ≤ ‖hillTailInverse SpectralWeight.one q n hn z hz hcut‖ *
        ‖SpectralWeight.one.convolution q (hillUnitFreeBoundaryGreen n r z)‖ :=
      (hillTailInverse SpectralWeight.one q n hn z hz hcut).le_opNorm _
    _ ≤ 2*(‖q‖*‖hillUnitFreeBoundaryGreen n r z‖) :=
      mul_le_mul (norm_hillTailInverse_le SpectralWeight.one q n hn z hz hcut)
        (SpectralWeight.one.norm_convolution_le _ _) (norm_nonneg _) (by norm_num)
    _ = _ := by rw [hillUnitFreeBoundaryGreen,norm_hillUnitWeightLift];ring

theorem norm_hillCorrectedBoundaryGreen_le_free :
    ‖hillCorrectedBoundaryGreen q n hn r z hz hcut‖ ≤ 2*‖hillFreeBoundaryGreen n r z‖ := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hc : 8*‖q‖/(n : ℝ) ≤ 1 := (div_le_iff₀ hnpos).mpr (by simpa using hcut)
  have hP := norm_hillBoundaryGreenPotential_le_free q n hn r z hz hcut
  have hR := norm_hillComplementToL1_apply_le SpectralWeight.one.toWeight n hn z hz
    (hillBoundaryGreenPotential q n hn r z hz hcut)
  have hh := norm_add_le (hillUnitFreeBoundaryGreen n r z)
    (hillComplementToL1 SpectralWeight.one.toWeight n hn z hz (hillBoundaryGreenPotential q n hn r z hz hcut))
  rw [hillUnitFreeBoundaryGreen,norm_hillUnitWeightLift] at hh
  change ‖hillCorrectedBoundaryGreen q n hn r z hz hcut‖ ≤ _ at hh
  have hp := mul_le_mul_of_nonneg_left hP (show 0 ≤ 4/(n : ℝ) by positivity)
  have he : (4/(n : ℝ))*(2*‖q‖*‖hillFreeBoundaryGreen n r z‖) =
      (8*‖q‖/(n : ℝ))*‖hillFreeBoundaryGreen n r z‖ := by ring
  rw [he] at hp
  nlinarith [mul_le_mul_of_nonneg_right hc (norm_nonneg (hillFreeBoundaryGreen n r z))]

/-- Original continuous boundary evaluation is contractive on this l1 vector. -/
theorem norm_hillBoundaryGreenTrace_le_corrected :
    ‖hillBoundaryGreenTrace q n hn r z hz hcut‖ ≤ ‖hillCorrectedBoundaryGreen q n hn r z hz hcut‖ := by
  calc
    _ ≤ ‖Fourier.continuousSynthesis (SpectralWeight.one.toCoeff
      (hillCorrectedBoundaryGreen q n hn r z hz hcut))‖ := ContinuousMap.norm_coe_le_norm _ _
    _ ≤ ‖SpectralWeight.one.toCoeff (hillCorrectedBoundaryGreen q n hn r z hz hcut)‖ :=
      Fourier.norm_continuousSynthesis_le _
    _ ≤ _ := SpectralWeight.one.norm_toCoeff_le _

/-- On a bounded complex potential ball, all corrected boundary entries are
uniformly small at one common high cutoff. -/
theorem exists_hillBoundaryGreen_uniform_small (B ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 1 ≤ N ∧ 8*B ≤ (N : ℝ) ∧
      ∀ q : WeightedCoeff SpectralWeight.one.toWeight 2, ‖q‖ ≤ B →
      ∀ n : ℕ, N ≤ n → ∀ hn1 : 1 ≤ n, ∀ r : ℤ, ∀ z : ℂ, ∀ hz : z ∈ reducedHillStrip n,
      ∀ hcut : 8*‖q‖ ≤ (n : ℝ),
        ‖hillBoundaryGreenPotential q n hn1 r z hz hcut‖ < ε ∧
        ‖hillCorrectedBoundaryGreen q n hn1 r z hz hcut‖ < ε ∧
        ‖hillBoundaryGreenTrace q n hn1 r z hz hcut‖ < ε := by
  let C := 2*(|B|+1)
  have hC : 0 < C := by dsimp only [C];positivity
  obtain ⟨N,hN,hfree⟩ := exists_hillFreeBoundaryGreen_uniform_small (ε/C) (div_pos hε hC)
  obtain ⟨M,hM⟩ := exists_nat_gt (8*B)
  refine ⟨max N M,hN.trans (le_max_left _ _),hM.le.trans (by exact_mod_cast le_max_right N M),?_⟩
  intro q hq n hn hn1 r z hz hc
  have hsmall : C*‖hillFreeBoundaryGreen n r z‖ < ε := by
    have hh := hfree n ((le_max_left N M).trans hn) r z hz
    simpa only [mul_comm] using (lt_div_iff₀ hC).mp hh
  have hqC : 2*‖q‖ ≤ C := by dsimp only [C];linarith [le_abs_self B]
  have h2C : 2 ≤ C := by dsimp only [C];linarith [abs_nonneg B]
  have hp : ‖hillBoundaryGreenPotential q n hn1 r z hz hc‖ < ε :=
    (norm_hillBoundaryGreenPotential_le_free q n hn1 r z hz hc).trans_lt
      ((mul_le_mul_of_nonneg_right hqC (norm_nonneg _)).trans_lt hsmall)
  have hg : ‖hillCorrectedBoundaryGreen q n hn1 r z hz hc‖ < ε :=
    (norm_hillCorrectedBoundaryGreen_le_free q n hn1 r z hz hc).trans_lt
      ((mul_le_mul_of_nonneg_right h2C (norm_nonneg _)).trans_lt hsmall)
  exact ⟨hp,hg,(norm_hillBoundaryGreenTrace_le_corrected q n hn1 r z hz hc).trans_lt hg⟩

end NLS.KdV
