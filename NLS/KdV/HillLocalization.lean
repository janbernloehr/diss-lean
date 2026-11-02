import NLS.KdV.HillAnalytic
import NLS.KdV.HillPhysical

/-!
# Quantitative localization from the actual two-mode Hill reduction

The effective correction has norm at most `4*norm(q)` on the unweighted
two-mode space. Thus every determinant zero and physical eigenvector in
the radius-6n strip lies within `4*norm(q)` of `pi²*n²`, under the proved
cutoff `n >= 8*norm(q)`. This proves inclusion, not the still-needed
count of two eigenvalues or a global spectral enumeration.
-/

noncomputable section
open scoped ENNReal
namespace NLS.KdV

theorem norm_hillModes_one_le (n : ℕ) (u : ℂ × ℂ) :
    ‖hillModes SpectralWeight.one.toWeight n u‖ ≤ 2*‖u‖ := by
  change ‖u.1 • WeightedCoeff.single SpectralWeight.one.toWeight (n : ℤ) 1 +
    u.2 • WeightedCoeff.single SpectralWeight.one.toWeight (-(n : ℤ)) 1‖ ≤ _
  apply (norm_add_le _ _).trans
  simp only [norm_smul, WeightedCoeff.norm_single,
    SpectralWeight.one_apply, norm_one, mul_one]
  linarith [norm_fst_le u, norm_snd_le u]

theorem norm_hillModeCoordinates_one_le {p : ℝ≥0∞} [Fact (1 ≤ p)] (n : ℕ)
    (a : WeightedCoeff SpectralWeight.one.toWeight p) :
    ‖hillModeCoordinates SpectralWeight.one.toWeight p n a‖ ≤ ‖a‖ := by
  change max ‖a.val n‖ ‖a.val (-(n : ℤ))‖ ≤ ‖a‖
  apply max_le
  · simpa using WeightedCoeff.norm_apply_le SpectralWeight.one.toWeight p a (n : ℤ)
  · simpa using WeightedCoeff.norm_apply_le SpectralWeight.one.toWeight p a (-(n : ℤ))

/-- The source effective correction has a uniform bound on raw resonant amplitudes. -/
theorem norm_hillEffectiveCorrection_one_le
    (q : WeightedCoeff SpectralWeight.one.toWeight 2) (n : ℕ) (hn : 1 ≤ n)
    (z : ℂ) (hz : z ∈ reducedHillStrip n) (hcut : 8*‖q‖ ≤ (n : ℝ)) (u : ℂ × ℂ) :
    ‖hillModeCoordinates SpectralWeight.one.toWeight 2 n
      (hillEffectivePotential SpectralWeight.one q n hn z hz hcut u)‖ ≤ 4*‖q‖*‖u‖ := by
  apply (norm_hillModeCoordinates_one_le n _).trans
  change ‖hillTailInverse SpectralWeight.one q n hn z hz hcut
    (SpectralWeight.one.convolution q (hillModes SpectralWeight.one.toWeight n u))‖ ≤ _
  calc
    _ ≤ ‖hillTailInverse SpectralWeight.one q n hn z hz hcut‖ *
        ‖SpectralWeight.one.convolution q (hillModes SpectralWeight.one.toWeight n u)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ 2 * (‖q‖ * ‖hillModes SpectralWeight.one.toWeight n u‖) :=
      mul_le_mul (norm_hillTailInverse_le _ q n hn z hz hcut)
        (SpectralWeight.one.norm_convolution_le q _) (norm_nonneg _) (by norm_num)
    _ ≤ 2 * (‖q‖ * (2*‖u‖)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (norm_hillModes_one_le n u) (norm_nonneg q)) (by norm_num)
    _ = _ := by ring

/-- A nonzero vector in the effective kernel obeys the quantitative Hill localization. -/
theorem hillReduced_kernel_localization
    (q : WeightedCoeff SpectralWeight.one.toWeight 2) (n : ℕ) (hn : 1 ≤ n)
    (z : ℂ) (hz : z ∈ reducedHillStrip n) (hcut : 8*‖q‖ ≤ (n : ℝ))
    (u : ℂ × ℂ) (hu0 : u ≠ 0)
    (hu : hillReducedOperator SpectralWeight.one q n hn z hz hcut u = 0) :
    ‖z-(freeHillValue n : ℂ)‖ ≤ 4*‖q‖ := by
  have he : (z-(freeHillValue n : ℂ)) • u =
      hillModeCoordinates SpectralWeight.one.toWeight 2 n
        (hillEffectivePotential SpectralWeight.one q n hn z hz hcut u) :=
    sub_eq_zero.mp hu
  have hb := norm_hillEffectiveCorrection_one_le q n hn z hz hcut u
  rw [← he, norm_smul] at hb
  exact (mul_le_mul_iff_of_pos_right (norm_pos_iff.mpr hu0)).mp hb

/-- Every zero of the actual effective determinant is in the indicated disc. -/
theorem hillReducedDeterminant_zero_localization
    (q : WeightedCoeff SpectralWeight.one.toWeight 2) (n : ℕ) (hn : 1 ≤ n)
    (z : ℂ) (hz : z ∈ reducedHillStrip n) (hcut : 8*‖q‖ ≤ (n : ℝ))
    (hd : hillReducedDeterminant SpectralWeight.one n (q,z) = 0) :
    ‖z-(freeHillValue n : ℂ)‖ ≤ 4*‖q‖ := by
  rw [hillReducedDeterminant_eq SpectralWeight.one n hn (q,z) hz hcut,
    hillReduced_det_eq_zero_iff,
    exists_hillFourierEigenvector_iff SpectralWeight.one q n hn z hz hcut] at hd
  obtain ⟨u, hu0, hu⟩ := hd
  exact hillReduced_kernel_localization q n hn z hz hcut u hu0 hu

/-- The same localization holds for the constructed physical periodic H2 operator. -/
theorem physicalHillEigenvector_localization
    (q : WeightedCoeff SpectralWeight.one.toWeight 2) (n : ℕ) (hn : 1 ≤ n)
    (z : ℂ) (hz : z ∈ reducedHillStrip n) (hcut : 8*‖q‖ ≤ (n : ℝ))
    (f : HillSobolevDomain) (hf0 : f ≠ 0)
    (hf : physicalHillOperator (Fourier.l2Synthesis (SpectralWeight.one.toCoeff q)) f =
      z • ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (hillRepresentative f)) :
    ‖z-(freeHillValue n : ℂ)‖ ≤ 4*‖q‖ := by
  have hd := (hillReduced_det_eq_zero_iff_physicalEigenvector q n hn z hz hcut).mpr
    ⟨f, hf0, hf⟩
  apply hillReducedDeterminant_zero_localization q n hn z hz hcut
  rwa [hillReducedDeterminant_eq SpectralWeight.one n hn (q,z) hz hcut]

/-- For a fixed potential, the actual determinant is analytic throughout
the open spectral strip, including at the physical eigenvalues. -/
theorem analyticOnNhd_hillReducedDeterminant_spectral
    (w : SpectralWeight) (q : WeightedCoeff w.toWeight 2) (n : ℕ) (hn : 1 ≤ n)
    (hcut : 8*‖q‖ ≤ (n : ℝ)) :
    AnalyticOnNhd ℂ (fun z => hillReducedDeterminant w n (q,z)) (openHillStrip n) := by
  intro z hz
  exact (analyticAt_hillReducedDeterminant w n hn (q,z) hz hcut).comp
    (f := fun z : ℂ => (q,z)) (analyticAt_const.prod analyticAt_id)

end NLS.KdV
