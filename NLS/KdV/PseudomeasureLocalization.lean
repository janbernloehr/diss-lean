import NLS.KdV.PseudomeasureAnalytic
import NLS.FunctionalAnalysis.TwoDimensionalDeterminant

/-! # Quantitative localization of the physical endpoint determinant

The opposite shifted inverse bounds control the two columns of the effective
correction without a loss of endpoint regularity. All estimates are uniform
over the corrected closed strip.
-/
noncomputable section
open scoped ENNReal
namespace NLS.KdV

/-- Unit-weight signed norms give the exact positive-order coordinate bound. -/
theorem norm_apply_le_negativeShiftedNorm_one (r : ℝ) (hr : 0 ≤ r) (l : ℤ)
    (a : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (k : ℤ) :
    ‖a.val k‖ ≤ SpectralWeight.one.negativeShiftedNorm r hr l ⊤ a * Weight.sobolev r (k+l) := by
  have h := WeightedCoeff.norm_apply_le _ ⊤ (SpectralWeight.one.negativeShiftEquiv r hr l ⊤ a) k
  simpa only [SpectralWeight.negativeShiftEquiv_apply, Weight.shift_apply,
    SpectralWeight.negativeSobolev_apply, SpectralWeight.one_apply, div_eq_mul_inv,
    one_mul, inv_inv, SpectralWeight.negativeShiftedNorm] using h

/-- The first resonant source column is actual Fourier modulation of q. -/
theorem endpointHillModePotential_basis_pos (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) :
    endpointHillModePotential r hr hr1 n q (1,0) =
      SpectralWeight.one.negativeModulation r hr (n:ℤ) q := by
  apply Subtype.ext
  funext k
  change (endpointH1Multiplication r hr hr1 q (endpointHillH1Modes n (1,0))).val k = _
  rw [endpointH1Multiplication_apply, SpectralWeight.negativeModulation_apply]
  simp only [endpointHillH1Modes_coefficient, ite_self, add_zero, mul_ite, mul_one, mul_zero, tsum_ite_eq]

/-- The second resonant source column is the opposite modulation of q. -/
theorem endpointHillModePotential_basis_neg (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) :
    endpointHillModePotential r hr hr1 n q (0,1) =
      SpectralWeight.one.negativeModulation r hr (-(n:ℤ)) q := by
  apply Subtype.ext
  funext k
  change (endpointH1Multiplication r hr hr1 q (endpointHillH1Modes n (0,1))).val k = _
  rw [endpointH1Multiplication_apply, SpectralWeight.negativeModulation_apply]
  simp only [endpointHillH1Modes_coefficient, ite_self, zero_add, mul_ite, mul_one, mul_zero, tsum_ite_eq]

variable (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
variable (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
variable (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
variable (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)

/-- Sharp placement of the opposite shifts on the effective source columns. -/
theorem endpointHillEffectivePotential_basis_shifted :
    SpectralWeight.one.negativeShiftedNorm r hr (-(n:ℤ)) ⊤
      (endpointHillEffectivePotential r hr hr1 n hn z hz q hs (1,0)) ≤ 2*‖q‖ ∧
    SpectralWeight.one.negativeShiftedNorm r hr (n:ℤ) ⊤
      (endpointHillEffectivePotential r hr hr1 n hn z hz q hs (0,1)) ≤ 2*‖q‖ := by
  constructor
  · change SpectralWeight.one.negativeShiftedNorm r hr (-(n:ℤ)) ⊤
      (endpointHillTailInverse SpectralWeight.one r hr hr1 n hn z hz q hs
        (endpointHillModePotential r hr hr1 n q (1,0))) ≤ 2*‖q‖
    rw [endpointHillModePotential_basis_pos]
    have h := (negativeShiftedNorm_endpointHillTailInverse_le SpectralWeight.one r hr hr1
      n hn z hz q hs (endpointHillModePotential r hr hr1 n q (1,0))).2
    rw [endpointHillModePotential_basis_pos] at h
    simpa only [SpectralWeight.negativeShiftedNorm_negativeModulation] using h
  · change SpectralWeight.one.negativeShiftedNorm r hr (n:ℤ) ⊤
      (endpointHillTailInverse SpectralWeight.one r hr hr1 n hn z hz q hs
        (endpointHillModePotential r hr hr1 n q (0,1))) ≤ 2*‖q‖
    rw [endpointHillModePotential_basis_neg]
    have h := (negativeShiftedNorm_endpointHillTailInverse_le SpectralWeight.one r hr hr1
      n hn z hz q hs (endpointHillModePotential r hr hr1 n q (0,1))).1
    rw [endpointHillModePotential_basis_neg] at h
    have hnorm := SpectralWeight.one.negativeShiftedNorm_negativeModulation r hr (-(n:ℤ)) q
    rw [neg_neg] at hnorm
    simpa only [hnorm] using h

/-- Both effective matrix columns have the exact endpoint-order growth bound. -/
theorem endpointHillEffectiveCorrection_columns_le :
    ‖hillModeCoordinates (SpectralWeight.one.negativeSobolev r) ⊤ n
      (endpointHillEffectivePotential r hr hr1 n hn z hz q hs (1,0))‖ ≤
        2*Weight.sobolev r (2*(n:ℤ))*‖q‖ ∧
    ‖hillModeCoordinates (SpectralWeight.one.negativeSobolev r) ⊤ n
      (endpointHillEffectivePotential r hr hr1 n hn z hz q hs (0,1))‖ ≤
        2*Weight.sobolev r (2*(n:ℤ))*‖q‖ := by
  have hS : 1 ≤ Weight.sobolev r (2*(n:ℤ)) :=
    Real.one_le_rpow (le_add_of_nonneg_right (abs_nonneg _)) hr
  obtain ⟨hplus,hminus⟩ := endpointHillEffectivePotential_basis_shifted r hr hr1 n hn z hz q hs
  constructor
  · apply max_le
    · have h := norm_apply_le_negativeShiftedNorm_one r hr (-(n:ℤ))
        (endpointHillEffectivePotential r hr hr1 n hn z hz q hs (1,0)) (n:ℤ)
      simp only [add_neg_cancel, Weight.sobolev_apply, Int.cast_zero, abs_zero, add_zero,
        Real.one_rpow, mul_one] at h
      exact h.trans (hplus.trans (by nlinarith [norm_nonneg q]))
    · have h := norm_apply_le_negativeShiftedNorm_one r hr (-(n:ℤ))
        (endpointHillEffectivePotential r hr hr1 n hn z hz q hs (1,0)) (-(n:ℤ))
      rw [show -(n:ℤ)+ -(n:ℤ) = -(2*(n:ℤ)) by omega, Weight.sobolev_neg] at h
      exact h.trans ((mul_le_mul_of_nonneg_right hplus ((Weight.sobolev r).positive _).le).trans_eq (by ring))
  · apply max_le
    · have h := norm_apply_le_negativeShiftedNorm_one r hr (n:ℤ)
        (endpointHillEffectivePotential r hr hr1 n hn z hz q hs (0,1)) (n:ℤ)
      rw [show (n:ℤ)+(n:ℤ) = 2*(n:ℤ) by omega] at h
      exact h.trans ((mul_le_mul_of_nonneg_right hminus ((Weight.sobolev r).positive _).le).trans_eq (by ring))
    · have h := norm_apply_le_negativeShiftedNorm_one r hr (n:ℤ)
        (endpointHillEffectivePotential r hr hr1 n hn z hz q hs (0,1)) (-(n:ℤ))
      simp only [neg_add_cancel, Weight.sobolev_apply, Int.cast_zero, abs_zero, add_zero,
        Real.one_rpow, mul_one] at h
      exact h.trans (hminus.trans (by nlinarith [norm_nonneg q]))

include hn hz hs in
/-- The determinant is a quantitative perturbation of the squared free dispersion. -/
theorem endpointReducedDeterminant_free_error_le :
    ‖endpointReducedDeterminant r hr hr1 n (q,z)-(z-(freeHillValue n:ℂ))^2‖ ≤
      2*‖z-(freeHillValue n:ℂ)‖*(2*Weight.sobolev r (2*(n:ℤ))*‖q‖) +
        2*(2*Weight.sobolev r (2*(n:ℤ))*‖q‖)^2 := by
  rw [endpointReducedDeterminant, endpointReducedFamily_eq r hr hr1 n hn (q,z) hz hs]
  let E := (hillModeCoordinates (SpectralWeight.one.negativeSobolev r) ⊤ n).comp
    (endpointHillEffectivePotential r hr hr1 n hn z hz q hs)
  obtain ⟨h1,h2⟩ := endpointHillEffectiveCorrection_columns_le r hr hr1 n hn z hz q hs
  exact FiniteSpectralDeterminant.determinant_shift_bound E (z-(freeHillValue n:ℂ))
    (2*Weight.sobolev r (2*(n:ℤ))*‖q‖)
      (mul_nonneg (mul_nonneg (by norm_num) ((Weight.sobolev r).positive _).le) (norm_nonneg q)) h1 h2

/-- Kernel localization follows from the same two columns without assuming
equality of diagonal corrections or choosing individual roots. -/
theorem endpointHillReduced_kernel_localization (u : ℂ × ℂ) (hu0 : u ≠ 0)
    (hu : endpointHillReducedOperator r hr hr1 n hn z hz q hs u = 0) :
    ‖z-(freeHillValue n:ℂ)‖ ≤ 4*Weight.sobolev r (2*(n:ℤ))*‖q‖ := by
  let E := (hillModeCoordinates (SpectralWeight.one.negativeSobolev r) ⊤ n).comp
    (endpointHillEffectivePotential r hr hr1 n hn z hz q hs)
  obtain ⟨h1,h2⟩ := endpointHillEffectiveCorrection_columns_le r hr hr1 n hn z hz q hs
  change ‖E (1,0)‖ ≤ 2*Weight.sobolev r (2*(n:ℤ))*‖q‖ at h1
  change ‖E (0,1)‖ ≤ 2*Weight.sobolev r (2*(n:ℤ))*‖q‖ at h2
  have he : (z-(freeHillValue n:ℂ)) • u = E u := sub_eq_zero.mp hu
  have hsplit : E u = u.1 • E (1,0)+u.2 • E (0,1) := by
    rw [← map_smul, ← map_smul, ← map_add]
    congr 1
    ext <;> simp
  have hb : ‖E u‖ ≤ (4*Weight.sobolev r (2*(n:ℤ))*‖q‖)*‖u‖ := by
    rw [hsplit]
    apply (norm_add_le _ _).trans
    rw [norm_smul, norm_smul]
    have hfst := norm_fst_le u
    have hsnd := norm_snd_le u
    have hA := mul_le_mul hfst h1 (norm_nonneg _) (norm_nonneg _)
    have hB := mul_le_mul hsnd h2 (norm_nonneg _) (norm_nonneg _)
    nlinarith
  rw [← he, norm_smul] at hb
  exact (mul_le_mul_iff_of_pos_right (norm_pos_iff.mpr hu0)).mp hb

end NLS.KdV
