import NLS.KdV.HillReduction

/-!
# Weighted coefficients of the effective Hill operator

The inverse bound is uniform in the source's shifted weighted norms.
Applying it to a literal single Fourier mode gives the coefficient
estimates underlying Lemma A.4, with the explicit bound `8*norm(q)^2/n`.
The period-two potential coefficient at `2*n` is retained here; its
identification with a period-one coefficient is a separate adapter.
-/

noncomputable section
open scoped ENNReal
namespace NLS.KdV

theorem shiftedNorm_hillTailInverse_le (w : SpectralWeight) (i : ℤ)
    (q : WeightedCoeff w.toWeight 2) (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ reducedHillStrip n) (hcut : 8*‖q‖ ≤ (n : ℝ))
    (b : WeightedCoeff w.toWeight 2) :
    w.shiftedNorm i (hillTailInverse w q n hn z hz hcut b) ≤ 2*w.shiftedNorm i b := by
  let a := hillTailInverse w q n hn z hz hcut b
  have hr : a-hillTailPerturbation w q n hn z hz a = b :=
    hillTailInverse_right w q n hn z hz hcut b
  have hb := norm_le_norm_sub_add (w.toShift i a)
    (w.toShift i (hillTailPerturbation w q n hn z hz a))
  rw [← map_sub, hr] at hb
  have ht := shiftedNorm_hillTailPerturbation_le w i q n hn z hz a
  have hc : 4*‖q‖/(n : ℝ) ≤ (1/2 : ℝ) := by
    apply (div_le_iff₀ (show (0 : ℝ) < n by exact_mod_cast (show 0 < n by omega))).mpr
    linarith
  have hnonneg : 0 ≤ w.shiftedNorm i a := norm_nonneg _
  change w.shiftedNorm i a ≤ w.shiftedNorm i b +
    w.shiftedNorm i (hillTailPerturbation w q n hn z hz a) at hb
  nlinarith [mul_le_mul_of_nonneg_right hc hnonneg]

theorem hill_convolution_single (w : SpectralWeight) (q : WeightedCoeff w.toWeight 2) (j : ℤ) :
    w.convolution q (WeightedCoeff.single w.toWeight j 1) = w.modulation j q := by
  apply Subtype.ext
  funext k
  simp [SpectralWeight.convolution_apply, WeightedCoeff.single_val, Pi.single_apply,
    SpectralWeight.modulation_apply]

theorem shiftedNorm_modulation_cancel (w : SpectralWeight) (q : WeightedCoeff w.toWeight 2)
    (j : ℤ) : w.shiftedNorm (-j) (w.modulation j q) = ‖q‖ := by
  rw [← w.norm_modulation]
  rw [← w.modulation_add j (-j) q]
  simp

theorem shiftedNorm_coefficient_le (w : SpectralWeight) (i k : ℤ)
    (a : WeightedCoeff w.toWeight 2) : w (k+i)*‖a.val k‖ ≤ w.shiftedNorm i a := by
  unfold SpectralWeight.shiftedNorm
  rw [WeightedCoeff.norm_eq]
  have h := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (WeightedCoeff.weightEquiv (w.toWeight.shift i) 2 (w.toShift i a)) k
  simpa only [WeightedCoeff.weightEquiv_apply, SpectralWeight.toShift_apply, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg (w.positive (k+i)).le,
    Weight.shift_apply, SpectralWeight.toWeight_apply] using h

variable (w : SpectralWeight) (q : WeightedCoeff w.toWeight 2)
  (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
  (hcut : 8*‖q‖ ≤ (n : ℝ))

/-- The corrected potential of a raw unit mode at any signed frequency. -/
def hillCorrectedMode (j : ℤ) : WeightedCoeff w.toWeight 2 :=
  hillTailInverse w q n hn z hz hcut (w.modulation j q)

theorem hillCorrectedMode_pos : hillCorrectedMode w q n hn z hz hcut n =
    hillEffectivePotential w q n hn z hz hcut (1,0) := by
  change hillTailInverse w q n hn z hz hcut (w.modulation (n : ℤ) q) =
    hillTailInverse w q n hn z hz hcut (w.convolution q (hillModes w.toWeight n (1,0)))
  congr 1
  rw [← hill_convolution_single]
  congr 1
  apply Subtype.ext
  funext k
  simp [hillModes_apply, WeightedCoeff.single_val, Pi.single_apply]

theorem hillCorrectedMode_neg : hillCorrectedMode w q n hn z hz hcut (-(n : ℤ)) =
    hillEffectivePotential w q n hn z hz hcut (0,1) := by
  change hillTailInverse w q n hn z hz hcut (w.modulation (-(n : ℤ)) q) =
    hillTailInverse w q n hn z hz hcut (w.convolution q (hillModes w.toWeight n (0,1)))
  congr 1
  rw [← hill_convolution_single]
  congr 1
  apply Subtype.ext
  funext k
  simp [hillModes_apply, WeightedCoeff.single_val, Pi.single_apply]

theorem shiftedNorm_hillCorrectedMode_le (j : ℤ) :
    w.shiftedNorm (-j) (hillCorrectedMode w q n hn z hz hcut j) ≤ 2*‖q‖ := by
  apply (shiftedNorm_hillTailInverse_le w (-j) q n hn z hz hcut (w.modulation j q)).trans_eq
  rw [shiftedNorm_modulation_cancel]

/-- Uniform weighted error of every coefficient, with no assumed gap estimate. -/
theorem hillCorrectedMode_coefficient_error (j k : ℤ) :
    w (k-j)*‖(hillCorrectedMode w q n hn z hz hcut j).val k-q.val (k-j)‖ ≤
      8*‖q‖^2/(n : ℝ) := by
  let a := hillCorrectedMode w q n hn z hz hcut j
  have hr : a-hillTailPerturbation w q n hn z hz a = w.modulation j q :=
    hillTailInverse_right w q n hn z hz hcut (w.modulation j q)
  have he : a-w.modulation j q = hillTailPerturbation w q n hn z hz a :=
    sub_eq_iff_eq_add.mpr ((sub_eq_iff_eq_add.mp hr).trans (add_comm _ _))
  change w (k-j)*‖a.val k-q.val (k-j)‖ ≤ _
  calc
    _ = w (k-j)*‖(a-w.modulation j q).val k‖ := by
      rw [WeightedCoeff.sub_val, SpectralWeight.modulation_apply]
    _ ≤ w.shiftedNorm (-j) (a-w.modulation j q) := by
      simpa only [sub_eq_add_neg] using shiftedNorm_coefficient_le w (-j) k (a-w.modulation j q)
    _ = w.shiftedNorm (-j) (hillTailPerturbation w q n hn z hz a) := by rw [he]
    _ ≤ (4*‖q‖/(n : ℝ))*w.shiftedNorm (-j) a :=
      shiftedNorm_hillTailPerturbation_le w (-j) q n hn z hz a
    _ ≤ (4*‖q‖/(n : ℝ))*(2*‖q‖) :=
      mul_le_mul_of_nonneg_left (shiftedNorm_hillCorrectedMode_le w q n hn z hz hcut j)
        (by positivity)
    _ = _ := by ring

/-- The upper diagonal correction; equality with the opposite diagonal is
proved separately from the coefficient estimate. -/
def hillDiagonal : ℂ := (hillCorrectedMode w q n hn z hz hcut n).val n

def hillOppositeDiagonal : ℂ := (hillCorrectedMode w q n hn z hz hcut (-(n : ℤ))).val (-(n : ℤ))

def hillUpperCoupling : ℂ := (hillCorrectedMode w q n hn z hz hcut (-(n : ℤ))).val n

def hillLowerCoupling : ℂ := (hillCorrectedMode w q n hn z hz hcut n).val (-(n : ℤ))

theorem hillDiagonal_error_le : ‖hillDiagonal w q n hn z hz hcut-q.val 0‖ ≤ 8*‖q‖^2/(n : ℝ) := by
  have h := hillCorrectedMode_coefficient_error w q n hn z hz hcut (n : ℤ) (n : ℤ)
  simp only [sub_self] at h
  have hb := mul_le_mul_of_nonneg_right (w.one_le 0)
    (norm_nonneg (hillDiagonal w q n hn z hz hcut-q.val 0))
  simp only [one_mul] at hb
  exact hb.trans h

theorem hillDiagonal_le_of_mean_zero (hzero : q.val 0 = 0) :
    ‖hillDiagonal w q n hn z hz hcut‖ ≤ 8*‖q‖^2/(n : ℝ) := by
  simpa only [hzero, sub_zero] using hillDiagonal_error_le w q n hn z hz hcut

theorem hillUpperCoupling_error_le :
    w (2*(n : ℤ))*‖hillUpperCoupling w q n hn z hz hcut-q.val (2*(n : ℤ))‖ ≤
      8*‖q‖^2/(n : ℝ) := by
  unfold hillUpperCoupling
  have h := hillCorrectedMode_coefficient_error w q n hn z hz hcut (-(n : ℤ)) (n : ℤ)
  simpa only [sub_neg_eq_add, ← two_mul] using h

theorem hillLowerCoupling_error_le :
    w (2*(n : ℤ))*‖hillLowerCoupling w q n hn z hz hcut-q.val (-(2*(n : ℤ)))‖ ≤
      8*‖q‖^2/(n : ℝ) := by
  have h := hillCorrectedMode_coefficient_error w q n hn z hz hcut (n : ℤ) (-(n : ℤ))
  rw [show -(n : ℤ)-(n : ℤ) = -(2*(n : ℤ)) by ring, w.apply_neg] at h
  exact h

end NLS.KdV
