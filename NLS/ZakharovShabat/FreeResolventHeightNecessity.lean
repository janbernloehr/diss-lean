import NLS.ZakharovShabat.TriangularNormalizedBand
import NLS.ZakharovShabat.HeightResolvent

/-! # Necessary exponent dependence of the actual free resolvent norm

Finite Fourier vectors show that the norm of the actual free resolvent
from lp to l1 cannot have an exponent-independent height coefficient.
This obstructs a proposed proof route for the printed periodic height;
it is not a periodic spectral counterexample.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- A nonreal free-resolvent parameter at an exponentially growing height. -/
def negativeDyadicHeight (P : ℕ) : ℂ := -Complex.ofReal ((2 : ℝ)^P)*Complex.I

@[simp] theorem abs_im_negativeDyadicHeight (P : ℕ) :
    |(negativeDyadicHeight P).im| = (2 : ℝ)^P := by
  simp only [negativeDyadicHeight, Complex.mul_im, Complex.neg_re, Complex.ofReal_re,
    Complex.I_im, mul_one, Complex.neg_im, Complex.ofReal_im, Complex.I_re, mul_zero,
    add_zero, abs_neg]
  exact abs_of_pos (by positivity)

theorem negativeDyadicHeight_not_mem_freeLattice (P : ℕ) :
    negativeDyadicHeight P ∉ freeLattice := by
  apply notMem_freeLattice_of_im_ne_zero
  apply abs_pos.mp
  rw [abs_im_negativeDyadicHeight]
  positivity

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The finite boundary functional is also an exact coefficient sum of the scalar free resolvent. -/
theorem tsum_scalarResolventToL1_ofFinsupp (hp : p ≠ ⊤) (a : ℤ →₀ ℂ)
    {H : ℝ} (hz : -Complex.ofReal H*Complex.I ∉ freeLattice) :
    (∑' n : ℤ, scalarResolventToL1 hp (-Complex.ofReal H*Complex.I) hz
      (Coeff.ofFinsupp a) n) = Complex.I*triangularBoundarySum a H := by
  simp only [scalarResolventToL1_apply, Coeff.ofFinsupp_apply]
  rw [tsum_eq_sum (s := a.support) (fun n hn => by
    rw [Finsupp.notMem_support_iff.mp hn, zero_div])]
  unfold triangularBoundarySum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  have he : -Complex.ofReal H*Complex.I-(Real.pi : ℂ)*n =
      -Complex.I*(Complex.ofReal H-(Real.pi : ℂ)*n*Complex.I) := by
    ring_nf
    simp [sub_eq_add_neg]
  rw [he]
  simp [div_eq_mul_inv, mul_comm, mul_assoc]

/-- Summing an l1 sequence is contractive. -/
theorem norm_tsum_coeff_one_le (a : Coeff 1) : ‖∑' n : ℤ, a n‖ ≤ ‖a‖ := by
  have hs := (lp.memℓp a).norm.summable_of_one
  exact (norm_tsum_le_tsum_norm hs).trans_eq
    (by simpa only [ENNReal.toReal_one, Real.rpow_one] using
      (lp.hasSum_norm (p := 1) (by simp) a).tsum_eq)

/-- The normalized finite vector has an output coefficient sum of exactly minus two. -/
theorem tsum_scalarResolventToL1_triangularNormalized {P : ℕ}
    [Fact (1 ≤ (P : ℝ≥0∞))] (hP : 0 < P) :
    (∑' n : ℤ, scalarResolventToL1 (ENNReal.natCast_ne_top P) (negativeDyadicHeight P)
      (negativeDyadicHeight_not_mem_freeLattice P)
      (Coeff.ofFinsupp (triangularNormalizedCoefficients P)) n) = -2 := by
  have h := tsum_scalarResolventToL1_ofFinsupp (ENNReal.natCast_ne_top P)
    (triangularNormalizedCoefficients P) (negativeDyadicHeight_not_mem_freeLattice P)
  rw [triangularBoundarySum_normalized hP] at h
  have hi : Complex.I*(2*Complex.I) = (-2 : ℂ) := by
    calc
      _ = 2*(Complex.I*Complex.I) := by ring
      _ = -2 := by rw [Complex.I_mul_I]; ring
  rw [hi] at h
  simpa only [negativeDyadicHeight] using h

/-- The actual operator output has norm at least two, despite the vanishing input norm. -/
theorem two_le_norm_scalarResolventToL1_triangularNormalized {P : ℕ}
    [Fact (1 ≤ (P : ℝ≥0∞))] (hP : 0 < P) :
    2 ≤ ‖scalarResolventToL1 (ENNReal.natCast_ne_top P) (negativeDyadicHeight P)
      (negativeDyadicHeight_not_mem_freeLattice P)
      (Coeff.ofFinsupp (triangularNormalizedCoefficients P))‖ := by
  have h := norm_tsum_coeff_one_le (scalarResolventToL1 (ENNReal.natCast_ne_top P)
    (negativeDyadicHeight P) (negativeDyadicHeight_not_mem_freeLattice P)
    (Coeff.ofFinsupp (triangularNormalizedCoefficients P)))
  rw [tsum_scalarResolventToL1_triangularNormalized hP] at h
  norm_num at h ⊢
  exact h

/-- The actual lp-to-l1 free-resolvent norm grows at least linearly in the exponent
at height 2^P. This is a lower bound for the operator, not merely for an upper estimate. -/
theorem scalarResolventToL1_dyadic_norm_lower {P : ℕ}
    [Fact (1 ≤ (P : ℝ≥0∞))] (hP : 0 < P) :
    (P : ℝ)/48 ≤ ‖scalarResolventToL1 (ENNReal.natCast_ne_top P)
      (negativeDyadicHeight P) (negativeDyadicHeight_not_mem_freeLattice P)‖ := by
  let a : Coeff (P : ℝ≥0∞) := Coeff.ofFinsupp (triangularNormalizedCoefficients P)
  let R := scalarResolventToL1 (ENNReal.natCast_ne_top P) (negativeDyadicHeight P)
    (negativeDyadicHeight_not_mem_freeLattice P)
  have ha : ‖a‖ ≤ 96/(P : ℝ) := by
    exact (WithLp.norm_fst_le (Coeff (P : ℝ≥0∞))
      (CoeffPair.ofFinsupp (triangularNormalizedCoefficients P,0))).trans
        (norm_triangularNormalizedCoefficients_source_le hP)
  have hR := (two_le_norm_scalarResolventToL1_triangularNormalized hP).trans
    ((R.le_opNorm a).trans (mul_le_mul_of_nonneg_left ha (norm_nonneg R)))
  have hPr : 0 < (P : ℝ) := by exact_mod_cast hP
  rw [← mul_div_assoc] at hR
  have hm := (le_div_iff₀ hPr).mp hR
  change (P : ℝ)/48 ≤ ‖R‖
  linarith

/-- The scalar component norm is bounded by the full free pair-resolvent norm. -/
theorem norm_scalarResolventToL1_le_pair (hp : p ≠ ⊤) (z : ℂ) (hz : z ∉ freeLattice) :
    ‖scalarResolventToL1 hp z hz‖ ≤ ‖freeResolventToL1 hp z hz‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro a
  have h := (norm_snd_le (freeResolventToL1 hp z hz (0,a))).trans
    ((freeResolventToL1 hp z hz).le_opNorm (0,a))
  have he : (freeResolventToL1 hp z hz (0,a)).2 = scalarResolventToL1 hp z hz a := rfl
  rw [he] at h
  simpa only [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg a)] using h

/-- The same lower bound holds for the full periodic free pair-resolvent. -/
theorem freeResolventToL1_dyadic_norm_lower {P : ℕ}
    [Fact (1 ≤ (P : ℝ≥0∞))] (hP : 0 < P) :
    (P : ℝ)/48 ≤ ‖freeResolventToL1 (ENNReal.natCast_ne_top P)
      (negativeDyadicHeight P) (negativeDyadicHeight_not_mem_freeLattice P)‖ :=
  (scalarResolventToL1_dyadic_norm_lower hP).trans
    (norm_scalarResolventToL1_le_pair _ _ _)

/-- The established upper bound has the same linear order at the test heights. -/
theorem freeResolventToL1_dyadic_norm_upper {P : ℕ}
    [Fact (1 ≤ (P : ℝ≥0∞))] (hP : 0 < P) :
    ‖freeResolventToL1 (ENNReal.natCast_ne_top P)
      (negativeDyadicHeight P) (negativeDyadicHeight_not_mem_freeLattice P)‖ ≤
        2*(P : ℝ) + ((2 : ℝ)^P)⁻¹ := by
  have him : (negativeDyadicHeight P).im ≠ 0 := by
    apply abs_pos.mp
    rw [abs_im_negativeDyadicHeight]
    positivity
  have h := norm_freeResolventToL1_le_height (ENNReal.natCast_ne_top P)
    (negativeDyadicHeight P) (negativeDyadicHeight_not_mem_freeLattice P) him
  have hPr : (P : ℝ) ≠ 0 := by exact_mod_cast hP.ne'
  have hroot : ((2 : ℝ)^P)^(1/(P : ℝ)) = 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      mul_one_div_cancel hPr, Real.rpow_one]
  rw [ENNReal.toReal_natCast, abs_im_negativeDyadicHeight, hroot] at h
  convert h using 1
  ring

/-- Any coefficient in the standard height-decay form must grow with the exponent,
even if the estimate is required only at the explicit dyadic test point. -/
theorem freeResolventHeightCoefficient_necessary {P : ℕ}
    [Fact (1 ≤ (P : ℝ≥0∞))] (hP : 0 < P) (C : ℝ)
    (hbound : ‖freeResolventToL1 (ENNReal.natCast_ne_top P)
      (negativeDyadicHeight P) (negativeDyadicHeight_not_mem_freeLattice P)‖ ≤
      C/|(negativeDyadicHeight P).im|^(1/(P : ℝ)) + |(negativeDyadicHeight P).im|⁻¹) :
    (P : ℝ) ≤ 24*C+48 := by
  have hPr : (P : ℝ) ≠ 0 := by exact_mod_cast hP.ne'
  have hroot : ((2 : ℝ)^P)^(1/(P : ℝ)) = 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      mul_one_div_cancel hPr, Real.rpow_one]
  rw [abs_im_negativeDyadicHeight, hroot] at hbound
  have hinv : ((2 : ℝ)^P)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hl := freeResolventToL1_dyadic_norm_lower hP
  linarith

/-- The actual constant-eight free-resolvent bound fails at every integer exponent above 240. -/
theorem freeResolvent_eight_height_bound_fails {P : ℕ}
    [Fact (1 ≤ (P : ℝ≥0∞))] (hP : 240 < P) :
    8/|(negativeDyadicHeight P).im|^(1/(P : ℝ)) + |(negativeDyadicHeight P).im|⁻¹ <
      ‖freeResolventToL1 (ENNReal.natCast_ne_top P)
        (negativeDyadicHeight P) (negativeDyadicHeight_not_mem_freeLattice P)‖ := by
  by_contra h
  have hn := freeResolventHeightCoefficient_necessary (by omega : 0 < P) 8 (le_of_not_gt h)
  have hPr : (240 : ℝ) < P := by exact_mod_cast hP
  norm_num at hn
  linarith

/-- No fixed coefficient repairs this free-resolvent norm estimate for all finite exponents. -/
theorem not_exists_uniform_freeResolventHeightCoefficient :
    ¬ ∃ C : ℝ, ∀ P : ℕ, ∀ hP : 0 < P,
      let _ : Fact (1 ≤ (P : ℝ≥0∞)) := ⟨by exact_mod_cast hP⟩
      ∀ z : ℂ, ∀ hz : z ∉ freeLattice, z.im ≠ 0 →
        ‖freeResolventToL1 (ENNReal.natCast_ne_top P) z hz‖ ≤
          C/|z.im|^(1/(P : ℝ)) + |z.im|⁻¹ := by
  rintro ⟨C,h⟩
  obtain ⟨P,hPC⟩ := exists_nat_gt (max (24*C+48) 0)
  have hP : 0 < P := by exact_mod_cast ((le_max_right (24*C+48) 0).trans_lt hPC)
  let _ : Fact (1 ≤ (P : ℝ≥0∞)) := ⟨by exact_mod_cast hP⟩
  have him : (negativeDyadicHeight P).im ≠ 0 := by
    apply abs_pos.mp
    rw [abs_im_negativeDyadicHeight]
    positivity
  have hn := freeResolventHeightCoefficient_necessary hP C
    (h P hP (negativeDyadicHeight P) (negativeDyadicHeight_not_mem_freeLattice P) him)
  exact (not_le_of_gt ((le_max_left (24*C+48) 0).trans_lt hPC)) hn

/-- Every test point is nonetheless in the actual free periodic resolvent set. -/
theorem negativeDyadicHeight_mem_free_resolvent (hp : p ≠ ⊤) (P : ℕ) :
    negativeDyadicHeight P ∈ resolventSet hp 0 :=
  mem_resolventSet_zero_of_notMem hp _ (negativeDyadicHeight_not_mem_freeLattice P)

end NLS.ZakharovShabat
