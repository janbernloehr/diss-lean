import NLS.ZakharovShabat.FreeStripInverseBounds

/-!
# Lower bounds for the free sine on the spectral exterior

Periodicity and compactness control the reciprocal on horizontal strips.
The exponential formula gives a lower bound at large imaginary height.
Together these bound exp(abs(Im z)) / abs(sin z) outside every fixed family
of free discs, without excluding any additional spectral parameters.
-/

noncomputable section
open Set Complex Metric
namespace NLS.ZakharovShabat

/-- The free sine has no zero away from the free spectral lattice. -/
theorem sin_ne_zero_of_notMem_freeLattice {z : ℂ} (hz : z ∉ freeLattice) : sin z ≠ 0 := by
  intro h
  obtain ⟨n, hn⟩ := Complex.sin_eq_zero_iff.mp h
  exact hz ⟨n, by simpa [mul_comm] using hn.symm⟩

/-- The reciprocal sine is bounded on each separated horizontal strip. -/
theorem exists_bound_sin_inv_strip {r : ℝ} (hr : 0 < r) (H : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, |z.im| ≤ H →
      (∀ n : ℤ, r ≤ ‖z-(Real.pi : ℂ)*n‖) → ‖(sin z)⁻¹‖ ≤ C := by
  let S : Set ℂ := {z | ∀ n : ℤ, r ≤ ‖z-(Real.pi : ℂ)*n‖}
  have hS : IsClosed S := by
    simp only [S, ofPred_forall]
    exact isClosed_iInter (fun n => isClosed_le continuous_const (by fun_prop))
  let K := closedBall (0 : ℂ) (Real.pi+H) ∩ S
  have hK : IsCompact K := (isCompact_closedBall _ _).inter_right hS
  have hc : ContinuousOn (fun z : ℂ => (sin z)⁻¹) K := by
    apply ContinuousOn.inv₀ continuous_sin.continuousOn
    intro z hz
    exact sin_ne_zero_of_notMem_freeLattice (notMem_freeLattice_of_separated hr hz.2)
  obtain ⟨C, hC⟩ := (hK.image_of_continuousOn hc).isBounded.exists_norm_le
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro z hz hsep
  obtain ⟨n, hn⟩ := exists_centered_real_part (z/2)
  let w := z-(Real.pi : ℂ)*(2*n)
  have hwr : |w.re| ≤ Real.pi := by
    have he : w.re = 2*((z/2).re-Real.pi*n) := by simp [w]; ring
    rw [he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hwi : w.im = z.im := by simp [w]
  have hw : w ∈ K := by
    refine ⟨?_, separated_sub_even_center hsep n⟩
    simp only [mem_closedBall, dist_zero_right]
    exact (Complex.norm_le_abs_re_add_abs_im w).trans (by rw [hwi]; linarith)
  have he : sin w = sin z := by
    have he : (Real.pi : ℂ)*(2*n) = (n : ℂ)*(2*Real.pi) := by ring
    simp only [w, he, Complex.sin_sub_int_mul_two_pi]
  have hbound := hC _ ⟨w, hw, rfl⟩
  dsimp only at hbound
  rw [he] at hbound
  exact hbound.trans (le_max_left _ _)

/-- The exponential formula gives a lower bound in either imaginary direction. -/
theorem exp_abs_im_sub_exp_neg_abs_im_le_two_norm_sin (z : ℂ) :
    Real.exp |z.im|-Real.exp (-|z.im|) ≤ 2*‖sin z‖ := by
  have he : ‖exp (-z*I)-exp (z*I)‖ = 2*‖sin z‖ := by
    have h := congrArg norm (Complex.two_sin (x := z))
    simpa only [norm_mul, norm_I, mul_one, norm_ofNat] using h.symm
  have hu := norm_sub_norm_le (exp (-z*I)) (exp (z*I))
  have hl := norm_sub_norm_le (exp (z*I)) (exp (-z*I))
  simp only [norm_exp, mul_re, neg_re, neg_im, I_re, I_im, mul_zero, mul_one,
    zero_sub, neg_neg] at hu hl
  rw [he] at hu
  rw [norm_sub_rev, he] at hl
  rcases le_total 0 z.im with hz | hz
  · simpa only [abs_of_nonneg hz] using hu
  · simpa only [abs_of_nonpos hz, neg_neg] using hl

/-- Above imaginary height one, the normalized sine is bounded below by one quarter. -/
theorem exp_abs_im_le_four_norm_sin {z : ℂ} (hz : 1 ≤ |z.im|) :
    Real.exp |z.im| ≤ 4*‖sin z‖ := by
  have h₁ := Real.add_one_le_exp |z.im|
  have h₂ : Real.exp (-|z.im|) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h₃ := exp_abs_im_sub_exp_neg_abs_im_le_two_norm_sin z
  linarith

/-- One positive constant bounds the normalized reciprocal sine on the entire exterior. -/
theorem exists_bound_exp_im_div_sin_of_separated {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
      (∀ n : ℤ, r ≤ ‖z-(Real.pi : ℂ)*n‖) →
      ‖(Real.exp |z.im| : ℂ)/sin z‖ ≤ C := by
  obtain ⟨B, hB, hb⟩ := exists_bound_sin_inv_strip hr 1
  refine ⟨max 4 (Real.exp 1*B), lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro z hsep
  have hs := sin_ne_zero_of_notMem_freeLattice (notMem_freeLattice_of_separated hr hsep)
  by_cases hz : 1 ≤ |z.im|
  · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact ((div_le_iff₀ (norm_pos_iff.mpr hs)).mpr (exp_abs_im_le_four_norm_sin hz)).trans
      (le_max_left _ _)
  · have hi : Real.exp |z.im| ≤ Real.exp 1 := Real.exp_le_exp.mpr (le_of_not_ge hz)
    rw [div_eq_mul_inv, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul hi (hb z (le_of_not_ge hz) hsep) (norm_nonneg _) (Real.exp_pos _).le).trans
      (le_max_right _ _)

end NLS.ZakharovShabat
