import NLS.ZakharovShabat.ResonantDiagonalCenter

/-!
# Closing a resonant pair at its diagonal center

Vanishing of both actual off-diagonal coefficients at the diagonal
center forces every determinant zero in the full strip to be that
center. Cauchy's estimate controls the coefficients away from the
center. The argument uses the actual determinant, and applies to
complex sources as well as real sources.
-/

noncomputable section
namespace NLS.ZakharovShabat

/-- The off-diagonal strip bound gives the corresponding quarter
Lipschitz bound on the refined disc. -/
theorem norm_offDiagonal_sub_le_on_refined_disk (n : ℤ) (b : ℂ → ℂ)
    (hb : AnalyticOnNhd ℂ b (resonantStrip n))
    (hbound : ∀ z ∈ resonantStrip n, ‖b z‖ ≤ Real.pi/16)
    (x y : ℂ) (hx : x ∈ refinedResonantDisk n) (hy : y ∈ refinedResonantDisk n) :
    ‖b x-b y‖ ≤ (1/4 : ℝ)*‖x-y‖ := by
  have hhalf : AnalyticOnNhd ℂ (fun z => b z/2) (resonantStrip n) := by
    intro z hz
    exact (hb z hz).div_const
  have hhalfbound (z : ℂ) (hz : z ∈ resonantStrip n) : ‖b z/2‖ ≤ Real.pi/32 := by
    rw [norm_div]
    norm_num
    linarith [hbound z hz]
  have h := norm_diagonal_sub_le_on_refined_disk n _ hhalf hhalfbound x y hx hy
  have heq : b x/2-b y/2 = (b x-b y)/2 := by ring
  rw [heq,norm_div] at h
  norm_num at h
  linarith

/-- If both off-diagonal entries vanish at the diagonal center, the
full-strip determinant has exactly that zero. The hypotheses are the
numerical bounds already proved locally uniformly for distant strips. -/
theorem resonant_quadratic_zero_iff_eq_diagonalCenter
    (n : ℤ) (a b d : ℂ → ℂ)
    (ha : AnalyticOnNhd ℂ a (resonantStrip n))
    (hb : AnalyticOnNhd ℂ b (resonantStrip n))
    (hd : AnalyticOnNhd ℂ d (resonantStrip n))
    (hbound : ∀ z ∈ resonantStrip n,
      ‖a z‖ ≤ Real.pi/32 ∧ ‖b z‖ ≤ Real.pi/16 ∧ ‖d z‖ ≤ Real.pi/16)
    (ζ : ℂ) (hζ : ζ ∈ refinedResonantDisk n)
    (hfix : ζ = (Real.pi : ℂ)*n+a ζ)
    (hbzero : b ζ = 0) (hdzero : d ζ = 0)
    (z : ℂ) (hz : z ∈ resonantStrip n) :
    (z-(Real.pi : ℂ)*n-a z)^2-b z*d z = 0 ↔ z = ζ := by
  constructor
  · intro hzero
    have hlocal := norm_resonant_quadratic_root_le
      (z-(Real.pi : ℂ)*n) (a z) (b z) (d z)
      (hbound z hz).1 (hbound z hz).2.1 (hbound z hz).2.2 hzero
    have hzdisk : z ∈ refinedResonantDisk n := by
      change dist z ((Real.pi : ℂ)*n) < Real.pi/4
      rw [dist_eq_norm]
      exact hlocal.trans_lt (by linarith [Real.pi_pos])
    have hab := norm_diagonal_sub_le_on_refined_disk n a ha
      (fun w hw => (hbound w hw).1) z ζ hzdisk hζ
    have hbb := norm_offDiagonal_sub_le_on_refined_disk n b hb
      (fun w hw => (hbound w hw).2.1) z ζ hzdisk hζ
    have hdb := norm_offDiagonal_sub_le_on_refined_disk n d hd
      (fun w hw => (hbound w hw).2.2) z ζ hzdisk hζ
    rw [hbzero,sub_zero] at hbb
    rw [hdzero,sub_zero] at hdb
    have hsq : ‖z-(Real.pi : ℂ)*n-a z‖^2 = ‖b z‖*‖d z‖ := by
      simpa only [norm_pow,norm_mul] using congrArg norm (sub_eq_zero.mp hzero)
    have hmul := mul_le_mul hbb hdb (norm_nonneg _) (by positivity)
    have hsplit : z-ζ = (z-(Real.pi : ℂ)*n-a z)+(a z-a ζ) := by
      calc
        z-ζ = z-((Real.pi : ℂ)*n+a ζ) := congrArg (fun t => z-t) hfix
        _ = _ := by ring
    have hlin : ‖z-ζ‖ ≤ ‖z-(Real.pi : ℂ)*n-a z‖+(1/8 : ℝ)*‖z-ζ‖ := by
      calc
        _ = ‖(z-(Real.pi : ℂ)*n-a z)+(a z-a ζ)‖ := congrArg norm hsplit
        _ ≤ ‖z-(Real.pi : ℂ)*n-a z‖+‖a z-a ζ‖ := norm_add_le _ _
        _ ≤ _ := add_le_add le_rfl hab
    have hres : (7/8 : ℝ)*‖z-ζ‖ ≤ ‖z-(Real.pi : ℂ)*n-a z‖ := by linarith
    have hlower := mul_self_le_mul_self (by positivity : 0 ≤ (7/8 : ℝ)*‖z-ζ‖) hres
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (z-ζ)]
  · rintro rfl
    have hres : z-(Real.pi : ℂ)*n-a z = 0 := by
      rw [sub_sub]
      exact sub_eq_zero.mpr hfix
    simp only [hres,hbzero,hdzero,zero_pow (by norm_num : 2 ≠ 0),zero_mul,sub_zero]

end NLS.ZakharovShabat
