import NLS.KdV.HillL2HighGapPairs
import NLS.ZakharovShabat.LocallyUniformExteriorProducts
import NLS.ZakharovShabat.VerticalStrips

/-! # Uniform confinement of actual high L2 Hill branch points

The canonical product excludes roots outside any prescribed small free
frequency disc, on one complex L2 neighborhood and one high cutoff.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV

theorem exists_hillL2_small_gap_coverage (q : Coeff 2)
    (r : ℝ) (hr : 0 < r) (hrpi : r ≤ Real.pi/4) :
    ∃ N : ℕ, ∃ V : Set (Coeff 2), 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ a ∈ V, ∀ n : ℤ, N ≤ n.natAbs →
        ∀ z ∈ closedBall ((Real.pi : ℂ)*n) (Real.pi/4),
          hillL2Radicand a (z^2) = 0 → z ∈ ball ((Real.pi : ℂ)*n) r := by
  obtain ⟨U,hU,_,hq,_,R,hbound⟩ := exists_uniform_exterior_canonicalProducts
    (by simp : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num : 1 < (2 : ℝ≥0∞))
    (hillL2CoefficientPotential q) hr hrpi (by norm_num : (0 : ℝ) < 1/2)
  obtain ⟨N,hN,hNR⟩ := exists_free_center_cutoff R (Real.pi/4)
  refine ⟨N,hillL2CoefficientPotential ⁻¹' U,hN,
    hU.preimage continuous_hillL2CoefficientPotential,hq,?_⟩
  intro a ha n hn z hz hzero
  have hdist : ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/4 := by
    simpa only [mem_closedBall,dist_eq_norm] using hz
  have hre : |z.re-Real.pi*n| ≤ Real.pi/2 := by
    have h := (abs_re_le_norm (z-(Real.pi : ℂ)*n)).trans hdist
    simp only [sub_re,mul_re,ofReal_re,ofReal_im,intCast_re,intCast_im,
      mul_zero,sub_zero] at h
    linarith [Real.pi_pos]
  by_contra hnot
  have hfar : r ≤ ‖z-(Real.pi : ℂ)*n‖ := by
    simpa only [mem_ball,dist_eq_norm,not_lt] using hnot
  have hsep (m : ℤ) : r ≤ ‖z-(Real.pi : ℂ)*m‖ := by
    have h := verticalStrip_denominator_lower (n := n) (m := m) hr hrpi ⟨hre,hfar⟩
    have hnonneg := mul_nonneg hr.le (abs_nonneg (((m-n : ℤ) : ℝ)))
    nlinarith
  have hnorm : R ≤ ‖z‖ := by
    have hcenter : ‖(Real.pi : ℂ)*n‖ = Real.pi*(n.natAbs : ℝ) := by
      simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,
        Complex.norm_intCast,Nat.cast_natAbs,Int.cast_abs]
    have ht := norm_sub_norm_le ((Real.pi : ℂ)*n) z
    rw [norm_sub_rev,hcenter] at ht
    have hnreal : (N : ℝ) ≤ n.natAbs := by exact_mod_cast hn
    nlinarith [Real.pi_pos]
  have hP : canonicalPeriodicProduct (by simp) (hillL2CoefficientPotential a) z = 0 := by
    rw [canonicalPeriodic_eq_discriminant_sq_sub_four _ (hillL2CoefficientPotential_even a),
      canonicalDiscriminant_hillL2CoefficientPotential]
    exact hzero
  have h := (hbound _ ha (hillL2CoefficientPotential_even a) z hnorm hsep).1
  rw [hP,zero_div,zero_sub,norm_neg,norm_one] at h
  norm_num at h

end NLS.KdV
