import NLS.KdV.PseudomeasureWeightedGaps

/-! The actual complex high spectral gap inherits any common bound
for both couplings on the full strip, without choosing a square-root branch. -/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.KdV

theorem EndpointHillComplexPair.gap_le_of_coupling_envelope
    (n : ℕ) (hn : 1 ≤ n) (q : WeightedCoeff (SpectralWeight.one.negativeSobolev 0) ⊤)
    (hs : endpointHillConstant 0*(n:ℝ)^((0:ℝ)-1/2)*‖q‖ ≤ 1/2)
    (p : EndpointHillComplexPair 0 (by norm_num) (by norm_num) q n)
    (W U L : ℝ) (hW : 0 < W) (hU : 0 ≤ U) (hL : 0 ≤ L)
    (hbc : ∀ z ∈ reducedHillStrip n,
      W*‖endpointUpperCoupling 0 (by norm_num) (by norm_num) n (q,z)‖ ≤ U ∧
        W*‖endpointLowerCoupling 0 (by norm_num) (by norm_num) n (q,z)‖ ≤ L) :
    W*‖p.right-p.left‖ ≤ Real.sqrt 6*(U+L) := by
  have hbound (z : ℂ) (hz : z ∈ reducedHillStrip n) :
      Real.sqrt ‖endpointUpperCoupling 0 (by norm_num) (by norm_num) n (q,z)*
        endpointLowerCoupling 0 (by norm_num) (by norm_num) n (q,z)‖ ≤ (U+L)/W := by
    obtain ⟨hb,hc⟩ := hbc z hz
    have hb' := (le_div_iff₀ hW).mpr (by simpa only [mul_comm] using hb)
    have hc' := (le_div_iff₀ hW).mpr (by simpa only [mul_comm] using hc)
    apply Real.sqrt_le_iff.mpr
    refine ⟨div_nonneg (add_nonneg hU hL) hW.le,?_⟩
    rw [norm_mul]
    have hprod := mul_le_mul hb' hc' (norm_nonneg _) (div_nonneg hU hW.le)
    have hu : 0 ≤ U/W := div_nonneg hU hW.le
    have hl : 0 ≤ L/W := div_nonneg hL hW.le
    rw [add_div]
    nlinarith [sq_nonneg (U/W),sq_nonneg (L/W)]
  have hrad : endpointCouplingRadius 0 (by norm_num) (by norm_num) n q ≤ (U+L)/W := by
    unfold endpointCouplingRadius
    apply csSup_le
    · refine ⟨_,(freeHillValue n:ℂ),?_,rfl⟩
      change |(freeHillValue n:ℂ).re-freeHillValue n| ≤ 6*(n:ℝ)
      simp only [Complex.ofReal_re, sub_self, abs_zero]
      positivity
    · rintro _ ⟨z,hz,rfl⟩
      exact hbound z hz
  have hl := (mem_endpointHillSpectrum_iff_determinant 0 (by norm_num) (by norm_num)
    n hn p.left p.left_mem q hs).mp p.left_spectral
  have hr := (mem_endpointHillSpectrum_iff_determinant 0 (by norm_num) (by norm_num)
    n hn p.right p.right_mem q hs).mp p.right_spectral
  have hg := (endpointReduced_roots_separation_sqrt 0 (by norm_num) (by norm_num)
    n hn q hs p.right p.left p.right_mem p.left_mem hr hl).trans
      (mul_le_mul_of_nonneg_left hrad (Real.sqrt_nonneg 6))
  have hh : ‖p.right-p.left‖ ≤ (Real.sqrt 6*(U+L))/W := hg.trans_eq (by ring)
  simpa only [mul_comm] using (le_div_iff₀ hW).mp hh

end NLS.KdV
