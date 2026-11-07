import NLS.KdV.PseudomeasureWeightedCoefficients
import NLS.KdV.PseudomeasureComplexPairs

/-! General source spectral weights control the ACTUAL original complex high gaps. -/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.KdV

variable (w : SpectralWeight) (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
variable (n : ℕ) (hn : 1 ≤ n) (q : WeightedCoeff (w.negativeSobolev r) ⊤)
variable (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)

include hn hs in
/-- The actual physical coupling product retains the FULL general spectral weight. -/
theorem sqrt_endpointCouplingProduct_le_weighted_norm (z : ℂ) (hz : z ∈ reducedHillStrip n) :
    Real.sqrt ‖endpointUpperCoupling r hr hr1 n (endpointForgetWeight w r q,z)*
      endpointLowerCoupling r hr hr1 n (endpointForgetWeight w r q,z)‖ ≤
        2*‖q‖ / w.negativeSobolev r (2*(n:ℤ)) := by
  have hW := (w.negativeSobolev r).positive (2*(n:ℤ))
  obtain ⟨hplus, hminus⟩ := endpointCouplings_weighted_le w r hr hr1 n hn z hz q hs
  have hp : ‖endpointUpperCoupling r hr hr1 n (endpointForgetWeight w r q,z)‖ ≤
      2*‖q‖ / w.negativeSobolev r (2*(n:ℤ)) := by
    apply (le_div_iff₀ hW).mpr
    simpa only [mul_comm] using hplus
  have hm : ‖endpointLowerCoupling r hr hr1 n (endpointForgetWeight w r q,z)‖ ≤
      2*‖q‖ / w.negativeSobolev r (2*(n:ℤ)) := by
    apply (le_div_iff₀ hW).mpr
    simpa only [mul_comm] using hminus
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  rw [norm_mul, pow_two]
  exact mul_le_mul hp hm (norm_nonneg _) (by positivity)

include hn hs in
/-- The supremum of the SAME full-strip physical coupling has the general-weight bound. -/
theorem endpointCouplingRadius_le_weighted_norm :
    endpointCouplingRadius r hr hr1 n (endpointForgetWeight w r q) ≤
      2*‖q‖ / w.negativeSobolev r (2*(n:ℤ)) := by
  unfold endpointCouplingRadius
  apply csSup_le
  · refine ⟨_, (freeHillValue n:ℂ), ?_, rfl⟩
    change |(freeHillValue n:ℂ).re-freeHillValue n| ≤ 6*(n:ℝ)
    simp only [Complex.ofReal_re, sub_self, abs_zero]
    positivity
  · rintro _ ⟨z, hz, rfl⟩
    exact sqrt_endpointCouplingProduct_le_weighted_norm w r hr hr1 n hn q hs z hz

include hr hr1 hn in
/-- The unsigned mode weight is controlled by the double-frequency source weight. -/
theorem negativeSobolev_mode_le_three_double :
    w.negativeSobolev r n ≤ 3*w.negativeSobolev r (2*(n:ℤ)) := by
  have hw : w n ≤ w (2*(n:ℤ)) := w.mono_abs (by
    rw [abs_of_nonneg (Int.natCast_nonneg n), abs_of_nonneg (by positivity : (0:ℤ) ≤ 2*(n:ℤ))]
    omega)
  have hS : Weight.sobolev r (2*(n:ℤ)) ≤ 3*Weight.sobolev r n := by
    apply (sobolev_two_mode_le r hr hr1 n hn).trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 3)
    simp only [Weight.sobolev_apply, Int.cast_natCast, abs_of_nonneg (show (0:ℝ) ≤ n by positivity)]
    exact Real.rpow_le_rpow (by positivity) (by linarith) hr
  simp only [SpectralWeight.negativeSobolev_apply]
  rw [show 3*(w (2*(n:ℤ))/Weight.sobolev r (2*(n:ℤ))) =
      (3*w (2*(n:ℤ)))/Weight.sobolev r (2*(n:ℤ)) by ring]
  apply (div_le_div_iff₀ ((Weight.sobolev r).positive _) ((Weight.sobolev r).positive _)).mpr
  exact (mul_le_mul hw hS ((Weight.sobolev r).positive _).le (w.positive _).le).trans_eq (by ring)

include hn hs in
/-- The double-frequency weighted gap is an estimate for the actual original complex pair. -/
theorem EndpointHillComplexPair.double_weighted_gap_le
    (p : EndpointHillComplexPair r hr hr1 (endpointForgetWeight w r q) n) :
    w.negativeSobolev r (2*(n:ℤ))*‖p.right-p.left‖ ≤ 2*Real.sqrt 6*‖q‖ := by
  have hv := endpointHill_small_forgetWeight w r hr1 n q hs
  have hl := (mem_endpointHillSpectrum_iff_determinant r hr hr1 n hn p.left p.left_mem _ hv).mp p.left_spectral
  have hrr := (mem_endpointHillSpectrum_iff_determinant r hr hr1 n hn p.right p.right_mem _ hv).mp p.right_spectral
  have he := (endpointReduced_roots_separation_sqrt r hr hr1 n hn _ hv p.right p.left
    p.right_mem p.left_mem hrr hl).trans
      (mul_le_mul_of_nonneg_left (endpointCouplingRadius_le_weighted_norm w r hr hr1 n hn q hs)
        (Real.sqrt_nonneg 6))
  have hb : ‖p.right-p.left‖ ≤ (2*Real.sqrt 6*‖q‖)/w.negativeSobolev r (2*(n:ℤ)) := by
    exact he.trans_eq (by ring)
  simpa only [mul_comm] using
    (le_div_iff₀ ((w.negativeSobolev r).positive (2*(n:ℤ)))).mp hb

include hn hs in
/-- Full original source spectral weights give a uniform high-gap bound with no loss of exponent. -/
theorem EndpointHillComplexPair.general_weighted_gap_le
    (p : EndpointHillComplexPair r hr hr1 (endpointForgetWeight w r q) n) :
    w.negativeSobolev r n*‖p.right-p.left‖ ≤ 6*Real.sqrt 6*‖q‖ := by
  have hW := negativeSobolev_mode_le_three_double w r hr hr1 n hn
  have he := mul_le_mul_of_nonneg_right hW (norm_nonneg (p.right-p.left))
  have hg := p.double_weighted_gap_le w r hr hr1 n hn q hs
  nlinarith

end NLS.KdV
