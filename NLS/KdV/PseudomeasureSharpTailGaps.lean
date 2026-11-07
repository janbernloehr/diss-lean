import NLS.KdV.PseudomeasureSharpTailWeights
import NLS.KdV.PseudomeasureWeightedGaps

/-! The literal linear tail and quadratic remainder bound for actual
complex physical pairs, with constants adequate for Lemma 2.12. -/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.KdV

variable (w : SpectralWeight) (r : ℝ) (hr : 0≤r) (hr1 : r<1/2)
variable (N n : ℕ) (hn : 2≤n) (hN : N≤n)
variable (q : WeightedCoeff (w.negativeSobolev r) ⊤)
variable (hs : 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖≤1/2)

include hn hN hs in
/-- Each coupling is controlled by the actual Fourier tail, including its boundary. -/
theorem wideEndpointCouplings_tail_le (z : ℂ) (hz : z ∈ wideHillStrip n) :
    let B := ‖WeightedCoeff.fourierTail (w.negativeSobolev r) N q‖+
      2*(13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖)*‖q‖
    w.negativeSobolev r (2*(n:ℤ))*‖endpointUpperCoupling r hr hr1 n (endpointForgetWeight w r q,z)‖≤B ∧
    w.negativeSobolev r (2*(n:ℤ))*‖endpointLowerCoupling r hr hr1 n (endpointForgetWeight w r q,z)‖≤B := by
  have hplus := negativeSobolev_fourierTail_coefficient w r N q (2*(n:ℤ)) (by norm_num [Int.natAbs_mul]; omega)
  have hminus := negativeSobolev_fourierTail_coefficient w r N q (-(2*(n:ℤ))) (by norm_num [Int.natAbs_mul]; omega)
  rw [SpectralWeight.negativeSobolev_neg] at hminus
  have he := wideEndpointCoefficients_weighted_errors_le w r hr hr1 n hn z hz q hs
  have hW := ((w.negativeSobolev r).positive (2*(n:ℤ))).le
  have htplus := mul_le_mul_of_nonneg_left (norm_le_norm_sub_add
    (endpointUpperCoupling r hr hr1 n (endpointForgetWeight w r q,z)) (q.val (2*(n:ℤ)))) hW
  have htminus := mul_le_mul_of_nonneg_left (norm_le_norm_sub_add
    (endpointLowerCoupling r hr hr1 n (endpointForgetWeight w r q,z)) (q.val (-(2*(n:ℤ))))) hW
  constructor
  · nlinarith [he.2.1]
  · nlinarith [he.2.2]

include hn hN hs in
theorem EndpointHillComplexPair.sharp_tail_gap_le
    (p : EndpointHillComplexPair r hr hr1 (endpointForgetWeight w r q) n) :
    w.negativeSobolev r n*‖p.right-p.left‖≤
      4*‖WeightedCoeff.fourierTail (w.negativeSobolev r) N q‖+
        8*(13*endpointHillConstant r)*(n:ℝ)^(r-1/2)*‖q‖^2 := by
  let W := w.negativeSobolev r (2*(n:ℤ))
  let B := ‖WeightedCoeff.fourierTail (w.negativeSobolev r) N q‖+
    2*(13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖)*‖q‖
  have hW : 0<W := (w.negativeSobolev r).positive _
  have hB : 0≤B := by dsimp [B]; positivity [endpointHillConstant_pos r hr1]
  have hb (z : ℂ) (hz : z ∈ reducedHillStrip n) :
      Real.sqrt ‖endpointUpperCoupling r hr hr1 n (endpointForgetWeight w r q,z)*
        endpointLowerCoupling r hr hr1 n (endpointForgetWeight w r q,z)‖≤B/W := by
    have he := wideEndpointCouplings_tail_le w r hr hr1 N n hn hN q hs z (reducedHillStrip_subset_wide n hz)
    have hplus : ‖endpointUpperCoupling r hr hr1 n (endpointForgetWeight w r q,z)‖≤B/W :=
      (le_div_iff₀ hW).mpr (by simpa only [W,B,mul_comm] using he.1)
    have hminus : ‖endpointLowerCoupling r hr hr1 n (endpointForgetWeight w r q,z)‖≤B/W :=
      (le_div_iff₀ hW).mpr (by simpa only [W,B,mul_comm] using he.2)
    apply Real.sqrt_le_iff.mpr
    refine ⟨div_nonneg hB hW.le,?_⟩
    rw [norm_mul,pow_two]
    exact mul_le_mul hplus hminus (norm_nonneg _) (div_nonneg hB hW.le)
  have hrad : endpointCouplingRadius r hr hr1 n (endpointForgetWeight w r q)≤B/W := by
    unfold endpointCouplingRadius
    apply csSup_le
    · exact ⟨_,wideHillCenter n 0,wideHillCenter_mem n 0,rfl⟩
    · rintro _ ⟨z,hz,rfl⟩
      exact hb z hz
  have hsv := wideEndpointHill_small_forgetWeight w r hr1 n q hs
  have hv := endpointHill_small_of_wide_small r hr1 n (endpointForgetWeight w r q) hsv
  have hl := (mem_endpointHillSpectrum_iff_determinant r hr hr1 n (by omega) p.left p.left_mem _ hv).mp p.left_spectral
  have hrr := (mem_endpointHillSpectrum_iff_determinant r hr hr1 n (by omega) p.right p.right_mem _ hv).mp p.right_spectral
  have hsep := (endpointReduced_roots_separation_sqrt r hr hr1 n (by omega) _ hv
    p.right p.left p.right_mem p.left_mem hrr hl).trans
      (mul_le_mul_of_nonneg_left hrad (Real.sqrt_nonneg 6))
  have hweight := negativeSobolev_mode_le_sqrt_two_double w r hr hr1 n
  have hsqrt : Real.sqrt 2*Real.sqrt 6≤4 := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
    exact Real.sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
  calc
    _ ≤ (Real.sqrt 2*W)*‖p.right-p.left‖ := mul_le_mul_of_nonneg_right hweight (norm_nonneg _)
    _ ≤ (Real.sqrt 2*W)*(Real.sqrt 6*(B/W)) :=
      mul_le_mul_of_nonneg_left hsep (mul_nonneg (Real.sqrt_nonneg _) hW.le)
    _ = (Real.sqrt 2*Real.sqrt 6)*B := by field_simp [hW.ne']
    _ ≤ 4*B := mul_le_mul_of_nonneg_right hsqrt hB
    _ = _ := by dsimp [B]; ring

end NLS.KdV
