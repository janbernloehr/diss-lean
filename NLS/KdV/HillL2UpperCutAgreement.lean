import NLS.KdV.HillL2RegularBoundary
import NLS.KdV.HillL2GapBoundaryValues

/-! # The global upper primitive agrees with every normalized high cut

A single source-circle anchor fixes the root on the connected upper
half-disc; equality of derivatives then fixes the primitive itself.
Consequently the intrinsic upper boundary has the exact high indexed
phase, including both endpoints of an open gap.
-/

noncomputable section
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
namespace NLS.KdV

theorem HillL2NormalizedCutPrimitive.upper_source_agreement
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (n : ℕ) (hn : 1 ≤ n) (p : HillRealHighGapPair (SpectralWeight.one.toCoeff q) n)
    (R F : ℂ → ℂ) (h : HillL2NormalizedCutPrimitive (SpectralWeight.one.toCoeff q) n p R F) :
    EqOn R (fun z => hillL2ContinuedRoot (z, SpectralWeight.one.toCoeff q))
      (ball (freeHillValue n : ℂ) (7 * (n : ℝ) / 8) ∩ {z : ℂ | 0 < z.im}) ∧
    EqOn F (fun z => hillL2ContinuedPrimitive (z, SpectralWeight.one.toCoeff q))
      (ball (freeHillValue n : ℂ) (7 * (n : ℝ) / 8) ∩ {z : ℂ | 0 < z.im}) := by
  let U := ball (freeHillValue n : ℂ) (7 * (n : ℝ) / 8) ∩ {z : ℂ | 0 < z.im}
  let S : ℂ → ℂ := fun z => hillL2ContinuedRoot (z, SpectralWeight.one.toCoeff q)
  let P : ℂ → ℂ := fun z => hillL2ContinuedPrimitive (z, SpectralWeight.one.toCoeff q)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hUopen : IsOpen U := isOpen_ball.inter (isOpen_lt continuous_const continuous_im)
  have hUconv : Convex ℝ U := (convex_ball _ _).inter (convex_halfSpace_im_gt 0)
  have hcut (z : ℂ) (hz : z ∈ U) : z ∈
      ball (freeHillValue n : ℂ) (7 * (n : ℝ) / 8) \ segment ℝ (p.left : ℂ) p.right :=
    ⟨hz.1, not_mem_real_segment_of_im_ne_zero _ _ z hz.2.ne'⟩
  have hsource (z : ℂ) (hz : z ∈ U) : (z, SpectralWeight.one.toCoeff q) ∈ hillL2ContinuationDomain :=
    mem_hillL2ContinuationDomain_of_im_ne_zero q hq hr z hz.2.ne'
  have hSa : AnalyticOnNhd ℂ S U := fun z hz =>
    (analyticOnNhd_hillL2ContinuedRoot _ (hsource z hz)).comp
      (f := fun z : ℂ => (z, SpectralWeight.one.toCoeff q)) (analyticAt_id.prod analyticAt_const)
  have hPa : AnalyticOnNhd ℂ P U := fun z hz =>
    (analyticOnNhd_hillL2ContinuedPrimitive _ (hsource z hz)).comp
      (f := fun z : ℂ => (z, SpectralWeight.one.toCoeff q)) (analyticAt_id.prod analyticAt_const)
  have hR : AnalyticOnNhd ℂ R U := h.root_analytic.mono (fun z hz =>
    ⟨ball_subset_ball (by linarith) hz.1, (hcut z hz).2⟩)
  let a : ℂ := (freeHillValue n : ℂ) + ((3 * (n : ℝ) / 4 : ℝ) : ℂ) * I
  have haS : a ∈ sphere (freeHillValue n : ℂ) (3 * (n : ℝ) / 4) := by
    simp only [a, mem_sphere, dist_eq_norm, add_sub_cancel_left, norm_mul, norm_I,
      mul_one, norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 3 * (n : ℝ) / 4)]
  have ha : a ∈ U := by
    refine ⟨?_, ?_⟩
    · rw [mem_ball]
      linarith [mem_sphere.mp haS]
    · change 0 < a.im
      simp only [a, add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re,
        mul_one, mul_zero, add_zero, zero_add]
      positivity
  have hmatchR : EqOn R S U := hUconv.isPreconnected.eq_of_sq_eq
    hR.continuousOn hSa.continuousOn (fun z hz => by
      change R z ^ 2 = S z ^ 2
      exact (h.root_data z ⟨ball_subset_ball (by linarith) hz.1, (hcut z hz).2⟩).2.trans
        (hillL2ContinuedRoot_sq _ (hsource z hz)).symm)
    (fun {z} hz => hillL2ContinuedRoot_ne_zero _ (hsource z hz)) ha (h.root_source a haS)
  refine ⟨hmatchR, ?_⟩
  apply hUopen.eqOn_of_deriv_eq hUconv.isPreconnected
    (h.analytic.mono (fun z hz => hcut z hz)).differentiableOn hPa.differentiableOn
    (fun z hz => ?_) ha (h.source a haS)
  rw [(h.hasDerivAt z (hcut z hz)).deriv,
    (hasDerivAt_hillL2ContinuedPrimitive _ (hsource z hz)).deriv, hmatchR hz]

theorem HillL2NormalizedCutPrimitive.upper_boundary_indexed
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (n : ℕ) (hn : 2 ≤ n) (hcut : 8 * ‖q‖ ≤ (n : ℝ))
    (p : HillRealHighGapPair (SpectralWeight.one.toCoeff q) n) (hopen : p.left ≠ p.right)
    (R F : ℂ → ℂ) (h : HillL2NormalizedCutPrimitive (SpectralWeight.one.toCoeff q) n p R F)
    (x : ℝ) (hx : x ∈ Icc p.left p.right) :
    hillL2UpperBoundaryPrimitive (SpectralWeight.one.toCoeff q) x =
      (hillRealGapProfile (SpectralWeight.one.toCoeff q) n x : ℂ) - I * (n : ℂ) * Real.pi := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hloc := p.localization q hq n (by omega) hcut
  have hxB : (x : ℂ) ∈ ball (freeHillValue n : ℂ) (7 * (n : ℝ) / 8) := by
    rw [mem_ball, dist_eq_norm, ← ofReal_sub, norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith [(abs_le.mp hloc.1).1, (abs_le.mp hloc.2).2, hx.1, hx.2]
  have hb := (h.gap_boundary_values q hq hr n hn hcut p hopen R F x hx).1.sub_const
    (I * (n : ℂ) * Real.pi)
  have hlim : Tendsto (fun z => hillL2ContinuedPrimitive (z, SpectralWeight.one.toCoeff q))
      (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ))
      (𝓝 ((hillRealGapProfile (SpectralWeight.one.toCoeff q) n x : ℂ) - I * (n : ℂ) * Real.pi)) := by
    apply hb.congr'
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (isOpen_ball.mem_nhds hxB)] with z hz hzB
    simp only [add_sub_cancel_right]
    exact (h.upper_source_agreement q hq hr n (by omega) p R F).2 ⟨hzB, hz⟩
  let := real_upper_nhds_neBot x
  exact hlim.limUnder_eq

end NLS.KdV
