import NLS.KdV.ClassicalL2PrimitiveAgreement
import NLS.KdV.ClassicalHillPrimitiveSheets
import NLS.KdV.HillL2PrimitiveReflection
import NLS.KdV.HillRealTraceParity
import NLS.ComplexAnalysis.PositiveRealPart

/-! # The physical half-plane sheets for actual real L2 Hill potentials

Fourier density transfers the continuous scalar Green sign to a weak
inequality for the actual L2 primitive. The maximum modulus principle
and nonconstancy of the actual discriminant make the inequality strict.
No spectral cutoff or NLS real-type condition is used.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ComplexConjugate
open NLS.ComplexAnalysis
namespace NLS.KdV

theorem hillL2Discriminant_not_constant
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) :
    ¬ ∃ c : ℂ, ∀ z : ℂ, hillL2Discriminant (SpectralWeight.one.toCoeff q) z = c := by
  rintro ⟨c, hc⟩
  have h0 : hillL2Discriminant (SpectralWeight.one.toCoeff q) (hillRealLabels q hq hr 0) = 2 := by
    simpa using hillRealLabels_trace_parity q hq hr 0
  have h1 : hillL2Discriminant (SpectralWeight.one.toCoeff q) (hillRealLabels q hq hr 1) = -2 := by
    simpa using hillRealLabels_trace_parity q hq hr 1
  have he : (2 : ℂ) = -2 := h0.symm.trans ((hc _).trans ((hc _).symm.trans h1))
  norm_num at he

/-- The scalar continuous-potential sheet sign is closed under L2
approximation at every nonreal upper energy. -/
theorem hillL2ContinuedPrimitive_re_nonneg
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (z : ℂ) (hz : 0 < z.im) :
    0 ≤ (hillL2ContinuedPrimitive (z, SpectralWeight.one.toCoeff q)).re := by
  let S : Coeff 2 → Coeff 2 := fun a => (1 / 2 : ℂ) • (a + star (Coeff.reflection a))
  have hS : Continuous S :=
    (continuous_id.add (Coeff.reflection.continuous.star)).const_smul (1 / 2 : ℂ)
  have hfix : S (SpectralWeight.one.toCoeff q) = SpectralWeight.one.toCoeff q := by
    ext k
    simp only [S, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.coeFn_add, Pi.add_apply,
      lp.star_apply, Coeff.reflection_apply, hr k, starRingEnd_apply, star_star]
    ring
  have hdom : (z, S (SpectralWeight.one.toCoeff q)) ∈ hillL2ContinuationDomain := by
    rw [hfix]
    exact mem_hillL2ContinuationDomain_of_im_ne_zero q hq hr z hz.ne'
  have hc : ContinuousAt (fun a => (hillL2ContinuedPrimitive (z, S a)).re)
      (SpectralWeight.one.toCoeff q) :=
    continuous_re.continuousAt.comp
      ((analyticOnNhd_hillL2ContinuedPrimitive _ hdom).continuousAt.comp
        (f := fun a : Coeff 2 => (z, S a))
        (continuous_const.prodMk hS).continuousAt)
  have hfinite (a : ℤ →₀ ℂ) :
      0 ≤ (hillL2ContinuedPrimitive (z, S (Coeff.ofFinsupp (p := 2) a))).re := by
    let Q := Fourier.continuousSynthesis (Coeff.ofFinsupp (p := 1) a)
    let P : C(AddCircle (2 : ℝ), ℂ) := (1 / 2 : ℂ) • (Q + star Q)
    have hQ : Fourier.continuousFourierCLM Q = Coeff.ofFinsupp (p := 2) a := by
      ext k
      rw [Fourier.continuousFourierCLM_apply]
      exact Fourier.fourierCoeff_continuousSynthesis _ k
    have hP : SpectralWeight.one.toCoeff (hillContinuousCoefficients P) = S (Coeff.ofFinsupp a) := by
      rw [toCoeff_hillContinuousCoefficients]
      dsimp only [P, S]
      rw [map_smul, map_add, Fourier.continuousFourierCLM_star, hQ]
    have hreal : ∀ t, (hillUnitPotentialCurve P t).im = 0 := by
      intro t
      simp [P, hillUnitPotentialCurve, Complex.mul_im]
    have hd := mem_classicalHillContinuationDomain_of_im_ne_zero _ hreal z hz.ne'
    rw [← hP, hillL2ContinuedPrimitive_eq_classical P z hd]
    exact (classicalHillContinuedPrimitive_re_pos _ hreal z hz).le
  have hcl : SpectralWeight.one.toCoeff q ∈ closure (range (Coeff.ofFinsupp (p := 2))) := by
    rw [(Coeff.denseRange_ofFinsupp (p := 2) (by simp)).closure_range]
    exact mem_univ _
  have hmap : MapsTo (fun a => (hillL2ContinuedPrimitive (z, S a)).re)
      (range (Coeff.ofFinsupp (p := 2))) (Ici (0 : ℝ)) := by
    rintro _ ⟨a, rfl⟩
    exact hfinite a
  have hmem := hc.continuousWithinAt.mem_closure hcl hmap
  simpa only [isClosed_Ici.closure_eq, hfix, mem_Ici] using hmem

/-- The actual source-normalized primitive selects the expanding
Floquet sheet on the entire upper energy half-plane. -/
theorem hillL2ContinuedPrimitive_re_pos
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (z : ℂ) (hz : 0 < z.im) :
    0 < (hillL2ContinuedPrimitive (z, SpectralWeight.one.toCoeff q)).re := by
  let F : ℂ → ℂ := fun w => hillL2ContinuedPrimitive (w, SpectralWeight.one.toCoeff q)
  let U : Set ℂ := {w | 0 < w.im}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_im
  have hF : AnalyticOnNhd ℂ F U :=
    (analyticOnNhd_hillL2ContinuedPrimitive_off_real q hq hr).mono (fun _ hw => hw.ne')
  have hnot : ¬ ∃ c : ℂ, ∀ w ∈ U, F w = c := by
    rintro ⟨c, hc⟩
    have hi : I ∈ U := by simp [U]
    have heq : hillL2Discriminant (SpectralWeight.one.toCoeff q) =ᶠ[𝓝 I]
        (fun _ => 2 * cosh c) := by
      filter_upwards [hU.mem_nhds hi] with w hw
      rw [← (hillL2ContinuedPrimitive_trace _
        (mem_hillL2ContinuationDomain_of_im_ne_zero q hq hr w hw.ne')).1]
      change 2 * cosh (F w) = 2 * cosh c
      rw [hc w hw]
    have hglobal := (analyticOnNhd_hillL2Discriminant (SpectralWeight.one.toCoeff q)).eqOn_of_preconnected_of_eventuallyEq
      analyticOnNhd_const isPreconnected_univ (mem_univ I) heq
    exact hillL2Discriminant_not_constant q hq hr ⟨2 * cosh c, fun w => hglobal (mem_univ w)⟩
  exact re_pos_of_analyticOnNhd_nonneg_not_constant F U hU
    (convex_halfSpace_im_gt 0).isPreconnected hF
    (fun w hw => hillL2ContinuedPrimitive_re_nonneg q hq hr w hw) hnot z hz

theorem hillL2ContinuedPrimitive_re_neg
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (z : ℂ) (hz : z.im < 0) :
    (hillL2ContinuedPrimitive (z, SpectralWeight.one.toCoeff q)).re < 0 := by
  have hp := hillL2ContinuedPrimitive_re_pos q hq hr (conj z) (by simpa only [conj_im] using neg_pos.mpr hz)
  rw [hillL2ContinuedPrimitive_conj _ hr z
    (mem_hillL2ContinuationDomain_of_im_ne_zero q hq hr z hz.ne), neg_re, conj_re] at hp
  linarith

theorem one_lt_norm_hillL2ContinuedMultiplier
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (z : ℂ) (hz : 0 < z.im) :
    1 < ‖hillL2ContinuedMultiplier (z, SpectralWeight.one.toCoeff q)‖ := by
  rw [← exp_hillL2ContinuedPrimitive _ (mem_hillL2ContinuationDomain_of_im_ne_zero q hq hr z hz.ne'),
    norm_exp, Real.one_lt_exp_iff]
  exact hillL2ContinuedPrimitive_re_pos q hq hr z hz

theorem norm_hillL2ContinuedMultiplier_lt_one
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (z : ℂ) (hz : z.im < 0) :
    ‖hillL2ContinuedMultiplier (z, SpectralWeight.one.toCoeff q)‖ < 1 := by
  rw [← exp_hillL2ContinuedPrimitive _ (mem_hillL2ContinuationDomain_of_im_ne_zero q hq hr z hz.ne),
    norm_exp, Real.exp_lt_one_iff]
  exact hillL2ContinuedPrimitive_re_neg q hq hr z hz

end NLS.KdV
