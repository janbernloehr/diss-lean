import NLS.ComplexAnalysis.RealGapEllipseIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! # Dominated convergence for shrinking real-gap ellipses -/

noncomputable section
open Set Metric Complex Filter MeasureTheory
open scoped unitInterval Topology
namespace NLS.ComplexAnalysis

/-- A bounded numerator and convergent boundary values give convergence
of the pulled-back integral on either angular half of the ellipse.
The interval endpoints can be discarded as null sets. -/
theorem tendsto_realGapEllipse_intervalIntegral
    (f : ℂ → ℂ) (g : ℝ → ℂ) (c d a b ε₀ M : ℝ)
    (hd : 0 ≤ d) (hab : a ≤ b) (hε₀ : 0 < ε₀) (hM : 0 ≤ M)
    (hcont : ∀ ε ∈ Ioo 0 ε₀, Continuous (fun θ => f (realGapEllipse c d ε θ)))
    (hbound : ∀ ε ∈ Ioo 0 ε₀, ∀ θ ∈ Icc a b, ‖f (realGapEllipse c d ε θ)‖ ≤ M)
    (hlim : ∀ θ ∈ Ioo a b,
      Tendsto (fun ε => f (realGapEllipse c d ε θ)) (𝓝[>] 0) (𝓝 (g θ))) :
    Tendsto (fun ε => ∫ θ in a..b,
      deriv (realGapEllipse c d ε) θ * f (realGapEllipse c d ε θ)) (𝓝[>] 0)
      (𝓝 (∫ θ in a..b, (((-d * Real.sin θ : ℝ) : ℂ)) * g θ)) := by
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Ioo 0 ε₀ := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (eventually_lt_nhds hε₀)] with ε hε hε₀'
    exact ⟨hε, hε₀'⟩
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (bound := fun _ => (d + 2 * ε₀) * M)
  · filter_upwards [hsmall] with ε hε
    have hderiv : Continuous (fun θ => deriv (realGapEllipse c d ε) θ) := by
      simp_rw [(hasDerivAt_realGapEllipse c d ε _).deriv]
      fun_prop
    exact (hderiv.mul (hcont ε hε)).aestronglyMeasurable
  · filter_upwards [hsmall] with ε hε
    refine Eventually.of_forall fun θ hθ => ?_
    have hθ' : θ ∈ Icc a b := by
      exact ⟨(show θ ∈ Ioc a b from by simpa [uIoc_of_le hab] using hθ).1.le,
        (show θ ∈ Ioc a b from by simpa [uIoc_of_le hab] using hθ).2⟩
    rw [norm_mul]
    apply (mul_le_mul_of_nonneg_right
      (norm_deriv_realGapEllipse_le c d ε θ hd hε.1.le) (norm_nonneg _)).trans
    apply (mul_le_mul_of_nonneg_left (hbound ε hε θ hθ') (add_nonneg hd (mul_nonneg (by norm_num) hε.1.le))).trans
    exact mul_le_mul_of_nonneg_right (by linarith [hε.2]) hM
  · exact intervalIntegrable_const
  · have hae : ∀ᵐ θ : ℝ ∂volume, θ ≠ b := by simp [ae_iff]
    filter_upwards [hae] with θ hθ hθab
    have hθ' : θ ∈ Ioc a b := by simpa [uIoc_of_le hab] using hθab
    exact ((tendsto_deriv_realGapEllipse c d θ).mono_left nhdsWithin_le_nhds).mul
      (hlim θ ⟨hθ'.1, lt_of_le_of_ne hθ'.2 hθ⟩)

/-- The limiting real cosine parameterization has the usual signed Jacobian. -/
theorem integral_real_cosine_pullback (g : ℝ → ℂ) (c d a b : ℝ)
    (hd : 0 ≤ d) (hg : ContinuousOn g (Icc (c - d) (c + d))) :
    (∫ θ in a..b, (((-d * Real.sin θ : ℝ) : ℂ)) * g (c + d * Real.cos θ)) =
      ∫ x in (c + d * Real.cos a)..(c + d * Real.cos b), g x := by
  have hderiv (θ : ℝ) :
      HasDerivAt (fun t => c + d * Real.cos t) (-d * Real.sin θ) θ := by
    simpa only [zero_add, mul_neg, neg_mul] using!
      (hasDerivAt_const θ c).add ((Real.hasDerivAt_cos θ).const_mul d)
  simpa only [Function.comp_def, Complex.real_smul] using!
    (intervalIntegral.integral_deriv_smul_comp'
      (fun θ _ => hderiv θ) (by fun_prop)
      (hg.mono (by
        rintro x ⟨θ, _, rfl⟩
        exact realGapEllipse_limit_mem_Icc c d θ hd)) (a := a) (b := b))

/-- Shrinking clockwise ellipses recover the upper-minus-lower jump
integrated from left to right. Boundedness supplies an integrable
majorant; one-sided pointwise limits alone are not substituted under
the integral. -/
theorem tendsto_curveIntegral_realGapEllipse
    (f : ℂ → ℂ) (lower upper : ℝ → ℂ) (c d ε₀ M : ℝ)
    (hd : 0 ≤ d) (hε₀ : 0 < ε₀) (hM : 0 ≤ M)
    (hcont : ∀ ε ∈ Ioo 0 ε₀, Continuous (fun θ => f (realGapEllipse c d ε θ)))
    (hbound : ∀ ε ∈ Ioo 0 ε₀, ∀ θ ∈ Icc 0 (2 * Real.pi),
      ‖f (realGapEllipse c d ε θ)‖ ≤ M)
    (hlcont : ContinuousOn lower (Icc (c - d) (c + d)))
    (hucont : ContinuousOn upper (Icc (c - d) (c + d)))
    (hlower : ∀ x ∈ Icc (c - d) (c + d),
      Tendsto f (𝓝[{z : ℂ | z.im < 0}] (x : ℂ)) (𝓝 (lower x)))
    (hupper : ∀ x ∈ Icc (c - d) (c + d),
      Tendsto f (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 (upper x))) :
    Tendsto (fun ε => ∫ᶜ z in realGapEllipsePath c d ε, holomorphicOneForm f z)
      (𝓝[>] 0) (𝓝 (∫ x in (c - d)..(c + d), upper x - lower x)) := by
  have hl := tendsto_realGapEllipse_intervalIntegral f
    (fun θ => lower (c + d * Real.cos θ)) c d 0 Real.pi ε₀ M hd Real.pi_pos.le hε₀ hM
    hcont (fun ε hε θ hθ => hbound ε hε θ ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩)
    (fun θ hθ => (hlower _ (realGapEllipse_limit_mem_Icc c d θ hd)).comp
      (tendsto_realGapEllipse_lower c d θ hθ))
  have hu := tendsto_realGapEllipse_intervalIntegral f
    (fun θ => upper (c + d * Real.cos θ)) c d Real.pi (2 * Real.pi) ε₀ M hd
    (by linarith [Real.pi_pos]) hε₀ hM
    hcont (fun ε hε θ hθ => hbound ε hε θ ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
    (fun θ hθ => (hupper _ (realGapEllipse_limit_mem_Icc c d θ hd)).comp
      (tendsto_realGapEllipse_upper c d θ hθ))
  rw [integral_real_cosine_pullback lower c d 0 Real.pi hd hlcont] at hl
  rw [integral_real_cosine_pullback upper c d Real.pi (2 * Real.pi) hd hucont] at hu
  simp only [Real.cos_zero, Real.cos_pi, Real.cos_two_pi, mul_one, mul_neg_one] at hl hu
  have hsum := hl.add hu
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Ioo 0 ε₀ := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (eventually_lt_nhds hε₀)] with ε hε hε₀'
    exact ⟨hε, hε₀'⟩
  have heq : (fun ε =>
      (∫ θ in (0 : ℝ)..Real.pi,
        deriv (realGapEllipse c d ε) θ * f (realGapEllipse c d ε θ)) +
      (∫ θ in Real.pi..(2 * Real.pi),
        deriv (realGapEllipse c d ε) θ * f (realGapEllipse c d ε θ))) =ᶠ[𝓝[>] 0]
      (fun ε => ∫ᶜ z in realGapEllipsePath c d ε, holomorphicOneForm f z) := by
    filter_upwards [hsmall] with ε hε
    have hderiv : Continuous (fun θ => deriv (realGapEllipse c d ε) θ) := by
      simp_rw [(hasDerivAt_realGapEllipse c d ε _).deriv]
      fun_prop
    rw [curveIntegral_realGapEllipse_eq_intervalIntegral]
    exact intervalIntegral.integral_add_adjacent_intervals
      ((hderiv.mul (hcont ε hε)).intervalIntegrable _ _)
      ((hderiv.mul (hcont ε hε)).intervalIntegrable _ _)
  have hval : (∫ x in (c + d)..(c + -d), lower x) +
      (∫ x in (c + -d)..(c + d), upper x) =
        ∫ x in (c - d)..(c + d), upper x - lower x := by
    have hcd : c - d ≤ c + d := by linarith
    rw [show c + -d = c - d by ring, intervalIntegral.integral_symm,
      intervalIntegral.integral_sub
        (hucont.intervalIntegrable_of_Icc hcd)
        (hlcont.intervalIntegrable_of_Icc hcd)]
    abel
  exact hval ▸ hsum.congr' heq

end NLS.ComplexAnalysis
