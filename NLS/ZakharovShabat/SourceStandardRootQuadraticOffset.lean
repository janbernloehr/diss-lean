import NLS.ZakharovShabat.SourceStandardRootZeroPeriodOffset

/-!
# Squared-gap midpoint offset from a vanishing contour

The centered regular factor is multiplied by the reciprocal-root
correction, which is quadratic in the gap. A positive midpoint factor
bound therefore controls the root offset by the squared gap times the
factor's variation on the circle. The estimate includes collapsed gaps
and applies to complex spectral endpoints.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A separated enclosing circle gives a direct quadratic-gap bound
for the midpoint offset times the regular factor's midpoint norm. -/
theorem norm_sourceStandardRoot_zero_period_offset_mul_le
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (m : ℤ)
    (c σ : ℂ) (R : ℝ) (hR : 0 < R)
    (hseg : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c R)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hzero : (∮ z in C(c,R), ((σ-z)/sourceStandardRoot hp hp1 ψ m z)*f z) = 0)
    (a S M : ℝ) (ha : 0 < a) (hS : 0 ≤ S) (hM : 0 ≤ M)
    (hsep : ∀ z ∈ sphere c R, a ≤ ‖sourceStandardRootMidpoint hp hp1 ψ m-z‖)
    (hgap : ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖ ≤ a)
    (hσ : ∀ z ∈ sphere c R, ‖σ-z‖ ≤ S)
    (hdev : ∀ z ∈ sphere c R, ‖f z-f (sourceStandardRootMidpoint hp hp1 ψ m)‖ ≤ M) :
    ‖σ-sourceStandardRootMidpoint hp hp1 ψ m‖*
      ‖f (sourceStandardRootMidpoint hp hp1 ψ m)‖ ≤
        R*S*M*(‖sourcePeriodicGapDisplacement hp hp1 ψ m‖^2/(2*a^3)) := by
  let τ := sourceStandardRootMidpoint hp hp1 ψ m
  let γ := sourcePeriodicGapDisplacement hp hp1 ψ m
  have hq : ‖γ^2‖ ≤ a^2 := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hgap 2
  have hroot z : sourceStandardRoot hp hp1 ψ m z = normalizedStandardRoot τ (γ^2) z := by
    simp only [sourceStandardRoot,τ,γ,sourcePeriodicGapDisplacement_apply]
  have hbound := norm_circleIntegral_weighted_root_inverse_correction_le
    τ (γ^2) c σ R a S M hR.le ha hS hM hsep hq hσ
      (fun z => f z-f τ) hdev
  simp_rw [← hroot] at hbound
  rw [norm_pow] at hbound
  have hidentity := sourceStandardRoot_zero_period_inverse_correction_identity
    hp hp1 ψ m c σ R hR hseg f hf hzero
  change (2*Real.pi*I : ℂ)*(σ-τ)*f τ =
    ∮ z in C(c,R), ((σ-z)*(f z-f τ))*
      ((sourceStandardRoot hp hp1 ψ m z)⁻¹-(τ-z)⁻¹) at hidentity
  rw [← hidentity,norm_mul,norm_mul] at hbound
  have hπnorm : ‖(2*Real.pi*I : ℂ)‖ = 2*Real.pi := by
    simp [Complex.norm_real,Real.pi_pos.le]
  rw [hπnorm] at hbound
  apply le_of_mul_le_mul_left (a := 2*Real.pi) ?_ (by positivity)
  convert hbound using 1 <;> (first | rfl | ring)

/-- A uniform positive lower bound at the midpoint turns the
vanishing-contour identity into a squared-gap root-offset estimate. -/
theorem norm_sourceStandardRoot_zero_period_offset_le
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (m : ℤ)
    (c σ : ℂ) (R : ℝ) (hR : 0 < R)
    (hseg : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c R)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hzero : (∮ z in C(c,R), ((σ-z)/sourceStandardRoot hp hp1 ψ m z)*f z) = 0)
    (a S M c₀ : ℝ) (ha : 0 < a) (hS : 0 ≤ S) (hM : 0 ≤ M) (hc₀ : 0 < c₀)
    (hsep : ∀ z ∈ sphere c R, a ≤ ‖sourceStandardRootMidpoint hp hp1 ψ m-z‖)
    (hgap : ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖ ≤ a)
    (hσ : ∀ z ∈ sphere c R, ‖σ-z‖ ≤ S)
    (hdev : ∀ z ∈ sphere c R, ‖f z-f (sourceStandardRootMidpoint hp hp1 ψ m)‖ ≤ M)
    (hlower : c₀ ≤ ‖f (sourceStandardRootMidpoint hp hp1 ψ m)‖) :
    ‖σ-sourceStandardRootMidpoint hp hp1 ψ m‖ ≤
      (R*S/(2*a^3*c₀))*M*‖sourcePeriodicGapDisplacement hp hp1 ψ m‖^2 := by
  have hbound := norm_sourceStandardRoot_zero_period_offset_mul_le
    hp hp1 ψ m c σ R hR hseg f hf hzero a S M ha hS hM hsep hgap hσ hdev
  have hsmall : ‖σ-sourceStandardRootMidpoint hp hp1 ψ m‖*c₀ ≤
      R*S*M*(‖sourcePeriodicGapDisplacement hp hp1 ψ m‖^2/(2*a^3)) :=
    (mul_le_mul_of_nonneg_left hlower (norm_nonneg _)).trans hbound
  have hdiv := (le_div_iff₀ hc₀).mpr hsmall
  convert hdiv using 1 <;> (first | rfl | ring)

end NLS.ZakharovShabat
