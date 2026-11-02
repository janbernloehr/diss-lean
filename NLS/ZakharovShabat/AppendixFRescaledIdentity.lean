import NLS.ZakharovShabat.AppendixFRootPath
import NLS.ZakharovShabat.AppendixFMidpointIdentity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Exact rescaling of Appendix F midpoint integrals

The substitution retains the full displacement coefficient. The only
point omitted from the pointwise identity is the measure-zero initial
endpoint; no nonvanishing assumption on the square root is needed.
-/

noncomputable section
open Set Complex MeasureTheory
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The normalized-root quotient has the literal principal-root rescaling. -/
theorem appendixF_spoke_quotient_eq_rescaled (τ γ a z : ℂ) (hz : z ≠ 0)
    (t : ℝ) (ht : 0 < t) :
    (a-(τ+(t:ℂ)*z))/normalizedStandardRoot τ (γ^2) (τ+(t:ℂ)*z) =
      ((t:ℂ)+(τ-a)/z)/Complex.sqrt ((t:ℂ)^2-(γ/(2*z))^2) := by
  rw [appendixF_normalized_root_on_spoke τ γ z hz t ht]
  have hnum : a-(τ+(t:ℂ)*z) = -z*((t:ℂ)+(τ-a)/z) := by
    field_simp
    ring
  rw [hnum, mul_div_mul_left _ _ (neg_ne_zero.mpr hz)]

/-- Rescaling the full interval integral preserves its differential coefficient. -/
theorem appendixF_spoke_integral_eq_rescaled (τ γ a z : ℂ) (hz : z ≠ 0)
    (χ : ℝ → ℂ) :
    (∫ t in (0:ℝ)..1, -Complex.I*z*((a-(τ+(t:ℂ)*z))/
      normalizedStandardRoot τ (γ^2) (τ+(t:ℂ)*z))*χ t) =
      -Complex.I*z*∫ t in (0:ℝ)..1,
        (((t:ℂ)+(τ-a)/z)/Complex.sqrt ((t:ℂ)^2-(γ/(2*z))^2))*χ t := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [] with t ht
  have ht' : t ∈ Ioc (0:ℝ) 1 := by
    simpa only [uIoc_of_le zero_le_one] using ht
  rw [appendixF_spoke_quotient_eq_rescaled τ γ a z hz t ht'.1]
  ring

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

/-- The actual source integral equals its literal rescaled principal-root expression. -/
theorem appendixF_source_spoke_integral_eq_rescaled (ψ : CoeffPair p) (n : ℤ)
    (ν : ℂ) (hz : ν-sourceStandardRootMidpoint hp hp1 ψ n ≠ 0) :
    let τ := sourceStandardRootMidpoint hp hp1 ψ n
    let γ := canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
    let a := canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
    (∫ t in (0:ℝ)..1, -Complex.I*(ν-τ)*
      ((a-(τ+(t:ℂ)*(ν-τ)))/sourceStandardRoot hp hp1 ψ n (τ+(t:ℂ)*(ν-τ)))*
        sourceActionChi hp hp1 n ψ (τ+(t:ℂ)*(ν-τ))) =
      -Complex.I*(ν-τ)*∫ t in (0:ℝ)..1,
        (((t:ℂ)+(τ-a)/(ν-τ))/Complex.sqrt ((t:ℂ)^2-(γ/(2*(ν-τ)))^2))*
          sourceActionChi hp hp1 n ψ (τ+(t:ℂ)*(ν-τ)) := by
  dsimp only
  exact appendixF_spoke_integral_eq_rescaled _ _ _ _ hz _

/-- Corrected F.3 with the literal rescaled integral and its exact short-piece term. -/
theorem SourceFullAbelianUniformCauchyFamily.appendixF_rescaled_endpoint_identity
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (ψ : CoeffPair p) (hψ : ψ ∈ Metric.ball C.discs.source.val C.discs.sourceRadius) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0)
    (ν : ℂ) (hν : ν ∈ sourceCanonicalRootDomain hp hp1 ψ)
    (upper : Bool) (hside : ν ∈ sourceAbelianGapSide hp hp1 ψ n upper)
    (hpath : ∀ t ∈ Ioc (0:ℝ) 1,
      sourceStandardRootMidpoint hp hp1 ψ n+(t:ℂ)*(ν-sourceStandardRootMidpoint hp hp1 ψ n) ∈
        sourceCanonicalRootDomain hp hp1 ψ)
    (hint : IntervalIntegrable (fun t : ℝ =>
      -Complex.I*(ν-sourceStandardRootMidpoint hp hp1 ψ n)*
        ((canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-
          (sourceStandardRootMidpoint hp hp1 ψ n+(t:ℂ)*(ν-sourceStandardRootMidpoint hp hp1 ψ n)))/
            sourceStandardRoot hp hp1 ψ n
              (sourceStandardRootMidpoint hp hp1 ψ n+(t:ℂ)*(ν-sourceStandardRootMidpoint hp hp1 ψ n)))*
        sourceActionChi hp hp1 n ψ
          (sourceStandardRootMidpoint hp hp1 ψ n+(t:ℂ)*(ν-sourceStandardRootMidpoint hp hp1 ψ n))) volume 0 1) :
    let τ := sourceStandardRootMidpoint hp hp1 ψ n
    let γ := canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
    let a := canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
    sourceAbelianEndpointAverage hp hp1 n ν ψ = C.gapBoundary n ψ (Real.pi/2) upper+
      -Complex.I*(ν-τ)*∫ t in (0:ℝ)..1,
        (((t:ℂ)+(τ-a)/(ν-τ))/Complex.sqrt ((t:ℂ)^2-(γ/(2*(ν-τ)))^2))*
          sourceActionChi hp hp1 n ψ (τ+(t:ℂ)*(ν-τ)) := by
  have hz : ν-sourceStandardRootMidpoint hp hp1 ψ n ≠ 0 := by
    intro he
    apply hν n
    rw [sub_eq_zero.mp he]
    exact sourcePeriodicMidpoint_mem_segment hp hp1 ψ n
  dsimp only
  rw [C.appendixF_midpoint_integral_identity ψ hψ n hgap ν hν upper hside hpath hint,
    appendixF_source_spoke_integral_eq_rescaled ψ n ν hz]

end NLS.ZakharovShabat
