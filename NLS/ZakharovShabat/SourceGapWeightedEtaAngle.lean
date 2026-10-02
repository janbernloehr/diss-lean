import NLS.ZakharovShabat.SourceGapWeightedEta

/-! # Identification with Section 15's gap-weighted exponentials

On an open gap, the new analytic coordinates equal twice the chosen
half-gap times `exp(±i eta)`. With the canonical half-gap this is exactly
`gamma * exp(±i eta)`. No assertion about a single-valued eta at closed
gaps is needed for the continuation.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem gapWeightedEta_formula (a b δ ε H σ : ℂ)
    (hc : a = δ*Complex.cos ε) (hs : b = δ*Complex.sin ε) (hσ : σ = 1 ∨ σ = -1) :
    -2*(a+σ*I*b)*Complex.exp (σ*I*H) =
      2*δ*Complex.exp (σ*I*(ε-(Real.pi : ℂ)+H)) := by
  rw [hc,hs]
  rcases hσ with rfl | rfl
  · have he : 1*I*(ε-(Real.pi : ℂ)+H) = ε*I-(Real.pi : ℂ)*I+I*H := by ring
    rw [he, Complex.exp_add, Complex.exp_sub, Complex.exp_pi_mul_I, Complex.exp_mul_I]
    simp only [one_mul, div_neg, div_one]
    ring
  · have he : -1*I*(ε-(Real.pi : ℂ)+H) = (-ε)*I+(Real.pi : ℂ)*I+-(I*H) := by ring
    rw [he, Complex.exp_add, Complex.exp_add, Complex.exp_pi_mul_I, Complex.exp_mul_I,
      Complex.cos_neg, Complex.sin_neg]
    simp only [neg_mul]
    ring

namespace SourceAngularEtaAnalyticChartData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {n : ℤ}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
  {W V U : Set (CoeffPair p)} {c : ℤ → ℂ} {T : ℤ → ℝ}
  {r R : ℝ} {z₀ : ℂ} {ρ : ℝ} {δ ε : CoeffPair p → ℂ}

theorem gapWeightedEtaCoordinate_eq_halfGap_exp
    (D : SourceAngularEtaAnalyticChartData hp hp1 n s W V U c T r R z₀ ρ δ ε)
    (ψ : CoeffPair p) (hψ : ψ ∈ U) (σ : ℂ) (hσ : σ = 1 ∨ σ = -1) :
    sourceGapWeightedEtaCoordinate hp hp1 n s σ ψ =
      2*δ ψ*Complex.exp (σ*I*sourceAngularEtaCauchyRepresentative hp hp1 n s (c n) r R z₀ ρ ε ψ) := by
  let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n
  let τ := canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let P := sourceStandardRootOmittedProduct hp hp1 n ψ μ
  have hc : μ-τ = δ ψ*Complex.cos (ε ψ) := by
    have h := (D.angle.terminal_coordinates ψ hψ).1
    change τ+δ ψ*Complex.cos (ε ψ) = μ at h
    linear_combination -h
  have hP : P ≠ 0 := sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ μ n
    (((D.annulus.disc_family ψ (D.angle.source_subset hψ)).contour_family.2 n).2.2.1
      (Metric.ball_subset_closedBall ((D.annulus.disc_family ψ (D.angle.source_subset hψ)).dirichlet_mem_ball n)))
  have hδ := D.angle.halfGap_ne_zero ψ hψ
  have hs : sourceDirichletEtaSineNumerator hp hp1 n ψ = δ ψ*Complex.sin (ε ψ) := by
    rw [(D.angle.terminal_coordinates ψ hψ).2]
    change sourceAntiDiscriminantCandidate hp hp1 ψ μ/(2*P) =
      δ ψ*(sourceAntiDiscriminantCandidate hp hp1 ψ μ/(2*δ ψ*P))
    field_simp
  unfold sourceGapWeightedEtaCoordinate sourceAngularEtaCauchyRepresentative
  rw [D.annulus.etaRemainder_eq_cauchyCandidate ρ D.inner_lt_cauchy D.cauchy_lt_outer
    ψ (D.angle.source_subset hψ)]
  exact gapWeightedEta_formula (μ-τ) _ (δ ψ) (ε ψ) _ σ hc hs hσ

/-- With the canonical half-gap, the analytic continuation has exactly
the dissertation's original `gamma * exp(±i eta)` value. -/
theorem gapWeightedEtaCoordinate_eq_gap_exp
    (D : SourceAngularEtaAnalyticChartData hp hp1 n s W V U c T r R z₀ ρ δ ε)
    (ψ : CoeffPair p) (hψ : ψ ∈ U) (σ : ℂ) (hσ : σ = 1 ∨ σ = -1)
    (hδ : δ ψ = canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n/2) :
    sourceGapWeightedEtaCoordinate hp hp1 n s σ ψ =
      canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n *
        Complex.exp (σ*I*sourceAngularEtaCauchyRepresentative hp hp1 n s (c n) r R z₀ ρ ε ψ) := by
  rw [D.gapWeightedEtaCoordinate_eq_halfGap_exp ψ hψ σ hσ, hδ]
  ring

end SourceAngularEtaAnalyticChartData
end NLS.ZakharovShabat
