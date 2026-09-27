import NLS.ZakharovShabat.SourceStandardRootGapSideMeanValue
import NLS.ZakharovShabat.SourceStandardRootWeightedLocalContourHomotopy

/-!
# Real mean values for local weighted gap contours

This is the real-valued conclusion of Lemma 12.3 for the selected
standard root. The numerator only needs to be analytic on a local
neighborhood containing the gap and the filled outer midpoint disc.
-/

noncomputable section
open Set Metric Complex
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The exact gap-side value yields a real mean value for any contour
whose integral has been identified with that boundary value. -/
theorem normalized_real_mean_value_of_boundary
    (τ δ : ℂ) (g : ℂ → ℂ) (J : ℂ)
    (hδ : δ ≠ 0)
    (hgcont : ContinuousOn g (standardRootGapSegment τ δ))
    (hgreal : ∀ z ∈ standardRootGapSegment τ δ, (g z).im = 0)
    (hJ : J = -(2 * gapSideBoundaryIntegral τ δ g 1 true)) :
    ∃ μ ∈ standardRootGapSegment τ δ,
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * J = -g μ := by
  obtain ⟨μ,hμ,hB⟩ :=
    gapSideBoundaryIntegral_eq_I_pi_mul_value_of_real
      τ δ g hδ hgcont hgreal
  let K : ℂ := 2 * (Real.pi : ℂ) * Complex.I
  have hK : K ≠ 0 := by
    dsimp [K]
    exact mul_ne_zero (mul_ne_zero (by norm_num)
      (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  refine ⟨μ,hμ,?_⟩
  change K⁻¹ * J = -g μ
  calc
    K⁻¹ * J = K⁻¹ * (-(K * g μ)) := by
      rw [hJ,hB]
      dsimp [K]
      ring
    _ = -g μ := by
      rw [mul_neg, ← mul_assoc, inv_mul_cancel₀ hK, one_mul]

/-- The normalized weighted midpoint-circle integral is the negative
of one value attained by a real-valued analytic numerator on the gap. -/
theorem weighted_sourceStandardRoot_midpointCircle_real_mean_value_of_local_disc
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (g : ℂ → ℂ) (U : Set ℂ) (hUopen : IsOpen U)
    (hgapU : standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ n)
      (sourceStandardRootHalfGap hp hp1 ψ n) ⊆ U)
    (hg : AnalyticOnNhd ℂ g U)
    (hgreal : ∀ z ∈ standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ n)
      (sourceStandardRootHalfGap hp hp1 ψ n), (g z).im = 0)
    (R : ℝ) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
    let d : ℝ := (r.re-l.re)/2
    d < R → closedBall c R ⊆ U →
      ∃ μ ∈ standardRootGapSegment
        (sourceStandardRootMidpoint hp hp1 ψ n)
        (sourceStandardRootHalfGap hp hp1 ψ n),
        (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
          (∮ z in C(c,R), g z / sourceStandardRoot hp hp1 ψ n z) = -g μ := by
  let τ := sourceStandardRootMidpoint hp hp1 ψ n
  let δ := sourceStandardRootHalfGap hp hp1 ψ n
  have hδ : δ ≠ 0 :=
    sourceStandardRootHalfGap_ne_zero_of_openRealGap hp hp1 ψ hreal n hopen
  have hgcont : ContinuousOn g (standardRootGapSegment τ δ) := by
    intro z hz
    exact ((hg z (hgapU hz)).continuousAt).continuousWithinAt
  dsimp only
  intro hR hUdisc
  apply normalized_real_mean_value_of_boundary τ δ g _ hδ hgcont hgreal
  exact weighted_sourceStandardRoot_midpointCircle_eq_boundary_of_local_disc
    hp hp1 ψ hreal n hopen g U hUopen hgapU hg R hR hUdisc

/-- The same real mean-value formula holds for an enclosing circle
with arbitrary center inside the local analytic midpoint disc. -/
theorem weighted_sourceStandardRoot_circle_real_mean_value_of_local_nested_midpoint
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (g : ℂ → ℂ) (U : Set ℂ) (hUopen : IsOpen U)
    (hgapU : standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ n)
      (sourceStandardRootHalfGap hp hp1 ψ n) ⊆ U)
    (hg : AnalyticOnNhd ℂ g U)
    (hgreal : ∀ z ∈ standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ n)
      (sourceStandardRootHalfGap hp hp1 ψ n), (g z).im = 0)
    (c₀ : ℂ) (r₀ R : ℝ) (hr₀ : 0 < r₀)
    (hseg₀ : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c₀ r₀) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
    let d : ℝ := (r.re-l.re)/2
    d < R → closedBall c R ⊆ U →
      closedBall c₀ r₀ ⊆ closedBall c R →
      ∃ μ ∈ standardRootGapSegment
        (sourceStandardRootMidpoint hp hp1 ψ n)
        (sourceStandardRootHalfGap hp hp1 ψ n),
        (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
          (∮ z in C(c₀,r₀), g z / sourceStandardRoot hp hp1 ψ n z) = -g μ := by
  let τ := sourceStandardRootMidpoint hp hp1 ψ n
  let δ := sourceStandardRootHalfGap hp hp1 ψ n
  have hδ : δ ≠ 0 :=
    sourceStandardRootHalfGap_ne_zero_of_openRealGap hp hp1 ψ hreal n hopen
  have hgcont : ContinuousOn g (standardRootGapSegment τ δ) := by
    intro z hz
    exact ((hg z (hgapU hz)).continuousAt).continuousWithinAt
  dsimp only
  intro hR hUdisc hnest
  apply normalized_real_mean_value_of_boundary τ δ g _ hδ hgcont hgreal
  exact weighted_sourceStandardRoot_circle_eq_boundary_of_local_nested_midpoint
    hp hp1 ψ hreal n hopen g U hUopen hgapU hg
      c₀ r₀ R hr₀ hseg₀ hR hUdisc hnest

end NLS.ZakharovShabat
