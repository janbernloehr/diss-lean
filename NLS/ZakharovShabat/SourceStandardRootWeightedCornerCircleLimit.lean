import NLS.ZakharovShabat.SourceStandardRootWeightedStadiumLimit
import NLS.ZakharovShabat.SourceStandardRootWeightedStadium

/-!
# Weighted standard-root corner-circle limit

The small corner circle has the opposite orientation to the gap
stadium. Combining their exact contour identity with the shrinking
stadium limit identifies the limiting weighted circle integral.
-/

noncomputable section
open Set Filter Topology Complex
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The weighted circle integral on corner circles shrinking onto a
real open gap tends to minus twice the upper gap-side integral. -/
theorem sourceStandardRoot_weighted_cornerCircleIntegral_tendsto_boundary
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
    (hglocal : AnalyticOnNhd ℂ g U)
    (hgdomain : ∀ z ∈ sourceCanonicalRootDomain hp hp1 ψ,
      AnalyticAt ℂ g z) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
    let d : ℝ := (r.re-l.re)/2
    Tendsto (fun ρ : ℝ =>
      ∮ z in C(c, stadiumCornerRadius d ρ),
        g z / sourceStandardRoot hp hp1 ψ n z)
      (𝓝[Set.Ioi 0] (0:ℝ))
      (𝓝 (-(2 * gapSideBoundaryIntegral
        (sourceStandardRootMidpoint hp hp1 ψ n)
        (sourceStandardRootHalfGap hp hp1 ψ n) g 1 true))) := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
  let d : ℝ := (r.re-l.re)/2
  obtain ⟨ε,hε,heq⟩ :=
    exists_sourceStandardRoot_weighted_cornerCircleIntegral_eq_neg_stadium
      hp hp1 ψ hreal n hopen g hgdomain
  have hstad := sourceStandardRoot_weighted_stadium_curveIntegral_tendsto_two_upper
    hp hp1 ψ hreal n hopen g U hUopen hgapU hglocal
      (fun z hz => (hgdomain z hz).continuousAt)
  have hneg := hstad.neg
  have hsmall0 : ∀ᶠ ρ in 𝓝 (0:ℝ), ρ < ε := Iio_mem_nhds hε
  have hsmall : ∀ᶠ ρ in 𝓝[Set.Ioi 0] (0:ℝ), ρ < ε :=
    hsmall0.filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ ρ in 𝓝[Set.Ioi 0] (0:ℝ), 0 < ρ :=
    self_mem_nhdsWithin
  have hevent : (fun ρ : ℝ =>
      ∮ z in C(c, stadiumCornerRadius d ρ),
        g z / sourceStandardRoot hp hp1 ψ n z)
      =ᶠ[𝓝[Set.Ioi 0] (0:ℝ)]
      (fun ρ : ℝ =>
        -(∫ᶜ z in sourceGapStadiumPath l r ρ,
          holomorphicOneForm
            (fun z => g z / sourceStandardRoot hp hp1 ψ n z) z)) := by
    filter_upwards [hpos,hsmall] with ρ hρ hρε
    exact heq ρ ⟨hρ,hρε.le⟩
  exact hneg.congr' hevent.symm

end NLS.ZakharovShabat
