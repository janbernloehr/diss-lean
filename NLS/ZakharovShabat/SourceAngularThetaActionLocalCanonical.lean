import NLS.ZakharovShabat.SourceAngularThetaActionCanonical
import NLS.ZakharovShabat.SourceComplexActionAnalytic
import NLS.ZakharovShabat.SourceHolomorphicRealCenteredBalls

/-! # Canonical theta/action identities as complex germs

The actual canonical value on every nearby real source determines the
analytic bracket on a complex neighborhood of each real open-gap source.
This local complex identity permits differentiating the canonical relation.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceAngularThetaCommonDomainData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (j : ℤ) → CoeffPair p → DeletedCoeff p j}

/-- The proved real canonical theta/action value holds on a complex
neighborhood of every real source with an open selected angle gap. -/
theorem eventually_thetaAction_eq_kronecker
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (n k : ℤ) (φ : realTypeSourceLocus p)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0) :
    sourceAngularThetaFunctionalBracket hp hp1 h2p n s (sourceComplexAction hp hp1 k) =ᶠ[𝓝 φ.val]
      (fun _ => if n = k then 1 else 0) := by
  let F := sourceAngularThetaFunctionalBracket hp hp1 h2p n s (sourceComplexAction hp hp1 k)
  have hφW : φ.val ∈ W := D.real_subset φ.property
  have hθ := D.analyticOnNhd_thetaDifferential n φ.val ⟨hφW,hgap⟩
  have hI := analyticAt_sourceComplexAction_of_realType hp hp1 k φ.val φ.property
  have hF : AnalyticAt ℂ F φ.val :=
    ((sourceBivector h2p).analyticAt_bilinear _).comp₂ hθ hI.fderiv
  have hnear := hF.eventually_analyticAt.and ((D.open_gap n).mem_nhds ⟨hφW,hgap⟩)
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hnear
  have hdiff : DifferentiableOn ℂ F (ball φ.val r) :=
    fun ψ hψ => (hball hψ).1.differentiableAt.differentiableWithinAt
  have heq := eqOn_sourceRealCenteredBalls_of_real_agreement hp φ φ r r
    F (fun _ => if n = k then (1 : ℂ) else 0) hdiff (differentiableOn_const _)
    (fun χ hχ => D.thetaAction_eq_kronecker h2p n k χ (hball hχ.1).2.2)
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with ψ hψ
  exact heq ⟨hψ,hψ⟩

/-- Differentiating the actual local canonical relation gives the zero
cotangent, for every action index including collapsed action gaps. -/
theorem fderiv_thetaAction_eq_zero
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (n k : ℤ) (φ : realTypeSourceLocus p)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0) :
    fderiv ℂ (sourceAngularThetaFunctionalBracket hp hp1 h2p n s (sourceComplexAction hp hp1 k)) φ.val = 0 := by
  rw [(D.eventually_thetaAction_eq_kronecker h2p n k φ hgap).fderiv_eq]
  exact (hasFDerivAt_const (if n = k then (1 : ℂ) else 0) φ.val).fderiv

end SourceAngularThetaCommonDomainData
end NLS.ZakharovShabat
