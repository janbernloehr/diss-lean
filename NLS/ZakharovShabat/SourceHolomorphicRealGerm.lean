import NLS.ZakharovShabat.SourceHolomorphicRealCenteredBalls

/-! # Equality of analytic source germs from real agreement -/

noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Banach-valued analytic source maps agreeing on the real locus
have the same complex germ at each real source where both are analytic. -/
theorem eventuallyEq_source_of_analyticAt_of_real_agreement
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (hp : p ≠ ⊤) (φ : realTypeSourceLocus p) (f g : CoeffPair p → F)
    (hf : AnalyticAt ℂ f φ.val) (hg : AnalyticAt ℂ g φ.val)
    (hreal : ∀ χ : realTypeSourceLocus p, f χ.val = g χ.val) :
    f =ᶠ[𝓝 φ.val] g := by
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp
    (hf.eventually_analyticAt.and hg.eventually_analyticAt)
  have heq := eqOn_sourceRealCenteredBalls_of_real_agreement hp φ φ r r f g
    (fun ψ hψ => (hball hψ).1.differentiableAt.differentiableWithinAt)
    (fun ψ hψ => (hball hψ).2.differentiableAt.differentiableWithinAt)
    (fun χ _ => hreal χ)
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with ψ hψ
  exact heq ⟨hψ,hψ⟩

end NLS.ZakharovShabat
