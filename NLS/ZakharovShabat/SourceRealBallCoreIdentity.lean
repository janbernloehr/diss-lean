import NLS.ZakharovShabat.SourceRealBallCore

/-! # Analytic identities on real-centered complex source domains -/
noncomputable section
set_option autoImplicit false
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Real agreement propagates to the entire real-centered ball core, including every component. -/
theorem eqOn_sourceRealBallCore_of_real_agreement (hp : p ≠ ⊤)
    {U : Set (CoeffPair p)} (hrealU : realTypeSourceLocus p ⊆ U)
    (f g : CoeffPair p → F) (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (hr : ∀ φ : realTypeSourceLocus p, f φ.val = g φ.val) :
    EqOn f g (sourceRealBallCore U) := by
  intro ψ hψ
  obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ
  obtain ⟨r,hr'⟩ := mem_iUnion.mp hφ
  obtain ⟨hball,hψr⟩ := mem_iUnion.mp hr'
  have hφr : φ.val ∈ ball φ.val r :=
    mem_ball_self ((dist_nonneg : 0 ≤ dist ψ φ.val).trans_lt hψr)
  have hφU := hrealU φ.property
  have he := eventuallyEq_source_of_analyticAt_of_real_agreement hp φ f g
    (hf _ hφU) (hg _ hφU) hr
  exact (hf.mono hball).eqOn_of_preconnected_of_eventuallyEq (hg.mono hball)
    (convex_ball φ.val r).isPreconnected hφr he hψr
end NLS.ZakharovShabat
