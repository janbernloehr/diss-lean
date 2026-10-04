import NLS.SequenceSpaces.NonnegativeActions

/-! # Holomorphic uniqueness from nonnegative actions

The nonnegative cone has empty interior in many sequence spaces. Instead
of assuming interior, lift through the open quadratic action map and use
holomorphic uniqueness on the real Birkhoff form.
-/
noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Agreement on nonnegative real actions near a nonnegative base gives
a full complex germ equality, including at zero actions. -/
theorem eventuallyEq_of_nonnegativeActions_agreement (hp : p ≠ ⊤)
    (f g : Coeff q → F) (U : Set (Coeff q)) (hU : IsOpen U)
    (c : Coeff q) (hc : c ∈ U) (hcpos : c ∈ nonnegativeLocus q)
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (he : ∀ b ∈ U, b ∈ nonnegativeLocus q → f b = g b) : f =ᶠ[𝓝 c] g := by
  let Q := quadraticActionsExponent (p := p) (q := q)
  have hQ : Differentiable ℂ Q := differentiableOn_univ.mp analyticOnNhd_quadraticActionsExponent.differentiableOn
  have hV : IsOpen (Q ⁻¹' U) := hU.preimage hQ.continuous
  obtain ⟨z,hzr,hzc,_⟩ := exists_real_quadraticActions_lift (p := p) hp c hcpos
  change Q z = c at hzc
  have hz : z ∈ Q ⁻¹' U := by change Q z ∈ U; simpa only [hzc] using hc
  have hfg := eventuallyEq_of_realPair_agreement (f ∘ Q) (g ∘ Q) (Q ⁻¹' U) hV z hz hzr
    (hf.comp hQ.differentiableOn (fun _ hz => hz))
    (hg.comp hQ.differentiableOn (fun _ hz => hz))
    (fun w hw hwr => he (Q w) hw (quadraticActions_mem_nonnegativeLocus w hwr))
  obtain ⟨V,hVsub,hVopen,hzV⟩ := _root_.mem_nhds_iff.mp hfg
  have hopen := isOpenMap_quadraticActionsExponent (p := p) (q := q) hp V hVopen
  have hcV : c ∈ Q '' V := ⟨z,hzV,hzc⟩
  filter_upwards [hopen.mem_nhds hcV] with b hb
  obtain ⟨w,hw,rfl⟩ := hb
  exact hVsub hw

/-- On an open convex action domain, agreement on its nonnegative part
determines the map everywhere whenever that part is nonempty. -/
theorem eqOn_of_nonnegativeActions_agreement (hp : p ≠ ⊤)
    (f g : Coeff q → F) (U : Set (Coeff q)) (hU : IsOpen U) (hconv : Convex ℝ U)
    (c : Coeff q) (hc : c ∈ U) (hcpos : c ∈ nonnegativeLocus q)
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (he : ∀ b ∈ U, b ∈ nonnegativeLocus q → f b = g b) : EqOn f g U :=
  ComplexAnalysis.DifferentiableOn.eqOn_of_convex_of_eventuallyEq f g U hU hconv hf hg c hc
    (eventuallyEq_of_nonnegativeActions_agreement hp f g U hU c hc hcpos hf hg he)

end NLS.Coeff
