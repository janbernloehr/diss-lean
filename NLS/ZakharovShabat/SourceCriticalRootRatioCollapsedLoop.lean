import NLS.ZakharovShabat.SourceCriticalRootRatioCollapsedContour
import NLS.ZakharovShabat.SourceCriticalRootRatioStadiumIntegral
import NLS.ComplexAnalysis.ConvexHolomorphicPrimitive

/-!
# Smooth loops around a collapsed gap

The quotient extends across a collapsed gap. Its integral therefore
vanishes on every `C¹` loop in a filled disc avoiding the other gaps,
even when the loop winds around the collapsed point. The original
quotient only needs to be defined along the loop itself.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every smooth loop in an isolating disc has zero integral when the
selected periodic gap is collapsed. The loop need not be circular or
twice differentiable. -/
theorem exists_global_sourceCriticalRootRatio_loopIntegral_zero_of_zeroGap
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧
      realTypeSourceLocus p ⊆ W ∧
      ∀ ψ ∈ W, ∀ n : ℤ,
        sourcePeriodicGapDisplacement hp hp1 ψ n = 0 →
          ∀ c : ℂ, ∀ r : ℝ, 0 < r →
            closedBall c r ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n →
              ∀ {a : ℂ} (γ : Path a a),
                ContDiffOn ℝ 1 γ.extend (Icc (0:ℝ) 1) →
                  range γ ⊆ ball c r →
                    range γ ⊆ sourceCanonicalRootDomain hp hp1 ψ →
                      (∫ᶜ z in γ, NLS.ComplexAnalysis.holomorphicOneForm
                        (fun z => deriv (canonicalDiscriminant hp
                          (periodOnePotential ψ)) z /
                          sourceCanonicalRoot hp hp1 ψ z) z) = 0 := by
  obtain ⟨W,hWopen,hreal,hdata⟩ :=
    exists_global_sourceCriticalRootRatio_analytic_of_zeroGap hp hp1
  refine ⟨W,hWopen,hreal,?_⟩
  intro ψ hψ n hgap c r hr hfilled a γ hsmooth hball hroot
  let f : ℂ → ℂ := sourceCriticalRootRatioExtension hp hp1 n ψ
  let q : ℂ → ℂ := fun z =>
    deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
      sourceCanonicalRoot hp hp1 ψ z
  have hanalytic := (hdata ψ hψ n hgap).1
  have heq := (hdata ψ hψ n hgap).2
  have hdiff : DifferentiableOn ℂ f (ball c r) := by
    intro z hz
    exact (hanalytic z (hfilled (ball_subset_closedBall hz))).differentiableAt.differentiableWithinAt
  have hpath : ∀ t ∈ Icc (0:ℝ) 1, γ.extend t ∈ ball c r := by
    intro t ht
    rw [γ.extend_apply ht]
    exact hball ⟨⟨t,ht⟩,rfl⟩
  have hω : ContinuousOn (NLS.ComplexAnalysis.holomorphicOneForm f)
      (range γ) := by
    intro z hz
    have hz' : z ∈ sourceStandardRootOmittedDomain hp hp1 ψ n :=
      hfilled (ball_subset_closedBall (hball hz))
    exact (((hanalytic z hz').continuousAt).smul continuousAt_const).continuousWithinAt
  have hint : CurveIntegrable (NLS.ComplexAnalysis.holomorphicOneForm f) γ :=
    hω.curveIntegrable_of_contDiffOn hsmooth (fun t => ⟨t,rfl⟩)
  have hzero : (∫ᶜ z in γ, NLS.ComplexAnalysis.holomorphicOneForm f z) = 0 :=
    NLS.ComplexAnalysis.curveIntegral_eq_zero_of_convex_loop_one
      f (ball c r) (convex_ball c r) isOpen_ball hdiff γ hsmooth hpath hint
  have hintegral :
      (∫ᶜ z in γ, NLS.ComplexAnalysis.holomorphicOneForm q z) =
        ∫ᶜ z in γ, NLS.ComplexAnalysis.holomorphicOneForm f z := by
    rw [curveIntegral_eq_intervalIntegral_deriv,
      curveIntegral_eq_intervalIntegral_deriv]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (0:ℝ) 1 := by
      simpa only [uIcc_of_le zero_le_one] using ht
    have hzt : γ.extend t ∈ sourceCanonicalRootDomain hp hp1 ψ := by
      rw [γ.extend_apply ht']
      exact hroot ⟨⟨t,ht'⟩,rfl⟩
    simp only [NLS.ComplexAnalysis.holomorphicOneForm_apply]
    rw [show f (γ.extend t) = q (γ.extend t) from heq _ hzt]
  exact hintegral.trans hzero

end NLS.ZakharovShabat
