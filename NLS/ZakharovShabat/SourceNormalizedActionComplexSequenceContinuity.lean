import NLS.ZakharovShabat.SourceNormalizedActionComplexAllCoordinates
import NLS.SequenceSpaces.BoundedCoordinateHolomorphic

/-!
# Norm continuity of the normalized-action sequence

The locally bounded `ℓq` realization of the normalized-action
deviation has differentiable scalar coordinates. The Schwarz estimate
for finite Fourier truncations upgrades this to norm continuity of
the full sequence-valued map.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Near every real-type potential, the complex normalized-action
deviation is a norm-continuous `ℓq`-valued map. -/
theorem exists_local_sourceNormalizedActionDeviation_continuousMap
    [Fact (1 ≤ q)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (hq1 : 1 < q) (hq : q ≠ ⊤)
    (hhalf : ENNReal.ofReal (p.toReal/2) ≤ q)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ F : CoeffPair p → Coeff q,
        (∀ ψ ∈ V, ∀ n : ℤ,
          F ψ n = sourceNormalizedActionDeviation hp hp1 ψ n) ∧
        ContinuousOn F V := by
  classical
  obtain ⟨V,hVopen,hφV,M,hdiff,hbound⟩ :=
    exists_local_sourceNormalizedActionComplexExtension_allCoordinates_boundedCoeff
      hp hp1 hq1 hq hhalf φ hreal
  let F : CoeffPair p → Coeff q := fun ψ =>
    if hψ : ψ ∈ V then Classical.choose (hbound ψ hψ) else 0
  have hFapply (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ) :
      F ψ n = sourceNormalizedActionDeviation hp hp1 ψ n := by
    simp only [F,dif_pos hψ]
    exact (Classical.choose_spec (hbound ψ hψ)).1 n
  have hFbound (ψ : CoeffPair p) (hψ : ψ ∈ V) : ‖F ψ‖ ≤ M := by
    simp only [F,dif_pos hψ]
    exact (Classical.choose_spec (hbound ψ hψ)).2
  have hcoord (n : ℤ) : DifferentiableOn ℂ (fun ψ => F ψ n) V := by
    intro ψ hψ
    have hdev : DifferentiableAt ℂ
        (fun χ : CoeffPair p => sourceNormalizedActionDeviation hp hp1 χ n) ψ := by
      change DifferentiableAt ℂ
        (fun χ : CoeffPair p =>
          4 * sourceNormalizedActionComplexExtension hp hp1 n χ - 1) ψ
      exact (((hdiff n ψ hψ).differentiableAt (hVopen.mem_nhds hψ)).const_mul 4).sub_const 1
    have heq : (fun χ : CoeffPair p => sourceNormalizedActionDeviation hp hp1 χ n)
        =ᶠ[𝓝 ψ] (fun χ : CoeffPair p => F χ n) := by
      filter_upwards [hVopen.mem_nhds hψ] with χ hχ
      exact (hFapply χ hχ n).symm
    exact (hdev.congr_of_eventuallyEq heq.symm).differentiableWithinAt
  refine ⟨V,hVopen,hφV,F,hFapply,?_⟩
  exact Coeff.continuousOn_of_bounded_coordinatewise hq F hVopen hcoord M hFbound

end NLS.ZakharovShabat
