import NLS.ZakharovShabat.SourceNormalizedActionComplexSequenceContinuity
import NLS.SequenceSpaces.BoundedCoordinateDerivative

/-!
# Bounded derivative sequences for normalized actions

The local `ℓq` realization of the normalized-action deviation is
coordinatewise complex differentiable and uniformly bounded. Consequently,
the derivatives of all its coordinates in any source direction assemble
into an `ℓq` sequence. The assembly is a bounded complex-linear map.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Near a real-type source, all coordinate derivatives of the normalized-action
deviation assemble into a locally bounded `ℓq`-valued complex-linear operator. -/
theorem exists_local_sourceNormalizedActionDeviation_coordinateDerivative
    [Fact (1 ≤ q)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (hq1 : 1 < q) (hq : q ≠ ⊤)
    (hhalf : ENNReal.ofReal (p.toReal/2) ≤ q)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ F : CoeffPair p → Coeff q,
        (∀ ψ ∈ V, ∀ n : ℤ,
          F ψ n = sourceNormalizedActionDeviation hp hp1 ψ n) ∧
        ∃ M : ℝ, (∀ ψ ∈ V, ‖F ψ‖ ≤ M) ∧
          (∀ ψ ∈ V, ∃ R : ℝ, 0 < R ∧ ball ψ R ⊆ V ∧
            ∃ L : CoeffPair p →L[ℂ] Coeff q,
              (∀ h : CoeffPair p, ∀ n : ℤ,
                L h n = (fderiv ℂ (fun χ => F χ n) ψ) h) ∧
              ‖L‖ ≤ 2*M/R) := by
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
  refine ⟨V,hVopen,hφV,F,hFapply,M,hFbound,?_⟩
  intro ψ hψ
  obtain ⟨R,hR,hball,L,hL,hLbound⟩ :=
    Coeff.exists_derivative_clm_of_bounded_coordinatewise
      F hVopen hcoord M hFbound ψ hψ
  exact ⟨R,hR,hball,L,hL,hLbound⟩

end NLS.ZakharovShabat
