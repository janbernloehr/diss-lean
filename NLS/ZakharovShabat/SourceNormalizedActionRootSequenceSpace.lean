import NLS.ZakharovShabat.SourceNormalizedActionComplexUniformPositive
import NLS.ZakharovShabat.SourceStandardRootProductFactors
import NLS.SequenceSpaces.BoundedCoordinateDifferentiable

/-!
# Sequence-space values of the normalized-action square root

The principal square root is globally one-sided Lipschitz at one.
The normalized-action deviation's locally uniform `ℓq` bound therefore
transfers to the root deviation. The common complex differentiability
domain for all root coordinates and the bounded-coordinate theorem
give Fréchet holomorphy of this `ℓq`-valued map.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The deviation of the principal normalized-action root from its
free value. -/
def sourceNormalizedActionRootDeviation
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) : ℂ :=
  sourceNormalizedActionRoot hp hp1 n ψ - 1

/-- Near every real-type source, the principal root deviation is a
Fréchet-holomorphic and locally bounded `ℓq`-valued map. -/
theorem exists_local_sourceNormalizedActionRootDeviation_continuousMap
    [Fact (1 ≤ q)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (hq1 : 1 < q) (hq : q ≠ ⊤)
    (hhalf : ENNReal.ofReal (p.toReal/2) ≤ q)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ M : ℝ, ∃ F : CoeffPair p → Coeff q,
        (∀ ψ ∈ V, ∀ n : ℤ,
          F ψ n = sourceNormalizedActionRootDeviation hp hp1 ψ n) ∧
        (∀ ψ ∈ V, ‖F ψ‖ ≤ M) ∧ ContinuousOn F V ∧
        DifferentiableOn ℂ F V := by
  classical
  obtain ⟨Vd,hVdopen,hφVd,M,_,hbound⟩ :=
    exists_local_sourceNormalizedActionComplexExtension_allCoordinates_boundedCoeff
      hp hp1 hq1 hq hhalf φ hreal
  obtain ⟨Vr,hVropen,hφVr,_,_,_,hrootdiff,_⟩ :=
    exists_local_sourceNormalizedActionRoot_allCoordinates
      hp hp1 hq1 hq hhalf φ hreal
  let V := Vd ∩ Vr
  have hVopen : IsOpen V := hVdopen.inter hVropen
  have hcoeff (ψ : CoeffPair p) (hψ : ψ ∈ V) :
      ∃ A : Coeff q,
        (∀ n : ℤ, A n = sourceNormalizedActionRootDeviation hp hp1 ψ n) ∧
        ‖A‖ ≤ M := by
    obtain ⟨B,hB,hBnorm⟩ := hbound ψ hψ.1
    have hpoint (n : ℤ) :
        ‖sourceNormalizedActionRootDeviation hp hp1 ψ n‖ ≤ ‖B n‖ := by
      have hs := norm_sqrt_sub_one_le
        (4 * sourceNormalizedActionComplexExtension hp hp1 n ψ)
      simpa only [sourceNormalizedActionRootDeviation,sourceNormalizedActionRoot,
        sourceNormalizedActionDeviation, hB n] using hs
    have hmem : Memℓp
        (sourceNormalizedActionRootDeviation hp hp1 ψ) q :=
      (lp.memℓp B).mono' hpoint
    let A : Coeff q := ⟨sourceNormalizedActionRootDeviation hp hp1 ψ,hmem⟩
    refine ⟨A,fun n => rfl,?_⟩
    exact (lp.norm_mono (zero_lt_one.trans hq1).ne' hpoint).trans hBnorm
  let F : CoeffPair p → Coeff q := fun ψ =>
    if hψ : ψ ∈ V then Classical.choose (hcoeff ψ hψ) else 0
  have hFapply (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ) :
      F ψ n = sourceNormalizedActionRootDeviation hp hp1 ψ n := by
    simp only [F,dif_pos hψ]
    exact (Classical.choose_spec (hcoeff ψ hψ)).1 n
  have hFbound (ψ : CoeffPair p) (hψ : ψ ∈ V) : ‖F ψ‖ ≤ M := by
    simp only [F,dif_pos hψ]
    exact (Classical.choose_spec (hcoeff ψ hψ)).2
  have hcoord (n : ℤ) : DifferentiableOn ℂ (fun ψ => F ψ n) V := by
    intro ψ hψ
    have hdev : DifferentiableAt ℂ
        (fun χ : CoeffPair p => sourceNormalizedActionRootDeviation hp hp1 χ n) ψ := by
      change DifferentiableAt ℂ
        (fun χ : CoeffPair p => sourceNormalizedActionRoot hp hp1 n χ - 1) ψ
      exact ((hrootdiff n ψ hψ.2).differentiableAt
        (hVropen.mem_nhds hψ.2)).sub_const 1
    have heq : (fun χ : CoeffPair p => F χ n) =ᶠ[𝓝 ψ]
        (fun χ : CoeffPair p => sourceNormalizedActionRootDeviation hp hp1 χ n) := by
      filter_upwards [hVopen.mem_nhds hψ] with χ hχ
      exact hFapply χ hχ n
    exact (hdev.congr_of_eventuallyEq heq).differentiableWithinAt
  have hFdiff : DifferentiableOn ℂ F V :=
    Coeff.differentiableOn_of_bounded_coordinatewise F hVopen hcoord M hFbound
  exact ⟨V,hVopen,⟨hφVd,hφVr⟩,M,F,hFapply,hFbound,
    hFdiff.continuousOn,hFdiff⟩

end NLS.ZakharovShabat
