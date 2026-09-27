import NLS.ZakharovShabat.SourceNormalizedActionRootCommonExponentDomain
import NLS.ZakharovShabat.SourceNormalizedActionComplexAllCoordinates
import NLS.SequenceSpaces.BoundedCoordinateDifferentiable

/-!
# One holomorphy domain for all normalized-action exponents

The normalized-action deviation has a locally uniform `ℓq` norm
bound on a common source neighborhood for every finite `q > 1` when
`1 < p ≤ 2`. Its scalar coordinates are differentiable on another
neighborhood independent of `q`. Their intersection supports
Fréchet-holomorphic `ℓq` realizations for all target exponents.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- For `1 < p ≤ 2`, one complex source neighborhood supports the
normalized-action deviation as a locally bounded,
Fréchet-holomorphic `ℓq`-valued map for every finite `q > 1`. -/
theorem exists_local_sourceNormalizedActionDeviation_holomorphic_allExponents
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∀ (q : ℝ≥0∞) [Fact (1 ≤ q)] (_hq1 : 1 < q) (_hq : q ≠ ⊤),
        ∃ M : ℝ, ∃ F : CoeffPair p → Coeff q,
          (∀ ψ ∈ V, ∀ n : ℤ,
            F ψ n = sourceNormalizedActionDeviation hp hp1 ψ n) ∧
          (∀ ψ ∈ V, ‖F ψ‖ ≤ M) ∧
          ContinuousOn F V ∧ DifferentiableOn ℂ F V := by
  classical
  obtain ⟨Va,hVaopen,hφVa,haction⟩ :=
    exists_local_sourceNormalizedActionDeviation_allExponents
      hp hp1 hp2 φ hφ
  obtain ⟨Vd,hVdopen,hφVd,hdiff⟩ :=
    exists_local_sourceNormalizedActionComplexExtension_allCoordinates_differentiableOn
      hp hp1 φ hφ
  let V := Va ∩ Vd
  have hVopen : IsOpen V := hVaopen.inter hVdopen
  refine ⟨V,hVopen,⟨hφVa,hφVd⟩,?_⟩
  intro q hqFact hq1 hq
  obtain ⟨M,hbound⟩ := haction q hq1 hq
  have hcoeff (ψ : CoeffPair p) (hψ : ψ ∈ V) :
      ∃ A : Coeff q,
        (∀ n : ℤ, A n = sourceNormalizedActionDeviation hp hp1 ψ n) ∧
        ‖A‖ ≤ M := hbound ψ hψ.1
  let F : CoeffPair p → Coeff q := fun ψ =>
    if hψ : ψ ∈ V then Classical.choose (hcoeff ψ hψ) else 0
  have hFapply (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ) :
      F ψ n = sourceNormalizedActionDeviation hp hp1 ψ n := by
    simp only [F,dif_pos hψ]
    exact (Classical.choose_spec (hcoeff ψ hψ)).1 n
  have hFbound (ψ : CoeffPair p) (hψ : ψ ∈ V) : ‖F ψ‖ ≤ M := by
    simp only [F,dif_pos hψ]
    exact (Classical.choose_spec (hcoeff ψ hψ)).2
  have hcoord (n : ℤ) : DifferentiableOn ℂ (fun ψ => F ψ n) V := by
    intro ψ hψ
    have hdev : DifferentiableAt ℂ
        (fun χ : CoeffPair p => sourceNormalizedActionDeviation hp hp1 χ n) ψ := by
      change DifferentiableAt ℂ (fun χ : CoeffPair p =>
        4 * sourceNormalizedActionComplexExtension hp hp1 n χ - 1) ψ
      exact (((hdiff n ψ hψ.2).differentiableAt
        (hVdopen.mem_nhds hψ.2)).const_mul 4).sub_const 1
    have heq : (fun χ : CoeffPair p => F χ n) =ᶠ[𝓝 ψ]
        (fun χ : CoeffPair p => sourceNormalizedActionDeviation hp hp1 χ n) := by
      filter_upwards [hVopen.mem_nhds hψ] with χ hχ
      exact hFapply χ hχ n
    exact (hdev.congr_of_eventuallyEq heq).differentiableWithinAt
  have hFdiff : DifferentiableOn ℂ F V :=
    Coeff.differentiableOn_of_bounded_coordinatewise F hVopen hcoord M hFbound
  exact ⟨M,F,hFapply,hFbound,hFdiff.continuousOn,hFdiff⟩

/-- One complex source neighborhood works simultaneously for the
normalized-action and principal-root deviations, with holomorphic
`ℓq` realizations and locally uniform norm bounds at every finite
`q > 1`. -/
theorem exists_local_sourceNormalizedAction_and_root_holomorphic_allExponents
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∀ (q : ℝ≥0∞) [Fact (1 ≤ q)] (_hq1 : 1 < q) (_hq : q ≠ ⊤),
        ∃ A R : CoeffPair p → Coeff q,
          (∀ ψ ∈ V, ∀ n : ℤ,
            A ψ n = sourceNormalizedActionDeviation hp hp1 ψ n ∧
            R ψ n = sourceNormalizedActionRootDeviation hp hp1 ψ n) ∧
          DifferentiableOn ℂ A V ∧ DifferentiableOn ℂ R V ∧
          ∃ Ma Mr : ℝ, ∀ ψ ∈ V, ‖A ψ‖ ≤ Ma ∧ ‖R ψ‖ ≤ Mr := by
  obtain ⟨Va,hVaopen,hφVa,haction⟩ :=
    exists_local_sourceNormalizedActionDeviation_holomorphic_allExponents
      hp hp1 hp2 φ hφ
  obtain ⟨Vr,hVropen,hφVr,hroot⟩ :=
    exists_local_sourceNormalizedActionRootDeviation_allExponents
      hp hp1 hp2 φ hφ
  let V := Va ∩ Vr
  refine ⟨V,hVaopen.inter hVropen,⟨hφVa,hφVr⟩,?_⟩
  intro q hqFact hq1 hq
  obtain ⟨Ma,A,hAapply,hAbound,_,hAdiff⟩ := haction q hq1 hq
  obtain ⟨Mr,R,hRapply,hRbound,_,hRdiff⟩ := hroot q hq1 hq
  refine ⟨A,R,?_,hAdiff.mono inter_subset_left,
    hRdiff.mono inter_subset_right,Ma,Mr,?_⟩
  · intro ψ hψ n
    exact ⟨hAapply ψ hψ.1 n,hRapply ψ hψ.2 n⟩
  · intro ψ hψ
    exact ⟨hAbound ψ hψ.1,hRbound ψ hψ.2⟩

end NLS.ZakharovShabat
