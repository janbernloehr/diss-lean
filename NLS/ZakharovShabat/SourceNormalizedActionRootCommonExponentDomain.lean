import NLS.ZakharovShabat.SourceNormalizedActionCommonExponentDomain
import NLS.ZakharovShabat.SourceNormalizedActionRootSequenceSpace

/-!
# One source domain for all principal-root sequence exponents

The principal square root is one-sided Lipschitz at one. The common
domain for the normalized-action deviation therefore supplies a
common domain for its root deviation. Fixing `q = 2` in the scalar
root regularity theorem also gives one differentiability domain for
all coordinates, independent of the target sequence exponent.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- When `1 < p ≤ 2`, one complex source neighborhood supports the
principal-root deviation as a locally bounded, Fréchet-holomorphic
`ℓq`-valued map for every finite `q > 1`. -/
theorem exists_local_sourceNormalizedActionRootDeviation_allExponents
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∀ (q : ℝ≥0∞) [Fact (1 ≤ q)] (_hq1 : 1 < q) (_hq : q ≠ ⊤),
        ∃ M : ℝ, ∃ F : CoeffPair p → Coeff q,
          (∀ ψ ∈ V, ∀ n : ℤ,
            F ψ n = sourceNormalizedActionRootDeviation hp hp1 ψ n) ∧
          (∀ ψ ∈ V, ‖F ψ‖ ≤ M) ∧
          ContinuousOn F V ∧ DifferentiableOn ℂ F V := by
  classical
  obtain ⟨Va,hVaopen,hφVa,haction⟩ :=
    exists_local_sourceNormalizedActionDeviation_allExponents
      hp hp1 hp2 φ hφ
  have hhalf2 : ENNReal.ofReal (p.toReal/2) ≤ (2 : ℝ≥0∞) :=
    (source_half_le_one hp hp2).trans (by norm_num)
  obtain ⟨Vr,hVropen,hφVr,_,_,_,hrootdiff,_⟩ :=
    exists_local_sourceNormalizedActionRoot_allCoordinates
      (q := 2) hp hp1 (by norm_num) (by norm_num) hhalf2 φ hφ
  let V := Va ∩ Vr
  have hVopen : IsOpen V := hVaopen.inter hVropen
  refine ⟨V,hVopen,⟨hφVa,hφVr⟩,?_⟩
  intro q hqFact hq1 hq
  obtain ⟨M,hbound⟩ := haction q hq1 hq
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
  exact ⟨M,F,hFapply,hFbound,hFdiff.continuousOn,hFdiff⟩

end NLS.ZakharovShabat
