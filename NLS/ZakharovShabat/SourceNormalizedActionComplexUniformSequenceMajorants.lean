import NLS.ZakharovShabat.SourceNormalizedActionUniformCircleComplexAgreement
import NLS.ZakharovShabat.SourceNormalizedActionUniformCircleMajorants

/-!
# Complex-source majorants for the normalized action

The common-circle candidate has locally uniform `ℓq + ℓ^(p/2)`
majorants. Its equality with the chart-independent normalized action
on one complex source ball transfers those estimates to the actual
normalized action, without excluding collapsed complex gaps.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)]

/-- On one complex source neighborhood, every sufficiently distant
chart-independent normalized action is source-differentiable. -/
theorem exists_local_sourceNormalizedActionComplexExtension_differentiableOn_tail
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    ∃ K : ℕ, ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∀ n : ℤ, K ≤ n.natAbs →
        DifferentiableOn ℂ (sourceNormalizedActionComplexExtension hp hp1 n) V := by
  obtain ⟨Kc,Vc,hVcopen,hφVc,hcandidate⟩ :=
    exists_local_source_distantNormalizedActionCircleCandidate_differentiableOn
      hp hp1 φ hreal
  obtain ⟨Ka,r,hr,hagree⟩ :=
    exists_local_sourceNormalizedAction_uniform_circle_complex_agreement
      hp hp1 φ hreal
  let V := Vc ∩ ball φ r
  let K := max (Kc+1) Ka
  have hVopen : IsOpen V := hVcopen.inter Metric.isOpen_ball
  refine ⟨K,V,hVopen,⟨hφVc,mem_ball_self hr⟩,?_⟩
  intro n hn ψ hψ
  have hKc : Kc < n.natAbs := by
    have h := le_trans (le_max_left (Kc+1) Ka) hn
    omega
  have hKa : Ka ≤ n.natAbs := le_trans (le_max_right _ _) hn
  let A := sourceNormalizedActionCircleCandidate hp hp1 n
    ((Real.pi:ℂ)*n) (Real.pi/8)
  let F := sourceNormalizedActionComplexExtension hp hp1 n
  have hA : DifferentiableAt ℂ A ψ :=
    ((hcandidate n hKc) ψ hψ.1).differentiableAt
      (hVcopen.mem_nhds hψ.1)
  have heq : F =ᶠ[𝓝 ψ] A := by
    filter_upwards [hVopen.mem_nhds hψ] with χ hχ
    exact (hagree χ hχ.2 n hKa).1.symm
  exact (hA.congr_of_eventuallyEq heq).differentiableWithinAt

/-- The chart-independent normalized action has locally uniform
`ℓq + ℓ^(p/2)` majorants on a complex source neighborhood of every
real-type potential, including collapsed complex gaps. -/
theorem exists_local_sourceNormalizedActionComplexExtension_complex_uniformSequenceMajorants
    [Fact (1 ≤ q)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (hq1 : 1 < q) (hq : q ≠ ⊤)
    (hhalf : ENNReal.ofReal (p.toReal/2) ≤ q)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ K : ℕ, ∃ Lq Lg : ℝ, ∀ ψ ∈ V,
        ∃ Cq : Coeff q, ∃ Cg : Coeff (ENNReal.ofReal (p.toReal/2)),
          (∀ n : ℤ, K ≤ n.natAbs →
            ‖4 * sourceNormalizedActionComplexExtension hp hp1 n ψ - 1‖ ≤
              ‖Cq n‖ + ‖Cg n‖) ∧
          ‖Cq‖ ≤ Lq ∧ ‖Cg‖ ≤ Lg := by
  obtain ⟨Vm,hVmopen,hφVm,Km,Lq,Lg,hmajor⟩ :=
    exists_local_sourceNormalizedAction_uniform_circle_sequenceMajorants
      hp hp1 hq1 hq hhalf φ hreal
  obtain ⟨Ka,r,hr,hagree⟩ :=
    exists_local_sourceNormalizedAction_uniform_circle_complex_agreement
      hp hp1 φ hreal
  let V := Vm ∩ ball φ r
  let K := max Km Ka
  refine ⟨V,hVmopen.inter Metric.isOpen_ball,
    ⟨hφVm,mem_ball_self hr⟩,K,Lq,Lg,?_⟩
  intro ψ hψ
  obtain ⟨Cq,Cg,hpoint,hCq,hCg⟩ := hmajor ψ hψ.1
  refine ⟨Cq,Cg,?_,hCq,hCg⟩
  intro n hn
  have hKm : Km ≤ n.natAbs := le_trans (le_max_left _ _) hn
  have hKa : Ka ≤ n.natAbs := le_trans (le_max_right _ _) hn
  have heq := (hagree ψ hψ.2 n hKa).1
  rw [← heq]
  exact hpoint n hKm

end NLS.ZakharovShabat
