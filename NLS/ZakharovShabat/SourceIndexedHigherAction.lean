import NLS.ZakharovShabat.SourceIndexedAction
import NLS.ZakharovShabat.SourceHigherActionCircle

/-! # Original indexed higher actions

Polynomial spectral weights preserve the cut-avoiding homotopy between
original isolating circles. The natural index k means printed level k+1.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Any two original isolating circles compute the same higher action. -/
theorem SourceCriticalRootPeriodCircle.higherAction_eq {hp : p ≠ ⊤} {hp1 : 1 < p} {ψ : CoeffPair p} {n : ℤ}
    (D E : SourceCriticalRootPeriodCircle hp hp1 ψ n) (k : ℕ) :
    sourceHigherActionCircle hp hp1 ψ (D.center : ℂ) D.radius k =
      sourceHigherActionCircle hp hp1 ψ (E.center : ℂ) E.radius k := by
  let H := ContinuousMap.Homotopy.affine
    (circlePath (D.center : ℂ) D.radius : C(I,ℂ)) (circlePath (E.center : ℂ) E.radius)
  let f : ℂ → ℂ := fun z => z^(k+1)*sourceCriticalRootRatioJoint hp hp1 (z,ψ)
  have hclosed : IsClosed (range H) := (isCompact_range (map_continuous H)).isClosed
  have he : (∫ᶜ z in circlePath (D.center : ℂ) D.radius, holomorphicOneForm f z) =
      ∫ᶜ z in circlePath (E.center : ℂ) E.radius, holomorphicOneForm f z := by
    apply curveIntegral_eq_of_holomorphic_homotopy f H
      (affineHomotopy_loop (γ₁ := circlePath (D.center : ℂ) D.radius)
        (γ₂ := circlePath (E.center : ℂ) E.radius)) (t := range H)
    · intro s _ u _
      exact ⟨(s,u),rfl⟩
    · intro z hz
      have hz' : z ∈ range H := by simpa only [hclosed.closure_eq] using hz
      exact ((analyticAt_id.pow (k+1)).mul
        (sourceCriticalRootRatio_analyticOnNhd hp hp1 ψ z (D.homotopy_range E hz'))).differentiableAt
    · exact affineHomotopy_contDiffOn (circlePath_contDiffOn _ _) (circlePath_contDiffOn _ _)
  rw [curveIntegral_circlePath,curveIntegral_circlePath] at he
  exact congrArg (((k+1:ℂ)*(Real.pi:ℂ))⁻¹ * ·) he

/-- The original indexed action at printed level `k+1`, with zero off its contour domain. -/
def sourceIndexedHigherAction (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (k : ℕ) (ψ : CoeffPair p) : ℂ := by
  classical
  exact if h : Nonempty (SourceCriticalRootPeriodCircle hp hp1 ψ n) then
    let D := Classical.choice h
    sourceHigherActionCircle hp hp1 ψ (D.center : ℂ) D.radius k
  else 0

/-- Every original isolating circle computes the indexed higher action. -/
theorem sourceIndexedHigherAction_eq_circle {hp : p ≠ ⊤} {hp1 : 1 < p}
    {ψ : CoeffPair p} {n : ℤ} (D : SourceCriticalRootPeriodCircle hp hp1 ψ n) (k : ℕ) :
    sourceIndexedHigherAction hp hp1 n k ψ = sourceHigherActionCircle hp hp1 ψ (D.center : ℂ) D.radius k := by
  classical
  rw [sourceIndexedHigherAction,dif_pos (show Nonempty (SourceCriticalRootPeriodCircle hp hp1 ψ n) from ⟨D⟩)]
  exact SourceCriticalRootPeriodCircle.higherAction_eq _ D k

/-- At printed level one this is exactly the original indexed action, including defaults. -/
theorem sourceIndexedHigherAction_zero (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (ψ : CoeffPair p) :
    sourceIndexedHigherAction hp hp1 n 0 ψ = sourceIndexedAction hp hp1 n ψ := by
  classical
  unfold sourceIndexedHigherAction sourceIndexedAction
  split <;> simp_all only [sourceHigherActionCircle_zero]

end NLS.ZakharovShabat
