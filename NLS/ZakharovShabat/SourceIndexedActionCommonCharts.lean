import NLS.ZakharovShabat.SourceIndexedActionAnalytic

/-!
# One complex neighborhood identifies every indexed action

Simultaneous contour circles supply real-centered action charts with one
common source ball. Thus every new indexed action agrees with the earlier
glued action on that ball, without an infinite intersection of neighborhoods.
-/

noncomputable section
open Set Metric Complex Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- All signed indices agree with the older action on one source neighborhood. -/
theorem SourceSection11ContourData.indexedAction_eq_complexAction_allIndices_near_real
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceSection11ContourData hp hp1 W)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) (hφW : φ ∈ W) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ IsConnected U ∧ φ ∈ U ∧ U ⊆ W ∧
      ∀ ψ ∈ U, ∀ n : ℤ, ψ ∈ sourceComplexActionDomain hp hp1 n ∧
        sourceIndexedAction hp hp1 n ψ = sourceComplexAction hp hp1 n ψ := by
  obtain ⟨V,hV,_,hφV,hVW,D,c,hD,C,ha⟩ := H.neighborhoods φ hφW
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hφV)
  let ch (n : ℤ) : SourceRealActionBallChart hp hp1 n := {
    center := φ
    center_real := hφ
    radius := r
    radius_pos := hr
    spectralCenter := (C.center n : ℂ)
    spectralRadius := C.radius n
    spectralRadius_pos := (C.inner_pos n).trans (C.inner_lt n)
    geometry := fun ψ hψ =>
      ⟨(C.periodCircle hD ψ (hball hψ) n).gap,
        (C.periodCircle hD ψ (hball hψ) n).closedBall_subset_omittedDomain⟩
    differentiable := ((ha n).2.differentiableOn).mono hball
    agrees_real := fun ψ hψ hreal =>
      (sourceIndexedAction_eq_sourceRealAction hp hp1 n ψ hreal).symm.trans
        (C.indexedAction_eq_circle hD ψ (hball hψ) n)
  }
  refine ⟨ball φ r,isOpen_ball,isConnected_ball hr,mem_ball_self hr,hball.trans hVW,?_⟩
  intro ψ hψ n
  exact ⟨⟨ch n,hψ⟩,(C.indexedAction_eq_circle hD ψ (hball hψ) n).trans
    (sourceComplexAction_eq_chart hp hp1 n (ch n) ψ hψ).symm⟩

end NLS.ZakharovShabat
