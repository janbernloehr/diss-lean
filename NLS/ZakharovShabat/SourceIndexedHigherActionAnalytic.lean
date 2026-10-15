import NLS.ZakharovShabat.SourceIndexedHigherAction
import NLS.ZakharovShabat.SourceIndexedActionAnalytic
import NLS.ZakharovShabat.SourceHigherActionRegularity

/-! # Analyticity and physical formulas for original higher actions

No containment in the older real-chart union is assumed. Analyticity
holds on the full original domain, simultaneously at every index and level.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- All higher actions are analytic throughout the unchanged original contour domain. -/
theorem SourceSection11ContourData.analytic_indexedHigherAction {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (h : SourceSection11ContourData hp hp1 W) (hW : IsOpen W) (n : ℤ) (k : ℕ) :
    AnalyticOnNhd ℂ (sourceIndexedHigherAction hp hp1 n k) W := by
  apply analyticOnNhd_of_complexDifferentiableOn _ W hW
  intro ψ hψ
  obtain ⟨U,hU,_,hψU,hUW,D,c,hD,C,_⟩ := h.neighborhoods ψ hψ
  have H := h.previous.previous.previous.previous
  have ha := sourceHigherActionCircle_analyticOnNhd hp hp1 H.joint.1 H.joint.2 hU
    (C.center n : ℂ) (C.radius n) ((C.inner_pos n).trans (C.inner_lt n)).le
    (fun χ hχ z hz => ⟨hUW hχ,C.collar_subset_rootDomain hD χ hχ n (C.sphere_subset_collar n hz)⟩) k
  have he : sourceIndexedHigherAction hp hp1 n k =ᶠ[𝓝 ψ]
      (fun χ => sourceHigherActionCircle hp hp1 χ (C.center n : ℂ) (C.radius n) k) := by
    filter_upwards [hU.mem_nhds hψU] with χ hχ
    exact sourceIndexedHigherAction_eq_circle (C.periodCircle hD χ hχ n) k
  exact ((ha ψ hψU).differentiableAt.congr_of_eventuallyEq he).differentiableWithinAt

/-- Real values agree with the actual spectral-power gap integral at every level. -/
theorem sourceIndexedHigherAction_eq_real (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) (k : ℕ) :
    sourceIndexedHigherAction hp hp1 n k φ.val = (sourceRealHigherAction hp hp1 φ n k : ℂ) := by
  obtain ⟨N,ε,_,_,V,_,_,hφV,c,hD⟩ :=
    exists_local_source_quantitative_isolating_discs hp hp1 φ.val φ.property
  obtain ⟨a,r,hr,he⟩ := hD.discs n
  let D := hD.periodCircle φ.val hφV n a r hr he
  rw [sourceIndexedHigherAction_eq_circle D k]
  exact sourceHigherActionCircle_eq_real_of_realCentered_enclosingCircle hp hp1 φ n k
    (D.center : ℂ) D.radius (by simp) D.radius_pos D.gap D.closedBall_subset_omittedDomain

/-- Formula (5.2) uses any retained primitive index on every original isolating circle. -/
theorem sourceIndexedHigherAction_eq_primitive {hp : p ≠ ⊤} {hp1 : 1 < p}
    {ψ : CoeffPair p} {n : ℤ} (C : SourceCriticalRootPeriodCircle hp hp1 ψ n)
    {W : Set (CoeffPair p)} (D : SourceAbelianSpectralChart hp hp1 W ψ) (k : ℕ) (q : ℤ) :
    sourceIndexedHigherAction hp hp1 n k ψ = -(Real.pi:ℂ)⁻¹ *
      ∮ z in C((C.center:ℂ),C.radius), z^k*sourceFullAbelianPrimitive hp hp1 W q (z,ψ) := by
  rw [sourceIndexedHigherAction_eq_circle C k]
  exact sourceHigherActionCircle_eq_primitive hp hp1 W q ψ D (C.center:ℂ) C.radius
    C.radius_pos.le C.sphere_subset_rootDomain k

end NLS.ZakharovShabat
