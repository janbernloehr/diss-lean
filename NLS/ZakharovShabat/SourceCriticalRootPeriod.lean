import NLS.ZakharovShabat.SourceCriticalRootPeriodCircle
import NLS.ZakharovShabat.SourceEquation2_15
import NLS.ComplexAnalysis.HolomorphicCircleIntegral
import NLS.ComplexAnalysis.BanachHolomorphicAnalytic

/-!
# The indexed critical-root period on the common source domain

Circle independence defines one period at each source. Locally it is the
integral on any original fixed circle, so joint analyticity of the
quotient implies analyticity of the period on the entire retained domain.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The unweighted indexed period; the arbitrary value outside sources
admitting an isolating circle is never used on the common domain. -/
def sourceCriticalRootPeriod (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (ψ : CoeffPair p) : ℂ := by
  classical
  exact if h : Nonempty (SourceCriticalRootPeriodCircle hp hp1 ψ n) then
    let D := Classical.choice h
    ∮ z in C((D.center : ℂ),D.radius), sourceCriticalRootRatioJoint hp hp1 (z,ψ)
  else 0

/-- Any valid circle computes the period, regardless of its choice. -/
theorem sourceCriticalRootPeriod_eq_circle
    {hp : p ≠ ⊤} {hp1 : 1 < p} {ψ : CoeffPair p} {n : ℤ}
    (D : SourceCriticalRootPeriodCircle hp hp1 ψ n) :
    sourceCriticalRootPeriod hp hp1 n ψ =
      ∮ z in C((D.center : ℂ),D.radius), sourceCriticalRootRatioJoint hp hp1 (z,ψ) := by
  classical
  rw [sourceCriticalRootPeriod,dif_pos (show Nonempty (SourceCriticalRootPeriodCircle hp hp1 ψ n) from ⟨D⟩)]
  exact SourceCriticalRootPeriodCircle.integral_eq _ D

/-- The period is represented on the full original source neighborhood
by its original boundary circle. -/
theorem SourceIsolatingNeighborhoods.period_eq_originalCircle
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (n : ℤ) (a r : ℝ) (hr : 0 < r) (he : D n = ball (a : ℂ) r)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) :
    sourceCriticalRootPeriod hp hp1 n ψ =
      ∮ z in C((a : ℂ),r), sourceCriticalRootRatioJoint hp hp1 (z,ψ) :=
  sourceCriticalRootPeriod_eq_circle (hD.periodCircle ψ hψ n a r hr he)

/-- Local fixed-circle representatives make the period holomorphic on W;
the domain is not replaced by smaller neighborhoods of real sources. -/
theorem SourceEquation2_15Data.analytic_period
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (h : SourceEquation2_15Data hp hp1 W) (hW : IsOpen W) (n : ℤ) :
    AnalyticOnNhd ℂ (sourceCriticalRootPeriod hp hp1 n) W := by
  apply NLS.ComplexAnalysis.analyticOnNhd_of_complexDifferentiableOn _ W hW
  intro ψ hψ
  obtain ⟨V,hV,_,hψV,hVW,D,c,hD,_,_⟩ := h.neighborhoods ψ hψ
  obtain ⟨a,r,hr,he⟩ := hD.toSourceIsolatingNeighborhoods.discs n
  have hcircle : ∀ z ∈ sphere (a : ℂ) r,
      (z,ψ) ∈ sourceCanonicalRootJointDomain hp hp1 W := by
    intro z hz
    exact ⟨hψ,(hD.toSourceIsolatingNeighborhoods.periodCircle ψ hψV n a r hr he).sphere_subset_rootDomain hz⟩
  have hd := NLS.ComplexAnalysis.hasFDerivAt_circleIntegral_of_jointDifferentiable
    (sourceCriticalRootRatioJoint hp hp1) _ h.joint.1 h.joint.2.differentiableOn
    (a : ℂ) r hr.le ψ hcircle
  have hlocal : sourceCriticalRootPeriod hp hp1 n =ᶠ[𝓝 ψ]
      (fun χ => ∮ z in C((a : ℂ),r), sourceCriticalRootRatioJoint hp hp1 (z,χ)) := by
    filter_upwards [hV.mem_nhds hψV] with χ hχ
    exact hD.toSourceIsolatingNeighborhoods.period_eq_originalCircle n a r hr he χ hχ
  exact (hd.differentiableAt.congr_of_eventuallyEq hlocal).differentiableWithinAt

end NLS.ZakharovShabat
