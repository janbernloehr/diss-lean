import NLS.ZakharovShabat.SourceFullAbelianPrimitive
import NLS.ZakharovShabat.SourceCriticalRootRatioJointAnalytic
import NLS.ComplexAnalysis.PiecewiseC1Loop

/-! # Zero actual critical-root periods from a verified full primitive -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem SourceAbelianSpectralChart.continuousOn_criticalRatio
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)} {ψ : CoeffPair p}
    (D : SourceAbelianSpectralChart hp hp1 W ψ) :
    ContinuousOn (fun z => sourceCriticalRootRatioJoint hp hp1 (z,ψ)) (sourceCanonicalRootDomain hp hp1 ψ) := by
  have hc : ContinuousOn (deriv (D.primitive 0)) (sourceCanonicalRootDomain hp hp1 ψ) := by
    intro z hz
    exact (D.analytic 0 z (sourceCanonicalRootDomain_subset_openGapComplement hp hp1 ψ hz)).deriv.continuousAt.continuousWithinAt
  exact hc.congr (fun z hz => (D.derivative 0 z hz).deriv.symm)

theorem SourceAbelianSpectralChart.criticalRatio_loop_integral_eq_zero
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)} {ψ : CoeffPair p}
    (D : SourceAbelianSpectralChart hp hp1 W ψ) (Γ : PiecewiseC1Loop)
    (hΓ : Γ.Inside (sourceCanonicalRootDomain hp hp1 ψ)) :
    Γ.integral (fun z => sourceCriticalRootRatioJoint hp hp1 (z,ψ)) = 0 :=
  Γ.integral_eq_zero_of_primitive _ (D.primitive 0) _ D.continuousOn_criticalRatio
    (fun z hz => D.derivative 0 z hz) hΓ

end NLS.ZakharovShabat
