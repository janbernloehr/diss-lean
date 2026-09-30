import NLS.ZakharovShabat.SourceAngularJointAnnulusPrimitive
import NLS.ZakharovShabat.SourceAngularEtaRemainder

/-! # Jointly analytic annular primitives of the actual eta remainder

Subtracting the eta model cancels the exact diagonal period on each
assigned enclosing circle. The explicit annular primitive is therefore
jointly analytic and has the actual remainder as spectral derivative,
at every complex source in the chart, including collapsed gaps.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceAngularEtaRemainderJointAnnularPrimitive
    (hp : p ≠ ⊤) (hp1 : 1 < p) (m : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k)
    (c : ℂ) (r R : ℝ) (z₀ : ℂ) : ℂ × CoeffPair p → ℂ :=
  parametricAnnularPrimitiveAtAnchor
    (fun x => sourceAngularEtaRemainderIntegrand hp hp1 m s x.2 x.1) c r R z₀

@[simp] theorem sourceAngularEtaRemainderJointAnnularPrimitive_anchor
    (hp : p ≠ ⊤) (hp1 : 1 < p) (m : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k)
    (c : ℂ) (r R : ℝ) (z₀ : ℂ) (ψ : CoeffPair p) :
    sourceAngularEtaRemainderJointAnnularPrimitive hp hp1 m s c r R z₀ (z₀,ψ) = 0 :=
  parametricAnnularPrimitiveAtAnchor_anchor _ _ r R z₀ ψ

namespace SourceAngularJointAnnulusChartData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {m : ℤ}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
  {W V : Set (CoeffPair p)} {c : ℤ → ℂ} {T : ℤ → ℝ} {r R : ℝ} {z₀ : ℂ}

theorem analyticOnNhd_etaRemainder_joint
    (D : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀) :
    AnalyticOnNhd ℂ (fun x : ℂ × CoeffPair p => sourceAngularEtaRemainderIntegrand hp hp1 m s x.2 x.1)
      ((closedBall (c m) R \ ball (c m) r) ×ˢ V) := by
  intro x hx
  have hne := sourceStandardRoot_ne_zero_off_segment hp hp1 x.2 m x.1
    (fun h => hx.1.2 (D.gap_enclosed x.2 hx.2 h))
  exact (D.integrand_analytic m x hx).sub
    (analyticAt_const.div (D.selected_root_analytic x hx) hne)

theorem etaRemainder_period_zero
    (D : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) :
    (∮ z in C(c m,r), sourceAngularEtaRemainderIntegrand hp hp1 m s ψ z) = 0 := by
  have hdisc := D.disc_family ψ hψ
  have hrT : r < T m := D.inner_lt_outer.trans D.outer_lt_assigned
  have hperiod : sourcePsiContour hp hp1 m (s m ψ : Coeff p) ψ (c m) r = 1 := by
    rw [sourcePsiContour_eq_of_nested_enclosingCircles hp hp1 m m (s m ψ : Coeff p) ψ
      (c m) (c m) r (T m) D.inner_pos (hdisc.contour_family.2 m).1 (D.gap_enclosed ψ hψ)
      (hdisc.contour_family.2 m).2.1 (closedBall_subset_closedBall hrT.le)
      (hdisc.contour_family.2 m).2.2.1]
    simpa using hdisc.periods m m
  exact circleIntegral_sourceAngularEtaRemainderIntegrand_eq_zero hp hp1 m s ψ (c m) r D.inner_pos
    (D.gap_enclosed ψ hψ) ((closedBall_subset_closedBall hrT.le).trans
      (hdisc.contour_family.2 m).2.2.1) hperiod

theorem analyticOnNhd_etaRemainderJointAnnularPrimitive
    (D : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀) :
    AnalyticOnNhd ℂ (sourceAngularEtaRemainderJointAnnularPrimitive hp hp1 m s (c m) r R z₀)
      ((ball (c m) R \ closedBall (c m) r) ×ˢ V) :=
  analyticOnNhd_parametricAnnularPrimitiveAtAnchor _ _ r R D.inner_pos D.inner_lt_outer
    V D.source_open D.analyticOnNhd_etaRemainder_joint z₀ D.anchor_mem

theorem etaRemainderJointAnnularPrimitive_derivative
    (D : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (z : ℂ) (hz : z ∈ ball (c m) R \ closedBall (c m) r) :
    HasDerivAt (fun w => sourceAngularEtaRemainderJointAnnularPrimitive hp hp1 m s (c m) r R z₀ (w,ψ))
      (sourceAngularEtaRemainderIntegrand hp hp1 m s ψ z) z :=
  hasDerivAt_parametricAnnularPrimitiveAtAnchor _ _ r R D.inner_pos D.inner_lt_outer
    V D.source_open D.analyticOnNhd_etaRemainder_joint z₀ ψ hψ (D.etaRemainder_period_zero ψ hψ) z hz

end SourceAngularJointAnnulusChartData
end NLS.ZakharovShabat
