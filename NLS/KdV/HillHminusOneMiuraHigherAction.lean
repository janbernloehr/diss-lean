import NLS.KdV.HillHminusOneMiuraContour
import NLS.ZakharovShabat.SourceCriticalRootPiecewiseZeroPeriod

/-! # The actual Hill contour is twice the Dirac level-two action

The exact energy shift contributes a critical-root quotient period,
which vanishes by the verified full primitive. The resulting factor two
comes from the original higher-action normalization, not a convention
chosen for this bridge.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV

def hillHminusMiuraIndexedAction (u : Coeff 2) (n : ℤ) : ℂ :=
  2*sourceIndexedHigherAction (by simp) (by norm_num) n 1 (hillMiuraDiagonal u)

theorem hillHminusMiuraContourAction_eq_twice_higherContour
    (q : PeriodOneHminusOne) (u : Coeff 2) (c : ℂ)
    (himage : periodOneMiura u = q+periodOneL2Inclusion (lp.single 2 0 c))
    (W : Set (CoeffPair 2)) (D : SourceAbelianSpectralChart (by simp) (by norm_num) W (hillMiuraDiagonal u))
    (Γ : PiecewiseC1Loop) (hΓ : Γ.Inside {z : ℂ | 0 < z.re})
    (hroot : Γ.Inside (sourceCanonicalRootDomain (by simp) (by norm_num) (hillMiuraDiagonal u))) :
    hillHminusMiuraContourAction q u c (quadraticEnergyLoop Γ c) =
      2*sourceHigherActionContour (by simp) (by norm_num) (hillMiuraDiagonal u) Γ 1 := by
  let Q : ℂ → ℂ := fun z => sourceCriticalRootRatioJoint (by simp) (by norm_num) (z,hillMiuraDiagonal u)
  have hQ : ContinuousOn Q (sourceCanonicalRootDomain (by simp) (by norm_num) (hillMiuraDiagonal u)) :=
    D.continuousOn_criticalRatio
  have he : (fun z : ℂ => (z^2-c)*Q z) = (fun z => z^2*Q z-c*Q z) := by funext z; ring
  rw [hillHminusMiuraContourAction_quadratic_pullback q u c himage Γ hΓ]
  change (1/(Real.pi : ℂ))*Γ.integral (fun z => (z^2-c)*Q z) = _
  have hs : Γ.integral (fun z => z^2*Q z-c*Q z) =
      Γ.integral (fun z => z^2*Q z)-Γ.integral (fun z => c*Q z) :=
    Γ.integral_sub (fun z => z^2*Q z) (fun z => c*Q z)
      ((continuousOn_id.pow 2).mul hQ) (continuousOn_const.mul hQ) hroot
  have hz : Γ.integral Q = 0 := D.criticalRatio_loop_integral_eq_zero Γ hroot
  rw [he,hs,Γ.integral_const_mul,hz,mul_zero,sub_zero]
  dsimp [sourceHigherActionContour,Q]
  norm_num
  field_simp

theorem hillHminusMiuraContourAction_eq_indexed
    (q : PeriodOneHminusOne) (u : Coeff 2) (c : ℂ)
    (himage : periodOneMiura u = q+periodOneL2Inclusion (lp.single 2 0 c))
    (W : Set (CoeffPair 2)) (D : SourceAbelianSpectralChart (by simp) (by norm_num) W (hillMiuraDiagonal u))
    (n : ℤ) (C : SourceCriticalRootPeriodCircle (by simp) (by norm_num) (hillMiuraDiagonal u) n)
    (hpos : 0 < C.center-C.radius) :
    hillHminusMiuraContourAction q u c
      (quadraticEnergyLoop (PiecewiseC1Loop.circle (C.center : ℂ) C.radius) c) =
      hillHminusMiuraIndexedAction u n := by
  let Γ := PiecewiseC1Loop.circle (C.center : ℂ) C.radius
  have hΓ : Γ.Inside {z : ℂ | 0 < z.re} := by
    intro i t
    have hs : Γ.edge i t ∈ sphere (C.center : ℂ) C.radius :=
      circleMap_mem_sphere (C.center : ℂ) C.radius_pos.le ((2*Real.pi)*(t : ℝ))
    have hb := re_bounds_of_mem_realCenteredClosedBall (sphere_subset_closedBall hs)
    change 0 < (Γ.edge i t).re
    linarith [hb.1]
  have hroot : Γ.Inside (sourceCanonicalRootDomain (by simp) (by norm_num) (hillMiuraDiagonal u)) := by
    intro i t
    exact C.sphere_subset_rootDomain (circleMap_mem_sphere (C.center : ℂ) C.radius_pos.le ((2*Real.pi)*(t : ℝ)))
  rw [hillHminusMiuraContourAction_eq_twice_higherContour q u c himage W D Γ hΓ hroot,
    sourceHigherActionContour_circle,← sourceIndexedHigherAction_eq_circle C 1]
  rfl

theorem winding_one_miura_action_contour
    (u : Coeff 2) (c : ℂ) (n : ℤ)
    (C : SourceCriticalRootPeriodCircle (by simp) (by norm_num) (hillMiuraDiagonal u) n)
    (hpos : 0 < C.center-C.radius) :
    (quadraticEnergyLoop (PiecewiseC1Loop.circle (C.center : ℂ) C.radius) c).windingIntegral
      ((sourceStandardRootMidpoint (by simp) (by norm_num) (hillMiuraDiagonal u) n)^2-c) = 1 := by
  let a := sourceStandardRootMidpoint (by simp) (by norm_num) (hillMiuraDiagonal u) n
  have ha : a ∈ ball (C.center : ℂ) C.radius := C.gap (sourcePeriodicMidpoint_mem_segment _ _ _ _)
  have hare : 0 < a.re := by
    have hb := re_bounds_of_mem_realCenteredClosedBall (ball_subset_closedBall ha)
    linarith [hb.1]
  have hna : -a ∉ closedBall (C.center : ℂ) C.radius := by
    intro he
    have hb := re_bounds_of_mem_realCenteredClosedBall he
    simp only [neg_re] at hb
    linarith [hb.1]
  exact windingIntegral_quadraticEnergyCircle_one (C.center : ℂ) a c C.radius ha hna

end NLS.KdV
