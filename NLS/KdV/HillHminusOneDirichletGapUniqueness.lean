import NLS.KdV.HillHminusOneDirichletBands
import NLS.KdV.HillHminusOneRealGapSigns
import NLS.FunctionalAnalysis.IntervalCurveMass
import NLS.ComplexAnalysis.PositiveZeroUniqueness

/-! # Exactly one simple Dirichlet root can lie in a canonical H^-1 gap

The signed real characteristic derivative is strictly positive at every
root in the indexed closed gap. Its sign follows from the actual terminal
multiplier, the canonical signed trace bound and the physical positive
mass in the original energy derivative identity. A real zero uniqueness
lemma then applies, including to the two endpoints of an open gap.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open MeasureTheory hiding extend
open scoped ComplexConjugate
open NLS.LinearVolterra NLS.ZakharovShabat NLS.MKdV NLS.FunctionalAnalysis NLS.ComplexAnalysis
namespace NLS.KdV

theorem hillHminusDirichlet_signed_deriv_pos
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ) (hn : 1 ≤ n) (x : ℝ)
    (hx : x ∈ Icc (hillHminusRealLabels q hr (2*n-1)) (hillHminusRealLabels q hr (2*n)))
    (hz : hillHminusDirichlet q x = 0) :
    0 < (-1 : ℝ)^n*(deriv (hillHminusDirichlet q) x).re := by
  let C := hillHminusMiuraChartAt q
  have hq : q ∈ C.domain := mem_hillHminusMiuraChartAt q
  let y := C.physicalPosition q x (0,1)
  let w := extend (C.physicalMomentum q x (0,1)) 1
  let d := (deriv (hillHminusDirichlet q) x).re
  let D := (hillHminusDiscriminant q x).re
  let s : ℝ := (-1)^n
  have hs : s^2 = 1 := by dsimp [s]; rw [← pow_mul,Nat.mul_comm n 2,pow_mul]; norm_num
  have hw : w.im = 0 := by
    have he := congrArg Complex.im (C.physicalMomentum_dirichlet_terminal_star_real q hq hr x hz)
    change -w.im = w.im at he
    linarith
  have he := congrArg Complex.re (C.dirichlet_terminal_multiplier q hq x hz)
  change (w^2-hillHminusDiscriminant q x*w+1).re = 0 at he
  have hquad : w.re^2-D*w.re+1 = 0 := by
    simpa only [pow_two,mul_re,sub_re,add_re,hw,mul_zero,zero_mul,sub_zero,one_re,zero_re,D] using he
  have hbound : 2 ≤ s*D := hillHminusDiscriminant_signed_gap_ge_two q hr n hn x hx
  have hsg : 0 < s*w.re := by
    have hid : (s*D)*(s*w.re) = w.re^2+1 := by
      calc
        _ = s^2*(D*w.re) := by ring
        _ = w.re^2+1 := by rw [hs,one_mul]; linarith [hquad]
    have hp : 0 < (s*D)*(s*w.re) := by rw [hid]; positivity
    exact pos_of_mul_pos_right hp (by linarith)
  have hyr (t : ℝ) : conj (extend y t) = extend y t := by
    exact congrArg (fun f : Curve ℂ => extend f t) (C.physicalPosition_dirichlet_star_real q hq hr x)
  have hmass : (∫ t in (0 : ℝ)..1, extend y t*extend y t) =
      ∫ t in (0 : ℝ)..1, extend y t*conj (extend y t) := by
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [hyr]
  have hnorm := congrArg Complex.re (C.hillHminusDirichlet_derivative_identity q hq x hz)
  change (w*deriv (hillHminusDirichlet q) x).re =
    (∫ t in (0 : ℝ)..1, extend y t*extend y t).re at hnorm
  rw [hmass] at hnorm
  have hn : w.re*d = (∫ t in (0 : ℝ)..1, extend y t*conj (extend y t)).re := by
    simpa only [mul_re,hw,zero_mul,sub_zero,d] using hnorm
  have hp : 0 < (s*d)*(s*w.re) := by
    rw [show (s*d)*(s*w.re) = s^2*(w.re*d) by ring,hs,one_mul,hn]
    exact integral_curve_mul_conj_re_pos y (C.physicalPosition_ne_zero q x (0,1) (by simp))
  exact pos_of_mul_pos_left hp hsg.le

theorem hillHminusDirichlet_zero_unique_in_gap
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ) (hn : 1 ≤ n) (x y : ℝ)
    (hx : x ∈ Icc (hillHminusRealLabels q hr (2*n-1)) (hillHminusRealLabels q hr (2*n)))
    (hy : y ∈ Icc (hillHminusRealLabels q hr (2*n-1)) (hillHminusRealLabels q hr (2*n)))
    (hzx : hillHminusDirichlet q x = 0) (hzy : hillHminusDirichlet q y = 0) : x = y := by
  let s : ℝ := (-1)^n
  have hs : s ≠ 0 := pow_ne_zero _ (by norm_num)
  have ha (t : ℂ) : AnalyticAt ℂ (hillHminusDirichlet q) t :=
    (analyticOnNhd_hillHminusDirichlet_joint (t,q) (mem_univ _)).comp
      (f := fun z : ℂ => (z,q)) (analyticAt_id.prod analyticAt_const)
  have ordered (a b : ℝ) (hab : a ≤ b)
      (hA : a ∈ Icc (hillHminusRealLabels q hr (2*n-1)) (hillHminusRealLabels q hr (2*n)))
      (hB : b ∈ Icc (hillHminusRealLabels q hr (2*n-1)) (hillHminusRealLabels q hr (2*n)))
      (hza : hillHminusDirichlet q a = 0) (hzb : hillHminusDirichlet q b = 0) : a = b := by
    apply eq_of_zero_of_pos_derivative_at_zeros
      (fun t : ℝ => s*(hillHminusDirichlet q t).re)
      (fun t : ℝ => s*(deriv (hillHminusDirichlet q) t).re) a b hab
    · intro t _
      exact ((ha t).differentiableAt.hasDerivAt.real_of_complex).const_mul s
    · intro t ht hz
      have hrt : hillHminusDirichlet q t = 0 := by
        apply Complex.ext _ (hillHminusDirichlet_real q hr t)
        exact (mul_eq_zero.mp hz).resolve_left hs
      exact hillHminusDirichlet_signed_deriv_pos q hr n hn t
        ⟨le_trans hA.1 ht.1,le_trans ht.2 hB.2⟩ hrt
    · simp only [hza,zero_re,mul_zero]
    · simp only [hzb,zero_re,mul_zero]
  rcases le_total x y with hxy | hyx
  · exact ordered x y hxy hx hy hzx hzy
  · exact (ordered y x hyx hy hx hzy hzx).symm

end NLS.KdV
