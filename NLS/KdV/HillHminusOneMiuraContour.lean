import NLS.KdV.HillHminusOneMiuraSheets
import NLS.ComplexAnalysis.QuadraticEnergyLoop
import NLS.ComplexAnalysis.PrincipalSquareRootSheet
import NLS.ZakharovShabat.SourceCriticalRootRatioJointAnalytic

/-! # The literal Hill contour after a rough Miura energy change

The transferred root is the original canonical Dirac root at sqrt(E+c).
It squares to the ACTUAL Hill radicand and agrees with the ACTUAL physical
Hill sheet at every nonreal energy for a real shifted Miura image.
The quadratic pullback retains the exact two-z Jacobian.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV

def hillHminusMiuraRoot (u : Coeff 2) (c E : ℂ) : ℂ :=
  sourceCanonicalRoot (by simp) (by norm_num) (hillMiuraDiagonal u) (Complex.sqrt (E+c))

def hillHminusMiuraContourAction (q : PeriodOneHminusOne) (u : Coeff 2) (c : ℂ)
    (Γ : PiecewiseC1Loop) : ℂ :=
  (1/(Real.pi : ℂ))*Γ.integral (fun E => E*deriv (hillHminusDiscriminant q) E/hillHminusMiuraRoot u c E)

theorem hillHminusMiuraRoot_at_squared_energy (u : Coeff 2) (c z : ℂ) (hz : 0 < z.re) :
    hillHminusMiuraRoot u c (z^2-c) = sourceCanonicalRoot (by simp) (by norm_num) (hillMiuraDiagonal u) z := by
  have he : (-I)*Complex.sqrt (z^2) = (-I)*z := classicalHillFreePrimitive_sq_of_re_pos z hz
  have hs : Complex.sqrt (z^2) = z := mul_left_cancel₀ (neg_ne_zero.mpr I_ne_zero) he
  rw [hillHminusMiuraRoot,sub_add_cancel,hs]

theorem hillHminusMiuraRoot_sq
    (q : PeriodOneHminusOne) (u : Coeff 2) (c E : ℂ)
    (himage : periodOneMiura u = q+periodOneL2Inclusion (lp.single 2 0 c))
    (hroot : Complex.sqrt (E+c) ∈ sourceCanonicalRootDomain (by simp) (by norm_num) (hillMiuraDiagonal u)) :
    hillHminusMiuraRoot u c E^2 = hillHminusRadicand q E := by
  rw [hillHminusMiuraRoot,sourceCanonicalRoot_sq_eq_discriminant_sq_sub_four _ _ _ _ hroot]
  have he := hillHminusDiscriminant_shifted_miura_square q u c (Complex.sqrt (E+c)) himage
  rw [complex_sqrt_sq,add_sub_cancel_right] at he
  rw [← he]
  rfl

theorem hillHminusMiuraRoot_eq_physical_of_real
    (u : PeriodOneRealL2) (q : PeriodOneHminusOne) (c : ℝ)
    (himage : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (c : ℂ)))
    (E : ℂ) (hE : E.im ≠ 0) :
    hillHminusMiuraRoot u.val (c : ℂ) E = hillHminusContinuedRoot (E,q) := by
  let z := Complex.sqrt (E+(c : ℂ))
  have hsq : z^2 = E+(c : ℂ) := complex_sqrt_sq _
  have hi : (z^2).im = E.im := by rw [hsq,add_im,ofReal_im,add_zero]
  have hzi : z.im ≠ 0 := by
    intro he
    simp only [pow_two,mul_im,he,mul_zero,zero_mul,add_zero] at hi
    exact hE hi.symm
  have hzr : 0 < z.re := by
    have hnonneg : 0 ≤ z.re := re_sqrt_nonneg _
    have hne : z.re ≠ 0 := by
      intro he
      simp only [pow_two,mul_im,he,mul_zero,zero_mul,add_zero] at hi
      exact hE hi.symm
    exact lt_of_le_of_ne hnonneg hne.symm
  have he := (hillHminus_shifted_miura_sheets u q c himage z hzr hzi).1
  have henergy : z^2-(c : ℂ) = E := by rw [hsq,add_sub_cancel_right]
  rw [henergy] at he
  exact he.symm

theorem hillHminus_shifted_miura_trace_derivative
    (q : PeriodOneHminusOne) (u : Coeff 2) (c z : ℂ)
    (himage : periodOneMiura u = q+periodOneL2Inclusion (lp.single 2 0 c)) :
    deriv (canonicalDiscriminant (by simp) (periodOnePotential (hillMiuraDiagonal u))) z =
      deriv (hillHminusDiscriminant q) (z^2-c)*(2*z) := by
  have hd : AnalyticAt ℂ (hillHminusDiscriminant q) (z^2-c) :=
    (analyticOnNhd_hillHminusDiscriminant_joint (z^2-c,q) (mem_univ _)).comp
      (f := fun w : ℂ => (w,q)) (analyticAt_id.prod analyticAt_const)
  have hT : HasDerivAt (fun w : ℂ => w^2-c) (2*z) z := by
    simpa using ((hasDerivAt_id z).pow 2).sub_const c
  have hc := hd.differentiableAt.hasDerivAt.comp z hT
  have he : (fun w => hillHminusDiscriminant q (w^2-c)) =
      canonicalDiscriminant (by simp) (periodOnePotential (hillMiuraDiagonal u)) :=
    funext (fun w => hillHminusDiscriminant_shifted_miura_square q u c w himage)
  dsimp only [Function.comp_def] at hc
  rw [he] at hc
  exact hc.deriv

theorem hillHminusMiuraContourAction_quadratic_pullback
    (q : PeriodOneHminusOne) (u : Coeff 2) (c : ℂ)
    (himage : periodOneMiura u = q+periodOneL2Inclusion (lp.single 2 0 c))
    (Γ : PiecewiseC1Loop) (hΓ : Γ.Inside {z : ℂ | 0 < z.re}) :
    hillHminusMiuraContourAction q u c (quadraticEnergyLoop Γ c) =
      (1/(Real.pi : ℂ))*Γ.integral (fun z => (z^2-c)*sourceCriticalRootRatioJoint
        (by simp) (by norm_num) (z,hillMiuraDiagonal u)) := by
  unfold hillHminusMiuraContourAction
  congr 1
  apply integral_quadraticEnergyLoop Γ c _ _ _ hΓ
  intro z hz
  rw [hillHminusMiuraRoot_at_squared_energy u c z hz]
  dsimp only [sourceCriticalRootRatioJoint]
  rw [hillHminus_shifted_miura_trace_derivative q u c z himage]
  ring

end NLS.KdV
