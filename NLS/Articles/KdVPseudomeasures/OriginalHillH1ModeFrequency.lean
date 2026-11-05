import NLS.Articles.KdVPseudomeasures.OriginalHillH1CircleStationarity
import NLS.FunctionalAnalysis.ContinuousCoordinateCancellation

/-! The actual physical canonical H1 energy has one normalized frequency
in each native mode, including collapsed modes. It is continuous everywhere
and real analytic at every point where the selected mode is nonzero.
Analyticity at collapsed modes and rough extension remain separate tasks. -/
noncomputable section
open Complex Filter Topology NLS.WeightedCoeff NLS.FunctionalAnalysis
namespace NLS.Articles.KdVPseudomeasures

def hillH1ImagModeCoordinate (n : ℕ+) :
    RealSignedHilbert (signedStepOrder (1/2) 1) →L[ℝ] ℝ :=
  Complex.imCLM.comp (fourierRealZeroEvalCLM _ 2 (n:ℤ))

theorem hillH1ImagModeCoordinate_apply (n : ℕ+)
    (z : RealSignedHilbert (signedStepOrder (1/2) 1)) :
    hillH1ImagModeCoordinate n z=(z.val.val.val (n:ℤ)).im := rfl

def hillH1ImagModeDerivative (n : ℕ+)
    (z : RealSignedHilbert (signedStepOrder (1/2) 1)) : ℝ :=
  (fderiv ℝ hillH1CanonicalHamiltonian z) (hillH1ModeCLM n I)

theorem analyticAt_hillH1ImagModeDerivative (n : ℕ+)
    (z : RealSignedHilbert (signedStepOrder (1/2) 1)) :
    AnalyticAt ℝ (hillH1ImagModeDerivative n) z :=
  @analyticAt_fderiv_apply_const (RealSignedHilbert (signedStepOrder (1/2) 1))
    inferInstance inferInstance hillH1CanonicalHamiltonian (hillH1ModeCLM n I) z
    (analyticAt_hillH1CanonicalHamiltonian z)

/-- The SAME filled scalar gives the imaginary gradient, even at x=0. -/
theorem hillH1ImagModeDerivative_eq_twice_coordinate_slope (n : ℕ+)
    (z : RealSignedHilbert (signedStepOrder (1/2) 1)) :
    hillH1ImagModeDerivative n z=2*hillH1ImagModeCoordinate n z*hillH1TransverseSlope n z := by
  let f := fun a : RealSignedHilbert (signedStepOrder (1/2) 1) =>
    hillH1ImagModeDerivative n a-2*hillH1ImagModeCoordinate n a*hillH1TransverseSlope n a
  have hc : Continuous f :=
    (continuous_iff_continuousAt.mpr (fun a => (analyticAt_hillH1ImagModeDerivative n a).continuousAt)).sub
      ((continuous_const.mul (hillH1ImagModeCoordinate n).continuous).mul (continuous_hillH1TransverseSlope n))
  have he (a : RealSignedHilbert (signedStepOrder (1/2) 1)) : hillH1RealModeCoordinate n a*f a=0 := by
    have hr := hillH1CanonicalHamiltonian_radial_gradient_relation a n
    change hillH1RealModeCoordinate n a*hillH1ImagModeDerivative n a=
      hillH1ImagModeCoordinate n a*hillH1RealModeDerivative n a at hr
    rw [hillH1RealModeDerivative_eq_twice_coordinate_slope] at hr
    dsimp only [f]
    nlinarith only [hr]
  have hz := @continuous_eq_zero_of_coordinate_mul (RealSignedHilbert (signedStepOrder (1/2) 1))
    inferInstance inferInstance f (hillH1RealModeCoordinate n) (hillH1ModeCLM n 1)
    (hillH1RealModeCoordinate_direction n) hc he z
  exact sub_eq_zero.mp hz

/-- Frequency is the derivative of the genuine energy with respect to
the native action z_n*z_-n=x_n^2+y_n^2. -/
def hillH1KdVFrequency (n : ℕ+)
    (z : RealSignedHilbert (signedStepOrder (1/2) 1)) : ℝ := hillH1TransverseSlope n z

theorem continuous_hillH1KdVFrequency (n : ℕ+) : Continuous (hillH1KdVFrequency n) :=
  continuous_hillH1TransverseSlope n

/-- The FULL actual energy differential on an arbitrary supported mode
direction equals frequency times the literal native action differential. -/
theorem hillH1CanonicalHamiltonian_mode_gradient (n : ℕ+)
    (z : RealSignedHilbert (signedStepOrder (1/2) 1)) (c : ℂ) :
    (fderiv ℝ hillH1CanonicalHamiltonian z) (hillH1ModeCLM n c)=
      hillH1KdVFrequency n z*(2*((starRingEnd ℂ) (z.val.val.val (n:ℤ))*c).re) := by
  have he : c=c.re • (1:ℂ)+c.im • I := by
    simpa only [Complex.real_smul,Complex.ofReal_mul,mul_one] using (Complex.re_add_im c).symm
  calc
    _ = c.re*hillH1RealModeDerivative n z+c.im*hillH1ImagModeDerivative n z := by
      conv_lhs => rw [he]
      rw [map_add,map_smul,map_smul,map_add,map_smul,map_smul]
      rfl
    _ = _ := by
      rw [hillH1RealModeDerivative_eq_twice_coordinate_slope,
        hillH1ImagModeDerivative_eq_twice_coordinate_slope]
      simp only [hillH1KdVFrequency,hillH1RealModeCoordinate_apply,hillH1ImagModeCoordinate_apply,
        Complex.mul_re,Complex.conj_re,Complex.conj_im]
      ring

theorem hillH1KdVFrequency_eq_imag_quotient (n : ℕ+)
    (z : RealSignedHilbert (signedStepOrder (1/2) 1)) (hz : hillH1ImagModeCoordinate n z≠0) :
    hillH1KdVFrequency n z=hillH1ImagModeDerivative n z/(2*hillH1ImagModeCoordinate n z) := by
  apply (eq_div_iff (mul_ne_zero (by norm_num) hz)).mpr
  rw [hillH1ImagModeDerivative_eq_twice_coordinate_slope]
  dsimp only [hillH1KdVFrequency]
  ring

theorem analyticAt_hillH1KdVFrequency_of_imag_coordinate_ne_zero (n : ℕ+)
    (z : RealSignedHilbert (signedStepOrder (1/2) 1)) (hz : hillH1ImagModeCoordinate n z≠0) :
    AnalyticAt ℝ (hillH1KdVFrequency n) z := by
  have hl : AnalyticAt ℝ (hillH1ImagModeCoordinate n) z :=
    @ContinuousLinearMap.analyticAt ℝ inferInstance
      (RealSignedHilbert (signedStepOrder (1/2) 1)) inferInstance inferInstance
      ℝ inferInstance inferInstance (hillH1ImagModeCoordinate n) z
  have hq := (analyticAt_hillH1ImagModeDerivative n z).div
    (analyticAt_const.mul hl) (mul_ne_zero (by norm_num : (2:ℝ)≠0) hz)
  apply hq.congr
  filter_upwards [hl.continuousAt.eventually_ne hz] with a ha
  exact (hillH1KdVFrequency_eq_imag_quotient n a ha).symm

theorem analyticAt_hillH1KdVFrequency_of_mode_ne_zero (n : ℕ+)
    (z : RealSignedHilbert (signedStepOrder (1/2) 1)) (hz : z.val.val.val (n:ℤ)≠0) :
    AnalyticAt ℝ (hillH1KdVFrequency n) z := by
  by_cases hx : hillH1RealModeCoordinate n z=0
  · apply analyticAt_hillH1KdVFrequency_of_imag_coordinate_ne_zero
    intro hy
    apply hz
    apply Complex.ext
    · exact hx
    · exact hy
  · exact analyticAt_hillH1TransverseSlope_of_real_coordinate_ne_zero n z hx

end NLS.Articles.KdVPseudomeasures
