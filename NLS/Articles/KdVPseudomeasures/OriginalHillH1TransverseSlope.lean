import NLS.Articles.KdVPseudomeasures.OriginalHillH1ModeSymmetry
import NLS.FunctionalAnalysis.HyperplaneDivision

/-! Continuous filled transverse derivatives of the genuine physical KdV
energy. These give the normalized real-mode gradient identity everywhere.
Full frequency/action-gradient identification and collapsed analyticity are
separate obligations. -/
noncomputable section
open Complex Filter Topology NLS.WeightedCoeff NLS.FunctionalAnalysis
namespace NLS.Articles.KdVPseudomeasures

def hillH1RealModeCoordinate (n : ℕ+) :
    RealSignedHilbert (signedStepOrder (1/2) 1) →L[ℝ] ℝ :=
  Complex.reCLM.comp (fourierRealZeroEvalCLM _ 2 (n:ℤ))

theorem hillH1RealModeCoordinate_apply (n : ℕ+)
    (z : RealSignedHilbert (signedStepOrder (1/2) 1)) :
    hillH1RealModeCoordinate n z=(z.val.val.val (n:ℤ)).re := rfl

theorem hillH1RealModeCoordinate_direction (n : ℕ+) :
    hillH1RealModeCoordinate n (hillH1ModeCLM n 1)=1 := by
  rw [hillH1RealModeCoordinate_apply,hillH1ModeCLM_apply]
  have hn : (n:ℤ)≠-(n:ℤ) := by
    have hp : (0:ℤ)<n := by exact_mod_cast n.pos
    omega
  simp [hn]

def hillH1RealModeDerivative (n : ℕ+)
    (z : RealSignedHilbert (signedStepOrder (1/2) 1)) : ℝ :=
  (fderiv ℝ hillH1CanonicalHamiltonian z) (hillH1ModeCLM n 1)

theorem analyticAt_hillH1RealModeDerivative (n : ℕ+)
    (z : RealSignedHilbert (signedStepOrder (1/2) 1)) :
    AnalyticAt ℝ (hillH1RealModeDerivative n) z :=
  @analyticAt_fderiv_apply_const (RealSignedHilbert (signedStepOrder (1/2) 1))
    inferInstance inferInstance hillH1CanonicalHamiltonian (hillH1ModeCLM n 1) z
    (analyticAt_hillH1CanonicalHamiltonian z)

/-- One half of the filled quotient of the actual real-mode energy derivative
by the actual real mode coordinate; no division occurs on its zero set. -/
def hillH1TransverseSlope (n : ℕ+)
    (z : RealSignedHilbert (signedStepOrder (1/2) 1)) : ℝ :=
  (1/2)*@hyperplaneSlope (RealSignedHilbert (signedStepOrder (1/2) 1))
    inferInstance inferInstance (hillH1RealModeDerivative n) (hillH1RealModeCoordinate n) (hillH1ModeCLM n 1) z

theorem continuous_hillH1TransverseSlope (n : ℕ+) : Continuous (hillH1TransverseSlope n) := by
  have hc : Continuous (fderiv ℝ (hillH1RealModeDerivative n)) :=
    @continuous_fderiv_of_analytic (RealSignedHilbert (signedStepOrder (1/2) 1))
      inferInstance inferInstance (hillH1RealModeDerivative n) (analyticAt_hillH1RealModeDerivative n)
  exact continuous_const.mul (@continuous_hyperplaneSlope
    (RealSignedHilbert (signedStepOrder (1/2) 1)) inferInstance inferInstance
    (hillH1RealModeDerivative n) (hillH1RealModeCoordinate n) (hillH1ModeCLM n 1) hc)

theorem hillH1RealModeDerivative_eq_twice_coordinate_slope (n : ℕ+)
    (z : RealSignedHilbert (signedStepOrder (1/2) 1)) :
    hillH1RealModeDerivative n z=2*hillH1RealModeCoordinate n z*hillH1TransverseSlope n z := by
  have hc : Continuous (fderiv ℝ (hillH1RealModeDerivative n)) :=
    @continuous_fderiv_of_analytic (RealSignedHilbert (signedStepOrder (1/2) 1))
      inferInstance inferInstance (hillH1RealModeDerivative n) (analyticAt_hillH1RealModeDerivative n)
  have ht := @mul_hyperplaneSlope (RealSignedHilbert (signedStepOrder (1/2) 1))
    inferInstance inferInstance (hillH1RealModeDerivative n) (hillH1RealModeCoordinate n)
    (hillH1ModeCLM n 1) (hillH1RealModeCoordinate_direction n)
    (fun a => (analyticAt_hillH1RealModeDerivative n a).differentiableAt) hc
    (fun a ha => hillH1CanonicalHamiltonian_fderiv_real_mode_zero a n ha) z
  rw [← ht]
  dsimp only [hillH1TransverseSlope]
  ring

theorem hillH1TransverseSlope_eq_quotient (n : ℕ+)
    (z : RealSignedHilbert (signedStepOrder (1/2) 1)) (hz : hillH1RealModeCoordinate n z≠0) :
    hillH1TransverseSlope n z=hillH1RealModeDerivative n z/(2*hillH1RealModeCoordinate n z) := by
  apply (eq_div_iff (mul_ne_zero (by norm_num) hz)).mpr
  rw [hillH1RealModeDerivative_eq_twice_coordinate_slope]
  ring

theorem analyticAt_hillH1TransverseSlope_of_real_coordinate_ne_zero (n : ℕ+)
    (z : RealSignedHilbert (signedStepOrder (1/2) 1)) (hz : hillH1RealModeCoordinate n z≠0) :
    AnalyticAt ℝ (hillH1TransverseSlope n) z := by
  have hl : AnalyticAt ℝ (hillH1RealModeCoordinate n) z :=
    @ContinuousLinearMap.analyticAt ℝ inferInstance
      (RealSignedHilbert (signedStepOrder (1/2) 1)) inferInstance inferInstance
      ℝ inferInstance inferInstance (hillH1RealModeCoordinate n) z
  have hq := (analyticAt_hillH1RealModeDerivative n z).div
    (analyticAt_const.mul hl) (mul_ne_zero (by norm_num : (2:ℝ)≠0) hz)
  apply hq.congr
  filter_upwards [hl.continuousAt.eventually_ne hz] with a ha
  exact (hillH1TransverseSlope_eq_quotient n a ha).symm

end NLS.Articles.KdVPseudomeasures
