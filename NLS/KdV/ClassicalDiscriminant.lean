import NLS.KdV.ClassicalSpectralSymmetry
import NLS.ZakharovShabat.ClassicalMonodromyAnalytic
import NLS.ComplexAnalysis.EntireEvenSquareDescent

/-! # The classical Hill discriminant as an entire energy function

The discriminant is defined from the actual normalized scalar solutions,
using the proved constant-upper bridge. Its value is independent of the
square-root choice. Analytic descent treats the ramification point zero.
This does not identify the rough Fourier Hill spectrum or label its gaps.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ZakharovShabat
namespace NLS.KdV

/-- Linear part of the constant-upper potential map, in the Banach curve norm. -/
def constantUpperLinearPotential :
    NLS.LinearVolterra.Curve ℂ →L[ℂ] NLS.LinearVolterra.Curve (ℂ × ℂ) :=
  ContinuousLinearMap.compLeftContinuous ℂ (Icc (0 : ℝ) 1)
    ((0 : ℂ →L[ℂ] ℂ).prod (-ContinuousLinearMap.id ℂ ℂ))

/-- The affine part is a fixed continuous potential. -/
def constantUpperOrigin : NLS.LinearVolterra.Curve (ℂ × ℂ) :=
  ContinuousMap.const _ (-1,0)

theorem constantUpperPotential_eq_affine (q : NLS.LinearVolterra.Curve ℂ) :
    constantUpperPotential q = constantUpperOrigin + constantUpperLinearPotential q := by
  apply ContinuousMap.ext
  intro t
  simp [constantUpperPotential, constantUpperOrigin, constantUpperLinearPotential,
    ContinuousLinearMap.compLeftContinuous]

/-- The actual source-potential embedding is analytic in the sup Banach norm. -/
theorem analyticOnNhd_constantUpperPotential :
    AnalyticOnNhd ℂ constantUpperPotential univ := by
  intro q _
  have he : constantUpperPotential =
      fun p => constantUpperOrigin + constantUpperLinearPotential p :=
    funext constantUpperPotential_eq_affine
  rw [he]
  exact analyticAt_const.add (constantUpperLinearPotential.analyticAt q)

/-- The square-root coordinate trace is jointly analytic in spectral
parameter and continuous potential, as an actual IVP trace. -/
theorem analyticOnNhd_constantUpperTrace_joint :
    AnalyticOnNhd ℂ (fun p : ℂ × NLS.LinearVolterra.Curve ℂ =>
      classicalDiscriminant (constantUpperPotential p.2) p.1) univ := by
  intro p _
  have hp : AnalyticAt ℂ (fun x : ℂ × NLS.LinearVolterra.Curve ℂ =>
      (x.1, constantUpperPotential x.2)) p := by
    exact analyticAt_fst.prod
      ((analyticOnNhd_constantUpperPotential p.2 (mem_univ _)).comp
        (f := fun x : ℂ × NLS.LinearVolterra.Curve ℂ => x.2) analyticAt_snd)
  exact (analyticOnNhd_classicalDiscriminant_joint
    (p.1,constantUpperPotential p.2) (mem_univ _)).comp
      (f := fun x : ℂ × NLS.LinearVolterra.Curve ℂ =>
        (x.1, constantUpperPotential x.2)) hp

/-- The chosen square root is used only to define a total representative;
the value is proved independent of that choice. -/
def classicalHillDiscriminant (q : NLS.LinearVolterra.Curve ℂ) (lambda : ℂ) : ℂ :=
  classicalDiscriminant (constantUpperPotential q) (Complex.sqrt lambda)

/-- Every root of the energy gives the same actual scalar discriminant. -/
theorem classicalHillDiscriminant_eq_of_sq (q : NLS.LinearVolterra.Curve ℂ)
    (lambda z : ℂ) (hz : z^2 = lambda) :
    classicalHillDiscriminant q lambda = classicalDiscriminant (constantUpperPotential q) z := by
  exact classicalDiscriminant_constantUpper_eq_of_sq_eq q _ z ((ComplexAnalysis.complex_sqrt_sq lambda).trans hz.symm)

@[simp] theorem classicalHillDiscriminant_sq (q : NLS.LinearVolterra.Curve ℂ) (z : ℂ) :
    classicalHillDiscriminant q (z^2) = classicalDiscriminant (constantUpperPotential q) z :=
  classicalHillDiscriminant_eq_of_sq q (z^2) z rfl

/-- Joint analyticity in the actual energy and continuous potential,
including the ramification point of the square-root coordinate. -/
theorem analyticOnNhd_classicalHillDiscriminant_joint :
    AnalyticOnNhd ℂ (fun p : ℂ × NLS.LinearVolterra.Curve ℂ =>
      classicalHillDiscriminant p.2 p.1) univ := by
  exact ComplexAnalysis.analyticOnNhd_entire_even_square_descent
    (fun p : ℂ × NLS.LinearVolterra.Curve ℂ => classicalDiscriminant (constantUpperPotential p.2) p.1)
    analyticOnNhd_constantUpperTrace_joint
    (fun q z => classicalDiscriminant_constantUpper_even q z)
    Complex.sqrt ComplexAnalysis.complex_sqrt_sq

/-- The discriminant is entire in energy, including at lambda=0. -/
theorem analyticOnNhd_classicalHillDiscriminant (q : NLS.LinearVolterra.Curve ℂ) :
    AnalyticOnNhd ℂ (classicalHillDiscriminant q) univ := by
  intro lambda _
  exact (analyticOnNhd_classicalHillDiscriminant_joint (lambda,q) (mem_univ _)).comp
    (f := fun z : ℂ => (z,q)) (analyticAt_id.prod analyticAt_const)

/-- The total energy discriminant is the trace of actual scalar Hill
solutions with initial data (1,0) and (0,1), for every energy. -/
theorem classicalHillDiscriminant_eq_scalar_trace (q : NLS.LinearVolterra.Curve ℂ)
    (lambda z : ℂ) (hz : z^2 = lambda) :
    classicalHillDiscriminant q lambda = constantUpperHillTrace q z := by
  rw [constantUpperHillTrace_eq_discriminant]
  exact classicalHillDiscriminant_eq_of_sq q lambda z hz

end NLS.KdV
