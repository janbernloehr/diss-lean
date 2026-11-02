import NLS.KdV.ClassicalSpectralSymmetry
import NLS.ZakharovShabat.ClassicalMonodromyAnalytic
import NLS.ComplexAnalysis.ParametricEvenSquareDescent

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

private theorem energy_sqrt_sq (a : ℂ) : (Complex.sqrt a)^2 = a := by
  have h := Complex.cpow_nat_inv_pow a (Nat.succ_ne_zero 1)
  norm_num at h
  simpa only [Complex.sqrt, one_div] using h

/-- Every root of the energy gives the same actual scalar discriminant. -/
theorem classicalHillDiscriminant_eq_of_sq (q : NLS.LinearVolterra.Curve ℂ)
    (lambda z : ℂ) (hz : z^2 = lambda) :
    classicalHillDiscriminant q lambda = classicalDiscriminant (constantUpperPotential q) z := by
  exact classicalDiscriminant_constantUpper_eq_of_sq_eq q _ z ((energy_sqrt_sq lambda).trans hz.symm)

@[simp] theorem classicalHillDiscriminant_sq (q : NLS.LinearVolterra.Curve ℂ) (z : ℂ) :
    classicalHillDiscriminant q (z^2) = classicalDiscriminant (constantUpperPotential q) z :=
  classicalHillDiscriminant_eq_of_sq q (z^2) z rfl

/-- Joint analyticity in the actual energy and continuous potential,
including the ramification point of the square-root coordinate. -/
theorem analyticOnNhd_classicalHillDiscriminant_joint :
    AnalyticOnNhd ℂ (fun p : ℂ × NLS.LinearVolterra.Curve ℂ =>
      classicalHillDiscriminant p.2 p.1) univ := by
  intro p _
  let R : ℝ := ‖p.1‖ + 1
  have hR : 0 < R := by dsimp [R]; positivity
  let V : Set (ℂ × NLS.LinearVolterra.Curve ℂ) := ball 0 (R^2) ×ˢ univ
  have hV : IsOpen V := isOpen_ball.prod isOpen_univ
  have hp : p ∈ V := by
    refine ⟨?_, mem_univ _⟩
    simp only [mem_ball, dist_zero_right]
    dsimp [R]
    nlinarith [norm_nonneg p.1]
  let F : ℂ × (ℂ × NLS.LinearVolterra.Curve ℂ) → ℂ :=
    fun x => classicalDiscriminant (constantUpperPotential x.2.2) x.1
  have hF : AnalyticOnNhd ℂ F univ := by
    intro x _
    have hq : AnalyticAt ℂ (fun y : ℂ × (ℂ × NLS.LinearVolterra.Curve ℂ) =>
        y.2.2) x := analyticAt_snd.comp
      (f := fun y : ℂ × (ℂ × NLS.LinearVolterra.Curve ℂ) => y.2) analyticAt_snd
    exact (analyticOnNhd_constantUpperTrace_joint (x.1,x.2.2) (mem_univ _)).comp
      (f := fun y : ℂ × (ℂ × NLS.LinearVolterra.Curve ℂ) => (y.1,y.2.2))
      (analyticAt_fst.prod hq)
  have heven : ∀ a ∈ V, ∀ z ∈ ball (0 : ℂ) R, F (-z,a) = F (z,a) := by
    intro a _ z _
    exact classicalDiscriminant_constantUpper_even a.2 z
  have hd : ∀ a ∈ V, ‖Complex.sqrt a.1‖ < R := by
    intro a ha
    have he : ‖Complex.sqrt a.1‖^2 = ‖a.1‖ := by
      rw [← norm_pow, energy_sqrt_sq]
    have hb : ‖a.1‖ < R^2 := by simpa only [mem_ball, dist_zero_right] using ha.1
    nlinarith [norm_nonneg (Complex.sqrt a.1)]
  have hsq : AnalyticOnNhd ℂ (fun a : ℂ × NLS.LinearVolterra.Curve ℂ =>
      (Complex.sqrt a.1)^2) V := by
    simp only [energy_sqrt_sq]
    exact analyticOnNhd_fst
  exact ComplexAnalysis.analyticOnNhd_evenFamily_of_analytic_square F R hR V hV
    (hF.mono (subset_univ _)) heven (fun a => Complex.sqrt a.1) hd hsq p hp

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
