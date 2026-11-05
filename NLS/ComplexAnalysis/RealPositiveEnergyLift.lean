import NLS.ComplexAnalysis.QuadraticEnergyPath
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.ComplexAnalysis

/-- The positive real frequency above a real energy, with its actual shift. -/
def positiveRealEnergyLift (c : ℝ) (E : ℂ) : ℂ := (Real.sqrt (E.re+c):ℂ)

theorem continuous_positiveRealEnergyLift (c : ℝ) : Continuous (positiveRealEnergyLift c) := by
  unfold positiveRealEnergyLift
  fun_prop

theorem positiveRealEnergyLift_sq (c : ℝ) (E : ℂ) (hreal : E.im=0)
    (hpos : 0<E.re+c) : (positiveRealEnergyLift c E)^2-(c:ℂ)=E := by
  have hsq : ((Real.sqrt (E.re+c):ℂ)^2)=((E.re+c:ℝ):ℂ) := by
    exact_mod_cast Real.sq_sqrt hpos.le
  unfold positiveRealEnergyLift
  rw [hsq]
  apply Complex.ext <;> simp [hreal]

theorem positiveRealEnergyLift_eq_of_sq (c : ℝ) (E z : ℂ)
    (hreal : z.im=0) (hpos : 0≤z.re) (hE : E=z^2-(c:ℂ)) :
    positiveRealEnergyLift c E=z := by
  apply Complex.ext
  · simp only [positiveRealEnergyLift,ofReal_re,hE,sub_re,pow_two,mul_re,hreal,
      mul_zero,sub_zero]
    rw [sub_add_cancel,Real.sqrt_mul_self hpos]
  · simp [positiveRealEnergyLift,hreal]

theorem positiveRealEnergyLift_re_pos (c : ℝ) (E : ℂ) (hpos : 0<E.re+c) :
    0<(positiveRealEnergyLift c E).re := Real.sqrt_pos.mpr hpos

def positiveRealEnergyLiftPath {a b : ℂ} (c : ℝ) (γ : Path a b) :
    Path (positiveRealEnergyLift c a) (positiveRealEnergyLift c b) :=
  γ.map (continuous_positiveRealEnergyLift c)

theorem contDiffOn_positiveRealEnergyLiftPath {a b : ℂ} (c : ℝ) (γ : Path a b)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hpos : ∀ t∈Icc (0:ℝ) 1, 0<(γ.extend t).re+c) :
    ContDiffOn ℝ 1 (positiveRealEnergyLiftPath c γ).extend (Icc 0 1) := by
  have hr : ContDiffOn ℝ 1 (fun t => (γ.extend t).re+c) (Icc 0 1) :=
    (Complex.reCLM.contDiff.comp_contDiffOn hγ).add contDiffOn_const
  exact Complex.ofRealCLM.contDiff.comp_contDiffOn (hr.sqrt (fun t ht => ne_of_gt (hpos t ht)))

/-- The lifted path squares back to the literal energy path, including
both endpoints; the endpoint cast carries no change of parameter. -/
theorem quadraticEnergyPath_positiveRealEnergyLiftPath {a b : ℂ} (c : ℝ) (γ : Path a b)
    (hreal : ∀ t : unitInterval, (γ t).im=0)
    (hpos : ∀ t : unitInterval, 0<(γ t).re+c) :
    (quadraticEnergyPath (c:ℂ) (positiveRealEnergyLiftPath c γ)).cast
      (positiveRealEnergyLift_sq c a (by simpa using hreal 0) (by simpa using hpos 0)).symm
      (positiveRealEnergyLift_sq c b (by simpa using hreal 1) (by simpa using hpos 1)).symm=γ := by
  ext t
  exact positiveRealEnergyLift_sq c (γ t) (hreal t) (hpos t)

end NLS.ComplexAnalysis
