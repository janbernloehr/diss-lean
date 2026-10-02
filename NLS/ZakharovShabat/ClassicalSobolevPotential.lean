import NLS.Fourier.SobolevUnitCurve
import NLS.ZakharovShabat.ClassicalFirstBornBound

/-! # Classical potentials constructed from H¹ Fourier coefficients

These are arbitrary physical period-two coefficient pairs. Restriction to
`[0,1]` supplies the potential for the classical ODE, with no extra
absolute-continuity or derivative-integrability assumptions.
-/

noncomputable section
open Set MeasureTheory
open NLS.LinearVolterra NLS.Fourier
namespace NLS.ZakharovShabat

/-- The continuous potential represented by a pair of physical H¹ Fourier series. -/
def classicalSobolevPotential (a : ScalarDomain 2 × ScalarDomain 2) : Curve (ℂ × ℂ) where
  toFun t := (sobolevUnitCurve a.1 t,sobolevUnitCurve a.2 t)
  continuous_toFun := (sobolevUnitCurve a.1).continuous.prodMk (sobolevUnitCurve a.2).continuous

@[simp] theorem extend_classicalSobolevPotential (a : ScalarDomain 2 × ScalarDomain 2) (t : ℝ) :
    extend (classicalSobolevPotential a) t =
      (extend (sobolevUnitCurve a.1) t,extend (sobolevUnitCurve a.2) t) := rfl

/-- The physical supremum norm is controlled uniformly on H¹ balls. -/
theorem norm_classicalSobolevPotential_le (a : ScalarDomain 2 × ScalarDomain 2) :
    ‖classicalSobolevPotential a‖ ≤ 4*‖a‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  apply norm_prod_le_iff.mpr
  constructor
  · exact ((sobolevUnitCurve a.1).norm_coe_le_norm t).trans
      ((norm_sobolevUnitCurve_le a.1).trans (mul_le_mul_of_nonneg_left (norm_fst_le a) (by norm_num)))
  · exact ((sobolevUnitCurve a.2).norm_coe_le_norm t).trans
      ((norm_sobolevUnitCurve_le a.2).trans (mul_le_mul_of_nonneg_left (norm_snd_le a) (by norm_num)))

/-- Both ODE potential components have the regularity needed for integration by parts. -/
theorem classicalSobolevPotential_regular (a : ScalarDomain 2 × ScalarDomain 2) :
    AbsolutelyContinuousOnInterval (fun t => (extend (classicalSobolevPotential a) t).1) 0 1 ∧
    AbsolutelyContinuousOnInterval (fun t => (extend (classicalSobolevPotential a) t).2) 0 1 ∧
    IntervalIntegrable (deriv (fun t => (extend (classicalSobolevPotential a) t).1)) volume 0 1 ∧
    IntervalIntegrable (deriv (fun t => (extend (classicalSobolevPotential a) t).2)) volume 0 1 :=
  ⟨absolutelyContinuous_extend_sobolevUnitCurve a.1,
   absolutelyContinuous_extend_sobolevUnitCurve a.2,
   intervalIntegrable_deriv_extend_sobolevUnitCurve a.1,
   intervalIntegrable_deriv_extend_sobolevUnitCurve a.2⟩

/-- The endpoint/derivative budget is bounded by the H¹ coefficient norm. -/
theorem classicalFirstBornUniformBudget_sobolev_le (a : ScalarDomain 2 × ScalarDomain 2) :
    classicalFirstBornUniformBudget (classicalSobolevPotential a) ≤ (8+2*Real.pi)*‖a‖ := by
  have hfst : (∫ t in (0 : ℝ)..1, ‖deriv (extend (sobolevUnitCurve a.1)) t‖) ≤ 2*Real.pi*‖a‖ :=
    (integral_norm_deriv_extend_sobolevUnitCurve_le a.1).trans
      (mul_le_mul_of_nonneg_left (norm_fst_le a) (by positivity))
  have hsnd : (∫ t in (0 : ℝ)..1, ‖deriv (extend (sobolevUnitCurve a.2)) t‖) ≤ 2*Real.pi*‖a‖ :=
    (integral_norm_deriv_extend_sobolevUnitCurve_le a.2).trans
      (mul_le_mul_of_nonneg_left (norm_snd_le a) (by positivity))
  have hmax := max_le hfst hsnd
  have hnorm := norm_classicalSobolevPotential_le a
  change 2*‖classicalSobolevPotential a‖+
    max (∫ t in (0 : ℝ)..1, ‖deriv (extend (sobolevUnitCurve a.1)) t‖)
      (∫ t in (0 : ℝ)..1, ‖deriv (extend (sobolevUnitCurve a.2)) t‖) ≤ _
  nlinarith

end NLS.ZakharovShabat
