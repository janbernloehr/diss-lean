import NLS.ZakharovShabat.EndpointGradientPolynomial
import NLS.ZakharovShabat.ClassicalShiftedFreeRemainder

/-! # The actual endpoint-gradient error and its free reference

The reference is the same variation-of-constants expression evaluated
on the free columns. Thus the difference is the error in the actual
potential derivative, including the terminal-column contribution.
-/

noncomputable section
open Set Complex NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- The five solution values entering the endpoint gradient. -/
def classicalEndpointGradientData (φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ)
    (s : ℝ) : Fin 5 → ℂ × ℂ :=
  ![classicalSolution φ z (1,0) s,classicalSolution φ z (0,1) s,
    classicalSolution φ z v s,classicalSolution φ z (1,0) 1,classicalSolution φ z (0,1) 1]

/-- The free reference for all five solution values. -/
def classicalFreeEndpointGradientData (z : ℂ) (v : ℂ × ℂ) (s : ℝ) : Fin 5 → ℂ × ℂ :=
  ![classicalFreeVector z (1,0) s,classicalFreeVector z (0,1) s,
    classicalFreeVector z v s,classicalFreeVector z (1,0) 1,classicalFreeVector z (0,1) 1]

/-- The free physical potential gradient of a linear endpoint functional. -/
def classicalFreeEndpointGradient (z : ℂ) (v : ℂ × ℂ) (L : (ℂ × ℂ) →L[ℂ] ℂ) (s : ℝ) : ℂ × ℂ :=
  endpointGradientPolynomial L (classicalFreeEndpointGradientData z v s)

theorem classicalEndpointGradient_eq_polynomial (φ : Curve (ℂ × ℂ)) (z : ℂ)
    (v : ℂ × ℂ) (L : (ℂ × ℂ) →L[ℂ] ℂ) (s : ℝ) :
    classicalEndpointGradient φ z v L s = endpointGradientPolynomial L (classicalEndpointGradientData φ z v s) := rfl

/-- At zero potential the reference agrees with the actual potential gradient. -/
theorem classicalEndpointGradient_free (z : ℂ) (v : ℂ × ℂ)
    (L : (ℂ × ℂ) →L[ℂ] ℂ) (s : Icc (0 : ℝ) 1) :
    classicalEndpointGradient 0 z v L s = classicalFreeEndpointGradient z v L s := by
  have he (u : ℂ × ℂ) (t : Icc (0 : ℝ) 1) : classicalSolution 0 z u t = classicalFreeVector z u t := by
    simp [classicalSolution_free,classicalFreeVector]
  rw [classicalEndpointGradient_eq_polynomial]
  unfold classicalFreeEndpointGradient
  congr 1
  funext i
  fin_cases i <;> simp only [classicalEndpointGradientData,classicalFreeEndpointGradientData]
  all_goals first | exact he _ s | exact he _ ⟨1,by constructor <;> norm_num⟩

/-- Difference from the free potential gradient at an arbitrary reference frequency. -/
def classicalEndpointGradientRemainder (φ : Curve (ℂ × ℂ)) (z w : ℂ) (v : ℂ × ℂ)
    (L : (ℂ × ℂ) →L[ℂ] ℂ) (s : ℝ) : ℂ × ℂ :=
  classicalEndpointGradient φ z v L s-classicalFreeEndpointGradient w v L s

theorem contDiff_classicalEndpointGradient (φ : Curve (ℂ × ℂ)) (z : ℂ)
    (v : ℂ × ℂ) (L : (ℂ × ℂ) →L[ℂ] ℂ) : ContDiff ℝ 1 (classicalEndpointGradient φ z v L) := by
  have ha := contDiff_classicalSolution φ z (1,0)
  have hb := contDiff_classicalSolution φ z (0,1)
  have hu := contDiff_classicalSolution φ z v
  unfold classicalEndpointGradient
  fun_prop

theorem contDiff_classicalFreeEndpointGradient (z : ℂ) (v : ℂ × ℂ) (L : (ℂ × ℂ) →L[ℂ] ℂ) :
    ContDiff ℝ 1 (classicalFreeEndpointGradient z v L) := by
  have hc : ContDiff ℝ 1 (fun t : ℝ => (t : ℂ)) := Complex.ofRealCLM.contDiff
  have ha := contDiff_classicalFreeVector z (1,0)
  have hb := contDiff_classicalFreeVector z (0,1)
  have hu := contDiff_classicalFreeVector z v
  change ContDiff ℝ 1 (fun s =>
    (I*(L (classicalFreeVector z (1,0) 1)*(classicalFreeVector z (0,1) s).2-
        L (classicalFreeVector z (0,1) 1)*(classicalFreeVector z (1,0) s).2)*(classicalFreeVector z v s).2,
     I*(L (classicalFreeVector z (1,0) 1)*(classicalFreeVector z (0,1) s).1-
        L (classicalFreeVector z (0,1) 1)*(classicalFreeVector z (1,0) s).1)*(classicalFreeVector z v s).1))
  fun_prop

theorem contDiff_classicalEndpointGradientRemainder (φ : Curve (ℂ × ℂ)) (z w : ℂ)
    (v : ℂ × ℂ) (L : (ℂ × ℂ) →L[ℂ] ℂ) :
    ContDiff ℝ 1 (classicalEndpointGradientRemainder φ z w v L) :=
  (contDiff_classicalEndpointGradient φ z v L).sub (contDiff_classicalFreeEndpointGradient w v L)

end NLS.ZakharovShabat
