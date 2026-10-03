import NLS.ZakharovShabat.ClassicalSobolevPotential
import NLS.ZakharovShabat.ClassicalFreeDiscriminant

/-! # A constant triangular physical potential

The potential `(1,0)` is represented by a single physical H¹ Fourier mode.
Its upper off-diagonal monodromy entry is nonzero at every nonreal frequency.
-/

noncomputable section
open Set Complex NLS.LinearVolterra NLS.Fourier
namespace NLS.ZakharovShabat

/-- A smooth periodic potential with only the upper coupling present. -/
def classicalTriangularPotential : Curve (ℂ × ℂ) := ContinuousMap.const _ (1,0)

/-- Its explicit physical H¹ coefficient pair. -/
def triangularSobolevCoefficients : ScalarDomain 2 × ScalarDomain 2 := (scalarMode 0 1,0)

@[simp] theorem classicalSobolevPotential_triangular :
    classicalSobolevPotential triangularSobolevCoefficients = classicalTriangularPotential := by
  ext t <;> simp [classicalSobolevPotential,triangularSobolevCoefficients,sobolevUnitCurve,
    classicalTriangularPotential]

/-- The second normalized column of the triangular system. -/
theorem classicalSolution_triangular_second (z : ℂ) (hz : z ≠ 0) (t : Icc (0 : ℝ) 1) :
    classicalSolution classicalTriangularPotential z (0,1) t =
      ((exp (I*z*t.val)-exp (-I*z*t.val))/(2*z),exp (I*z*t.val)) := by
  have h := classicalSolution_unique classicalTriangularPotential z (0,1)
    (fun s : ℝ => ((exp (I*z*s)-exp (-I*z*s))/(2*z),exp (I*z*s)))
    (by fun_prop) (by simp) (by
      intro s _
      have he (c : ℂ) : HasDerivAt (fun t : ℝ => exp (c*t)) (exp (c*s.val)*c) s.val := by
        simpa using (Complex.ofRealCLM.hasDerivAt.const_mul c).cexp
      have hd := (((he (I*z)).sub (he (-I*z))).div_const (2*z)).prodMk (he (I*z))
      convert! hd using 1
      simp only [classicalODECoefficient_apply,classicalTriangularPotential,ContinuousMap.const_apply]
      apply Prod.ext <;> dsimp <;> field_simp [hz] <;> ring)
  exact (h t.property).symm

/-- A nonreal frequency cannot cancel the triangular monodromy coupling. -/
theorem classicalTriangularMonodromy_upper_ne_zero (z : ℂ) (hz : z.im ≠ 0) :
    (classicalSolution classicalTriangularPotential z (0,1) 1).1 ≠ 0 := by
  have hz0 : z ≠ 0 := fun h => hz (by simp [h])
  have he := classicalSolution_triangular_second z hz0 ⟨1,by constructor <;> norm_num⟩
  rw [he]
  simp only [Complex.ofReal_one,mul_one]
  apply div_ne_zero _ (mul_ne_zero (by norm_num) hz0)
  intro h
  have hn := (Complex.norm_exp_eq_iff_re_eq).mp (congrArg norm (sub_eq_zero.mp h))
  simp only [mul_re,neg_re,I_re,I_im,zero_mul,one_mul,neg_mul] at hn
  apply hz
  linarith

end NLS.ZakharovShabat
