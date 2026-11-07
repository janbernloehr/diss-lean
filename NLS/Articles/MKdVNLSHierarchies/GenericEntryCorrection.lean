import NLS.ZakharovShabat.ClassicalTriangularPotential
import NLS.ZakharovShabat.ClassicalComponentSwap

/-! # The generic-monodromy-entry argument needs a reality restriction

A nonzero smooth periodic complex potential can have its upper-right
monodromy entry identically zero as a function of the spectral parameter.
The direct adjugate spatial-gradient proof avoids this division entirely.
-/
noncomputable section
open Set Complex NLS.LinearVolterra NLS.ZakharovShabat NLS.Fourier
namespace NLS.Articles.MKdVNLSHierarchies

def lowerTriangularPotential : Curve (ℂ × ℂ) := ContinuousMap.const _ (0,1)

theorem lowerTriangular_second_column (z : ℂ) (t : Icc (0:ℝ) 1) :
    classicalSolution lowerTriangularPotential z (0,1) t = (0,exp (I*z*t.val)) := by
  have h := classicalSolution_unique lowerTriangularPotential z (0,1)
    (fun x : ℝ => (0,exp (I*z*x))) (by fun_prop) (by simp) (by
      intro x _
      have he : HasDerivAt (fun r : ℝ => exp (I*z*r)) (exp (I*z*x.val)*(I*z)) x.val := by
        simpa using (Complex.ofRealCLM.hasDerivAt.const_mul (I*z)).cexp
      convert! (hasDerivAt_const x.val (0:ℂ)).prodMk he using 1
      simp only [classicalODECoefficient_apply,lowerTriangularPotential,ContinuousMap.const_apply]
      apply Prod.ext <;> dsimp <;> ring)
  exact (h t.property).symm

theorem lowerTriangular_upper_entry_identically_zero (z : ℂ) :
    classicalMonodromy lowerTriangularPotential z 0 1 = 0 := by
  have h := congrArg Prod.fst (lowerTriangular_second_column z ⟨1,by norm_num⟩)
  exact h

theorem printed_generic_entry_criterion_false :
    ∃ ab : ScalarDomain 2 × ScalarDomain 2,
      classicalSobolevPotential ab ≠ 0 ∧
      ∀ z : ℂ, classicalMonodromy (classicalSobolevPotential ab) z 0 1 = 0 := by
  have he : classicalSobolevPotential ((0,scalarMode 0 1) : ScalarDomain 2 × ScalarDomain 2) =
      lowerTriangularPotential := by
    ext t <;> simp [classicalSobolevPotential,sobolevUnitCurve,lowerTriangularPotential]
  refine ⟨(0,scalarMode 0 1),?_,?_⟩
  · rw [he]
    intro h
    have hc := congrArg (fun Φ : Curve (ℂ × ℂ) => (Φ ⟨0,by norm_num⟩).2) h
    norm_num [lowerTriangularPotential] at hc
  · rw [he]
    exact lowerTriangular_upper_entry_identically_zero

end NLS.Articles.MKdVNLSHierarchies
