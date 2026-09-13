import NLS.ZakharovShabat.ClassicalBoundaryDeterminants
import NLS.ZakharovShabat.FreeSpectralProducts
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Free normalization of the classical discriminant

The constructed fundamental solution has the signed free exponentials, and
its monodromy trace agrees exactly with the existing free spectral-product
normalization at every complex spectral parameter.
-/

noncomputable section
open Set Complex Matrix
open NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- The free initial-value solution is given by the two signed exponentials. -/
theorem classicalSolution_free (z : ℂ) (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    classicalSolution 0 z v t = (exp (-I*z*t.val)*v.1,exp (I*z*t.val)*v.2) := by
  have h := classicalSolution_unique 0 z v
    (fun s : ℝ => (exp (-I*z*s)*v.1,exp (I*z*s)*v.2))
    (by fun_prop) (by simp) (by
      intro s _
      have he (c : ℂ) : HasDerivAt (fun t : ℝ => exp (c*t)) (exp (c*s.val)*c) s.val := by
        simpa using (Complex.ofRealCLM.hasDerivAt.const_mul c).cexp
      have hd := ((he (-I*z)).mul_const v.1).prodMk ((he (I*z)).mul_const v.2)
      convert! hd using 1
      simp only [classicalODECoefficient_apply,ContinuousMap.zero_apply,Prod.fst_zero,Prod.snd_zero,mul_zero,zero_mul,add_zero,zero_add]
      apply Prod.ext <;> dsimp <;> ring)
  exact (h t.property).symm

/-- The free fundamental matrix is the diagonal signed exponential matrix. -/
theorem classicalFundamentalMatrix_free (z : ℂ) (t : Icc (0 : ℝ) 1) :
    classicalFundamentalMatrix 0 z t = !![exp (-I*z*t.val),0;0,exp (I*z*t.val)] := by
  simp [classicalFundamentalMatrix,classicalSolution_free]

/-- The classical monodromy trace has exactly the established free normalization. -/
theorem classicalDiscriminant_free (z : ℂ) : classicalDiscriminant 0 z = freeDiscriminant z := by
  have hf := classicalFundamentalMatrix_free z ⟨1,by constructor <;> norm_num⟩
  change (classicalFundamentalMatrix 0 z 1).trace = _
  rw [hf,Matrix.trace_fin_two_of]
  simp only [Complex.ofReal_one,mul_one,freeDiscriminant,Complex.two_cos]
  rw [add_comm]
  congr 1 <;> congr 1 <;> ring

end NLS.ZakharovShabat
