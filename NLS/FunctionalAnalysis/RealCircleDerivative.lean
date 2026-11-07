import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp

/-! Infinitesimal stationarity of a differentiable functional along an
actual complex mode circle, with its literal complex coefficient. -/
noncomputable section
open Complex
namespace NLS.FunctionalAnalysis

def realCirclePhase (t : ℝ) : ℂ := (Real.cos t:ℂ)+(Real.sin t:ℂ)*I

theorem realCirclePhase_mul_conj (t : ℝ) :
    realCirclePhase t*(starRingEnd ℂ) (realCirclePhase t)=1 := by
  apply Complex.ext
  · simpa only [realCirclePhase,Complex.mul_re,Complex.add_re,Complex.add_im,
      Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
      Complex.conj_re,Complex.conj_im,mul_zero,zero_mul,add_zero,zero_add,mul_one,sub_neg_eq_add,
      zero_sub,neg_neg,neg_zero,mul_neg,Complex.one_re,pow_two] using Real.cos_sq_add_sin_sq t
  · simp [realCirclePhase]
    ring

theorem realCirclePhase_zero : realCirclePhase 0=1 := by simp [realCirclePhase]

theorem hasDerivAt_realCirclePhase_zero : HasDerivAt realCirclePhase I 0 := by
  simpa only [realCirclePhase,Real.sin_zero,Real.cos_zero,neg_zero,Complex.ofReal_zero,
    Complex.ofReal_one,zero_add,one_mul] using!
    ((Real.hasDerivAt_cos (0:ℝ)).ofReal_comp.add
      ((Real.hasDerivAt_sin (0:ℝ)).ofReal_comp.mul_const I))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hasDerivAt_differentiable_real_line (f : E → ℝ) (z v : E) (t : ℝ)
    (hf : DifferentiableAt ℝ f (z+t • v)) :
    HasDerivAt (fun r : ℝ => f (z+r • v)) ((fderiv ℝ f (z+t • v)) v) t := by
  have hline : HasDerivAt (fun r : ℝ => z+r • v) v t := by
    simpa only [one_smul,id_eq] using! ((hasDerivAt_id t).smul_const v).const_add z
  exact hf.hasFDerivAt.comp_hasDerivAt t hline

theorem fderiv_circle_tangent_eq_zero (f : E → ℝ) (z : E) (L : ℂ →L[ℝ] E) (c : ℂ)
    (hf : DifferentiableAt ℝ f z)
    (hinv : ∀ t : ℝ, f (z+L ((realCirclePhase t-1)*c))=f z) :
    (fderiv ℝ f z) (L (I*c))=0 := by
  have hphase : HasDerivAt (fun t : ℝ => (realCirclePhase t-1)*c) (I*c) 0 :=
    (hasDerivAt_realCirclePhase_zero.sub_const 1).mul_const c
  have hline : HasDerivAt (fun t : ℝ => z+L ((realCirclePhase t-1)*c)) (L (I*c)) 0 := by
    exact (L.hasFDerivAt.comp_hasDerivAt 0 hphase).const_add z
  have hd : HasDerivAt (fun t : ℝ => f (z+L ((realCirclePhase t-1)*c)))
      ((fderiv ℝ f z) (L (I*c))) 0 :=
    hf.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp [realCirclePhase_zero])
  have he : (fun t : ℝ => f (z+L ((realCirclePhase t-1)*c)))=(fun _ : ℝ => f z) := funext hinv
  rw [he] at hd
  exact hd.unique (hasDerivAt_const (0:ℝ) (f z))

end NLS.FunctionalAnalysis
