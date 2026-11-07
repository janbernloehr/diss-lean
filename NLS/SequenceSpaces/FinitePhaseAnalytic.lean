import NLS.SequenceSpaces.PhaseRotation
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Full native analyticity of finite-support phase trajectories -/
noncomputable section
set_option autoImplicit false
open Complex
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1≤p)]

theorem analyticAt_phaseFlow_of_finite_support
    (ω : ℤ → ℝ) (S : Finset ℤ) (a : Coeff p) (ha : ∀ n∉S, a n=0) (t : ℝ) :
    AnalyticAt ℝ (fun u : ℝ => phaseFlow ω u a) t := by
  have hsum : (fun u : ℝ => ∑ n∈S, lp.single p n (Complex.exp (((u*ω n : ℝ) : ℂ)*I)*a n))=
      fun u : ℝ => phaseFlow ω u a := by
    funext u
    ext j
    change (lp.evalₗ (𝕜 := ℂ) (fun _ : ℤ => ℂ) p j)
      (∑ n∈S, lp.single p n (Complex.exp (((u*ω n : ℝ) : ℂ)*I)*a n))=_
    rw [map_sum]
    by_cases hj : j∈S
    · simp [lp.evalₗ_apply,lp.single_apply,Pi.single_apply,phaseFlow_apply,hj]
    · simp [lp.evalₗ_apply,lp.single_apply,Pi.single_apply,phaseFlow_apply,hj,ha j hj]
  rw [←hsum]
  apply Finset.analyticAt_fun_sum S
  intro n _
  have hlin : AnalyticAt ℝ (fun u : ℝ => ((u*ω n : ℝ) : ℂ)*I) t :=
    by
      let K : ℝ →L[ℝ] ℂ := ((ω n : ℂ)*I) • Complex.ofRealCLM
      have hK : (fun u : ℝ => ((u*ω n : ℝ) : ℂ)*I)=K := by
        funext u
        change ((u*ω n : ℝ) : ℂ)*I=((ω n : ℂ)*I)*(u : ℂ)
        rw [ofReal_mul]
        ring
      rw [hK]
      exact K.analyticAt t
  have he : AnalyticAt ℝ (fun u : ℝ => Complex.exp (((u*ω n : ℝ) : ℂ)*I)) t :=
    (analyticAt_cexp.restrictScalars (𝕜 := ℝ)).comp hlin
  exact ((lp.singleContinuousLinearMap ℝ (fun _ : ℤ => ℂ) p n).analyticAt _).comp (he.mul (analyticAt_const (v := a n)))

end NLS.Coeff
