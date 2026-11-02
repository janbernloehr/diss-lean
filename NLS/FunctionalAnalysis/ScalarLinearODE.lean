import NLS.FunctionalAnalysis.AutonomousODEUniqueness
import NLS.FunctionalAnalysis.ScalarACVariation

/-! # The complete scalar constant-coefficient equation

An everywhere differentiable complex curve with constant logarithmic
velocity is the literal exponential mode, for every real time.
-/
noncomputable section
open Set Complex
namespace NLS.FunctionalAnalysis

theorem eq_scalarExponential_of_hasDerivAt (α : ℂ) (f : ℝ → ℂ)
    (hf : ∀ t, HasDerivAt f (α*f t) t) (t : ℝ) :
    f t = Complex.exp (α*(t : ℂ))*f 0 := by
  have hd (r : ℝ) : HasDerivAt (fun u : ℝ => Complex.exp (α*(u : ℂ))*f 0)
      (α*(Complex.exp (α*(r : ℂ))*f 0)) r := by
    simpa only [mul_assoc] using (hasDerivAt_scalarExponential α r).mul_const (f 0)
  have he := eqOn_of_autonomous_hasDerivAt isOpen_univ isPreconnected_univ
    (v := fun z : ℂ => α*z)
    (fun r _ => (show ContDiff ℝ 1 (fun z : ℂ => α*z) from contDiff_const.mul contDiff_id).contDiffAt
      (x := Complex.exp (α*(r : ℂ))*f 0))
    (fun r _ => hd r) (fun r _ => hf r) (mem_univ (0 : ℝ))
    (by simp)
  exact (he (mem_univ t)).symm

end NLS.FunctionalAnalysis
