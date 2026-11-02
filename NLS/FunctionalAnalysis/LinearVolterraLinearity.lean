import NLS.FunctionalAnalysis.LinearVolterraSolution

/-! # Additivity and the zero initial state of the constructed Volterra flow -/

noncomputable section
open Set
namespace NLS.LinearVolterra
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem solution_add (A : Curve (E →L[ℝ] E)) (v w : E) (t : Icc (0 : ℝ) 1) :
    solution A (v+w) t = solution A v t+solution A w t := by
  apply Eq.symm
  apply solution_unique A (v+w) (fun x => solution A v x+solution A w x)
    ((continuous_solution A v).add (continuous_solution A w)).continuousOn
    (by simp only [solution_zero]) _ t.property
  intro s _
  simpa only [map_add, Pi.add_def] using (hasDerivAt_solution_coe A v s).add (hasDerivAt_solution_coe A w s)

theorem solution_zero_initial (A : Curve (E →L[ℝ] E)) (t : Icc (0 : ℝ) 1) :
    solution A 0 t = 0 := by
  have h := solution_add A 0 0 t
  rw [zero_add] at h
  exact add_left_cancel (show solution A 0 t+solution A 0 t = solution A 0 t+0 by simpa using h.symm)

end NLS.LinearVolterra
