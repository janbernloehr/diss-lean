import NLS.FunctionalAnalysis.LinearVolterra

/-!
# Classical solutions of continuous linear differential equations

The Volterra fixed point gives a differentiable solution on the whole unit
interval, with arbitrary coefficient size. Uniqueness only requires continuity
at the endpoints and the differential equation in the interior.
-/

noncomputable section
open Set MeasureTheory intervalIntegral
namespace NLS.LinearVolterra
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The uniquely determined continuous Volterra solution. -/
def solutionCurve (A : Curve (E →L[ℝ] E)) (x : E) : Curve E :=
  (existsUnique_solution A x).choose

theorem solutionCurve_eq (A : Curve (E →L[ℝ] E)) (x : E) (t : Icc (0 : ℝ) 1) :
    solutionCurve A x t = x + ∫ s in (0 : ℝ)..t.val, integrand A (solutionCurve A x) s :=
  (existsUnique_solution A x).choose_spec.1 t

/-- A differentiable extension of the solution, obtained by integrating its continuous integrand. -/
def solution (A : Curve (E →L[ℝ] E)) (x : E) (t : ℝ) : E :=
  x + ∫ s in (0 : ℝ)..t, integrand A (solutionCurve A x) s

theorem solution_coe (A : Curve (E →L[ℝ] E)) (x : E) (t : Icc (0 : ℝ) 1) :
    solution A x t = solutionCurve A x t := (solutionCurve_eq A x t).symm

@[simp] theorem solution_zero (A : Curve (E →L[ℝ] E)) (x : E) : solution A x 0 = x := by
  simp [solution]

theorem hasDerivAt_solution (A : Curve (E →L[ℝ] E)) (x : E) (t : ℝ) :
    HasDerivAt (solution A x) (integrand A (solutionCurve A x) t) t := by
  have hc := continuous_integrand A (solutionCurve A x)
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add x

theorem continuous_solution (A : Curve (E →L[ℝ] E)) (x : E) : Continuous (solution A x) :=
  continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_solution A x t).continuousAt)

/-- The constructed solution satisfies the original coefficient equation at every point of the closed interval. -/
theorem hasDerivAt_solution_coe (A : Curve (E →L[ℝ] E)) (x : E) (t : Icc (0 : ℝ) 1) :
    HasDerivAt (solution A x) (A t (solution A x t)) t := by
  simpa only [integrand,extend_coe,solution_coe] using hasDerivAt_solution A x t

/-- A continuous curve satisfying the ODE in the interior and the initial condition equals the solution. -/
theorem solution_unique (A : Curve (E →L[ℝ] E)) (x : E) (u : ℝ → E)
    (hu : ContinuousOn u (Icc 0 1)) (h0 : u 0 = x)
    (hd : ∀ t : Icc (0 : ℝ) 1, t.val ∈ Ioo (0 : ℝ) 1 → HasDerivAt u (A t (u t)) t) :
    EqOn u (solution A x) (Icc 0 1) := by
  let v : Curve E := ⟨fun t => u t,hu.comp_continuous continuous_subtype_val (fun t => t.property)⟩
  have hv (t : Icc (0 : ℝ) 1) : v t = x + ∫ s in (0 : ℝ)..t.val, integrand A v s := by
    have hi : ∫ s in (0 : ℝ)..t.val, integrand A v s = u t-u 0 := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le t.property.1
      · exact hu.mono (Icc_subset_Icc le_rfl t.property.2)
      · intro s hs
        have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le,hs.2.le.trans t.property.2⟩
        simpa only [integrand,extend,projIcc_of_mem _ hs',v,ContinuousMap.coe_mk] using
          hd ⟨s,hs'⟩ ⟨hs.1,hs.2.trans_le t.property.2⟩
      · exact (continuous_integrand A v).intervalIntegrable _ _
    rw [hi,h0]
    change u t = x + (u t-x)
    abel
  have he : v = solutionCurve A x := (existsUnique_solution A x).unique hv (solutionCurve_eq A x)
  intro t ht
  have he' := congrArg (fun v : Curve E => v ⟨t,ht⟩) he
  simpa only [v,ContinuousMap.coe_mk,← solution_coe] using he'

end NLS.LinearVolterra
