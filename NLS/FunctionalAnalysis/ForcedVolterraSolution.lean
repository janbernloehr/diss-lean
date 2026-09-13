import NLS.FunctionalAnalysis.ComplexVolterraAnalytic
import NLS.FunctionalAnalysis.LinearVolterraRegularity
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Inhomogeneous continuous linear initial-value problems

The inverse Volterra operator solves a continuous source term and arbitrary
initial data. Its real-time representative is continuously differentiable,
and absolutely continuous almost-everywhere solutions satisfy uniqueness.
-/

noncomputable section
open Set Filter MeasureTheory intervalIntegral
namespace NLS.LinearVolterra
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The continuous primitive is a bounded complex-linear operator. -/
def primitive : Curve E →L[ℂ] Curve E := volterra (ContinuousMap.const _ (ContinuousLinearMap.id ℂ E))

@[simp] theorem primitive_apply (g : Curve E) (t : Icc (0 : ℝ) 1) :
    primitive g t = ∫ s in (0 : ℝ)..t.val, extend g s := by
  rw [primitive,volterra_apply]
  rfl

/-- Solve the continuous forced integral equation in the supremum-norm space. -/
def forcedSolutionCurve (A : Curve (E →L[ℂ] E)) (g : Curve E) (x : E) : Curve E :=
  solutionOperator A (ContinuousMap.const _ x+primitive g)

/-- The inverse satisfies the inhomogeneous integral equation. -/
theorem forcedSolutionCurve_eq (A : Curve (E →L[ℂ] E)) (g : Curve E) (x : E)
    (t : Icc (0 : ℝ) 1) :
    forcedSolutionCurve A g x t = x + ∫ s in (0 : ℝ)..t.val,
      (extend A s (extend (forcedSolutionCurve A g x) s)+extend g s) := by
  have h := congrArg (fun L : Curve E →L[ℂ] Curve E => L (ContinuousMap.const _ x+primitive g) t)
    (mul_solutionOperator A)
  simp only [mul_apply_eq_comp,sub_apply,one_apply_eq_self,ContinuousMap.sub_apply,
    ContinuousMap.add_apply,ContinuousMap.const_apply,primitive_apply,volterra_apply] at h
  rw [intervalIntegral.integral_add
    ((show Continuous (fun s => extend A s (extend (forcedSolutionCurve A g x) s)) by unfold extend; fun_prop).intervalIntegrable _ _)
    ((continuous_extend g).intervalIntegrable _ _)]
  change forcedSolutionCurve A g x t = x+(_+_)
  change forcedSolutionCurve A g x t - _ = x+_ at h
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  abel

/-- A real-time representative of the forced initial-value solution. -/
def forcedSolution (A : Curve (E →L[ℂ] E)) (g : Curve E) (x : E) (t : ℝ) : E :=
  x + ∫ s in (0 : ℝ)..t, (extend A s (extend (forcedSolutionCurve A g x) s)+extend g s)

/-- On the closed unit interval the real-time representative is the inverse Volterra curve. -/
theorem forcedSolution_coe (A : Curve (E →L[ℂ] E)) (g : Curve E) (x : E)
    (t : Icc (0 : ℝ) 1) : forcedSolution A g x t = forcedSolutionCurve A g x t :=
  (forcedSolutionCurve_eq A g x t).symm

@[simp] theorem forcedSolution_zero (A : Curve (E →L[ℂ] E)) (g : Curve E) (x : E) :
    forcedSolution A g x 0 = x := by simp [forcedSolution]

/-- The forced solution is differentiable at every real time. -/
theorem hasDerivAt_forcedSolution (A : Curve (E →L[ℂ] E)) (g : Curve E) (x : E) (t : ℝ) :
    HasDerivAt (forcedSolution A g x)
      (extend A t (extend (forcedSolutionCurve A g x) t)+extend g t) t := by
  have hc : Continuous (fun s => extend A s (extend (forcedSolutionCurve A g x) s)+extend g s) := by unfold extend; fun_prop
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    (hc.stronglyMeasurableAtFilter volume (nhds t)) (hc.continuousAt)).const_add x

/-- The actual forced ODE holds at all points of the closed physical interval. -/
theorem hasDerivAt_forcedSolution_coe (A : Curve (E →L[ℂ] E)) (g : Curve E) (x : E)
    (t : Icc (0 : ℝ) 1) :
    HasDerivAt (forcedSolution A g x) (A t (forcedSolution A g x t)+g t) t := by
  simpa only [extend_coe,forcedSolution_coe] using hasDerivAt_forcedSolution A g x t

/-- The real-time forced solution is continuously differentiable. -/
theorem contDiff_forcedSolution (A : Curve (E →L[ℂ] E)) (g : Curve E) (x : E) :
    ContDiff ℝ 1 (forcedSolution A g x) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun t => (hasDerivAt_forcedSolution A g x t).differentiableAt,?_⟩
  have he : deriv (forcedSolution A g x) = fun t =>
      extend A t (extend (forcedSolutionCurve A g x) t)+extend g t := by
    funext t
    exact (hasDerivAt_forcedSolution A g x t).deriv
  rw [he]
  unfold extend
  fun_prop

/-- Absolutely continuous almost-everywhere solutions of the forced ODE agree with the inverse construction. -/
theorem forcedSolution_unique_of_ac (A : Curve (E →L[ℂ] E)) (g : Curve E) (u : ℝ → E)
    (hu : AbsolutelyContinuousOnInterval u 0 1)
    (hd : ∀ᵐ s : ℝ, s ∈ Icc (0 : ℝ) 1 → HasDerivAt u (extend A s (u s)+extend g s) s) :
    EqOn u (forcedSolution A g (u 0)) (Icc 0 1) := by
  have hc : ContinuousOn u (Icc 0 1) := by simpa using hu.continuousOn
  let v : Curve E := ⟨fun t => u t,hc.comp_continuous continuous_subtype_val (fun t => t.property)⟩
  have hv (t : Icc (0 : ℝ) 1) : v t = u 0 + ∫ s in (0 : ℝ)..t.val,
      (extend A s (extend v s)+extend g s) := by
    have hs : uIcc 0 t.val ⊆ Icc (0 : ℝ) 1 := by
      rw [uIcc_of_le t.property.1]
      exact Icc_subset_Icc le_rfl t.property.2
    have hcont : Continuous (fun s => extend A s (extend v s)+extend g s) := by unfold extend; fun_prop
    have hi := NLS.FunctionalAnalysis.integral_eq_sub_of_ac_of_ae_hasDerivAt
      (hu.mono (by simpa using hs)) (hcont.intervalIntegrable 0 t.val) (by
        filter_upwards [hd] with s hds
        intro hst
        have hs' := hs hst
        simpa only [extend,projIcc_of_mem _ hs',v,ContinuousMap.coe_mk] using hds hs')
    rw [hi]
    change u t = u 0+(u t-u 0)
    abel
  have hV : (1-volterra A) v = ContinuousMap.const _ (u 0)+primitive g := by
    ext t
    simp only [sub_apply,one_apply_eq_self,ContinuousMap.sub_apply,volterra_apply,
      ContinuousMap.add_apply,ContinuousMap.const_apply,primitive_apply]
    rw [hv t,intervalIntegral.integral_add
      ((show Continuous (fun s => extend A s (extend v s)) by unfold extend; fun_prop).intervalIntegrable _ _)
      ((continuous_extend g).intervalIntegrable _ _)]
    abel
  have he : v = forcedSolutionCurve A g (u 0) := by
    have h := congrArg (fun w => solutionOperator A w) hV
    rw [← mul_apply_eq_comp,solutionOperator_mul,one_apply_eq_self] at h
    exact h
  intro t ht
  have h := congrArg (fun w : Curve E => w ⟨t,ht⟩) he
  simpa only [v,ContinuousMap.coe_mk,← forcedSolution_coe] using h

end NLS.LinearVolterra
