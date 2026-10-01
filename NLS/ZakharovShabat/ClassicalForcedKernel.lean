import NLS.ZakharovShabat.ClassicalPotentialVariation

/-! # Variation of constants through the actual fundamental matrix

The two normalized homogeneous columns have determinant one. Their
adjugate transports a continuous forcing term to constant coordinates.
Integrating those coordinates and multiplying back by the fundamental
matrix constructs the actual zero-initial forced solution. This is the
integral kernel needed for the potential gradients of the monodromy.
-/

noncomputable section
set_option maxHeartbeats 400000
open Set Complex MeasureTheory intervalIntegral NLS.LinearVolterra
namespace NLS.ZakharovShabat

def classicalForcedKernelIntegrand (Φ g : Curve (ℂ × ℂ)) (z : ℂ) (s : ℝ) : ℂ × ℂ :=
  ((classicalSolution Φ z (0,1) s).2*(extend g s).1-
      (classicalSolution Φ z (0,1) s).1*(extend g s).2,
    -(classicalSolution Φ z (1,0) s).2*(extend g s).1+
      (classicalSolution Φ z (1,0) s).1*(extend g s).2)

theorem continuous_classicalForcedKernelIntegrand (Φ g : Curve (ℂ × ℂ)) (z : ℂ) :
    Continuous (classicalForcedKernelIntegrand Φ g z) := by
  have ha := continuous_classicalSolution Φ z (1,0)
  have hb := continuous_classicalSolution Φ z (0,1)
  have hg := continuous_extend g
  unfold classicalForcedKernelIntegrand
  fun_prop

def classicalForcedKernelPrimitive (Φ g : Curve (ℂ × ℂ)) (z : ℂ) (t : ℝ) : ℂ × ℂ :=
  ∫ s in (0 : ℝ)..t, classicalForcedKernelIntegrand Φ g z s

theorem hasDerivAt_classicalForcedKernelPrimitive (Φ g : Curve (ℂ × ℂ)) (z : ℂ) (t : ℝ) :
    HasDerivAt (classicalForcedKernelPrimitive Φ g z) (classicalForcedKernelIntegrand Φ g z t) t := by
  have hc := continuous_classicalForcedKernelIntegrand Φ g z
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    (hc.stronglyMeasurableAtFilter volume (nhds t)) hc.continuousAt

theorem continuous_classicalForcedKernelPrimitive (Φ g : Curve (ℂ × ℂ)) (z : ℂ) :
    Continuous (classicalForcedKernelPrimitive Φ g z) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_classicalForcedKernelPrimitive Φ g z t).continuousAt

def classicalForcedKernelSolution (Φ g : Curve (ℂ × ℂ)) (z : ℂ) (t : ℝ) : ℂ × ℂ :=
  (classicalForcedKernelPrimitive Φ g z t).1 • classicalSolution Φ z (1,0) t+
    (classicalForcedKernelPrimitive Φ g z t).2 • classicalSolution Φ z (0,1) t

theorem continuous_classicalForcedKernelSolution (Φ g : Curve (ℂ × ℂ)) (z : ℂ) :
    Continuous (classicalForcedKernelSolution Φ g z) := by
  have ha := continuous_classicalSolution Φ z (1,0)
  have hb := continuous_classicalSolution Φ z (0,1)
  have hq := continuous_classicalForcedKernelPrimitive Φ g z
  exact (hq.fst.smul ha).add (hq.snd.smul hb)

@[simp] theorem classicalForcedKernelSolution_zero (Φ g : Curve (ℂ × ℂ)) (z : ℂ) :
    classicalForcedKernelSolution Φ g z 0 = 0 := by
  simp [classicalForcedKernelSolution,classicalForcedKernelPrimitive]

theorem hasDerivAt_classicalForcedKernelSolution (Φ g : Curve (ℂ × ℂ)) (z : ℂ)
    (t : Icc (0 : ℝ) 1) :
    HasDerivAt (classicalForcedKernelSolution Φ g z)
      (classicalODECoefficient (Φ t) z (classicalForcedKernelSolution Φ g z t)+g t) t := by
  have ha := hasDerivAt_classicalSolution Φ z (1,0) t
  have hb := hasDerivAt_classicalSolution Φ z (0,1) t
  have hq := hasDerivAt_classicalForcedKernelPrimitive Φ g z t
  have h := ((HasFDerivAt.hasDerivAt hq.fst).smul ha).add
    ((HasFDerivAt.hasDerivAt hq.snd).smul hb)
  have hdet := det_classicalFundamentalMatrix Φ z t
  simp only [classicalFundamentalMatrix,Matrix.det_fin_two_of] at hdet
  convert! h using 1
  apply Prod.ext <;>
    simp only [classicalForcedKernelSolution,classicalForcedKernelIntegrand,extend_coe,
      classicalODECoefficient_apply,Prod.smul_fst,Prod.smul_snd,Prod.fst_add,Prod.snd_add,
      smul_eq_mul,ContinuousLinearMap.comp_apply,ContinuousLinearMap.toSpanSingleton_apply,one_smul] <;> dsimp
  · linear_combination -(g t).1*hdet
  · linear_combination -(g t).2*hdet

theorem classicalForcedKernelSolution_eq_forcedSolution
    (Φ g : Curve (ℂ × ℂ)) (z : ℂ) (t : Icc (0 : ℝ) 1) :
    classicalForcedKernelSolution Φ g z t =
      forcedSolution (classicalCoefficientCurveCLM (z,Φ)) g 0 t := by
  let A := classicalCoefficientCurveCLM (z,Φ)
  let U : Curve (ℂ × ℂ) := ⟨fun s => classicalForcedKernelSolution Φ g z s,
    (continuous_classicalForcedKernelSolution Φ g z).comp continuous_subtype_val⟩
  have hU : (1-volterra A) U = primitive g := by
    apply ContinuousMap.ext
    intro r
    have hc : Continuous (fun s : ℝ => extend A s (extend U s)+extend g s) := by
      exact ((continuous_extend A).clm_apply (continuous_extend U)).add (continuous_extend g)
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le r.property.1
      (continuous_classicalForcedKernelSolution Φ g z).continuousOn
      (fun s (hs : s ∈ Ioo (0 : ℝ) r.val) => by
        have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le,hs.2.le.trans r.property.2⟩
        simpa only [A,NLS.LinearVolterra.extend,projIcc_of_mem _ hs',U,ContinuousMap.coe_mk,
          classicalCoefficientCurveCLM_apply] using! hasDerivAt_classicalForcedKernelSolution Φ g z ⟨s,hs'⟩)
      (hc.intervalIntegrable 0 r.val)
    rw [intervalIntegral.integral_add
      (((continuous_extend A).clm_apply (continuous_extend U)).intervalIntegrable _ _)
      ((continuous_extend g).intervalIntegrable _ _),classicalForcedKernelSolution_zero,sub_zero] at hi
    rw [sub_apply,one_apply_eq_self,ContinuousMap.sub_apply,volterra_apply,primitive_apply]
    change classicalForcedKernelSolution Φ g z r-
      (∫ s in (0 : ℝ)..r.val, extend A s (extend U s)) = ∫ s in (0 : ℝ)..r.val, extend g s
    rw [← hi]
    abel
  have heq : U = forcedSolutionCurve A g 0 := by
    have h := congrArg (fun u => solutionOperator A u) hU
    rw [← mul_apply_eq_comp,solutionOperator_mul,one_apply_eq_self] at h
    simpa only [forcedSolutionCurve,
      show ContinuousMap.const (Icc (0 : ℝ) 1) (0 : ℂ × ℂ) = 0 from rfl,zero_add] using h
  have h := congrArg (fun u : Curve (ℂ × ℂ) => u t) heq
  simpa only [U,ContinuousMap.coe_mk,← forcedSolution_coe] using h

end NLS.ZakharovShabat
