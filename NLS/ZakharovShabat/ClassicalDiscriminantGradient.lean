import NLS.ZakharovShabat.ClassicalForcedKernel

/-! # The actual classical discriminant gradient

The potential derivative of the monodromy trace is represented by an
explicit bilinear physical integral. The two gradient components are
polynomials in the actual normalized fundamental columns and endpoint
monodromy, with the original complex signs. The formula is proved from
the Volterra derivative and variation-of-constants kernel; it is not a
spectral-gradient hypothesis.
-/

noncomputable section
set_option maxHeartbeats 400000
open Set Complex MeasureTheory intervalIntegral NLS.LinearVolterra
namespace NLS.ZakharovShabat

def classicalDiscriminantGradient (Φ : Curve (ℂ × ℂ)) (z : ℂ) (s : ℝ) : ℂ × ℂ :=
  let a := classicalSolution Φ z (1,0) s
  let b := classicalSolution Φ z (0,1) s
  let T := classicalMonodromy Φ z
  (I*((T 0 0-T 1 1)*a.2*b.2-T 0 1*a.2^2+T 1 0*b.2^2),
    I*((T 0 0-T 1 1)*a.1*b.1-T 0 1*a.1^2+T 1 0*b.1^2))

theorem continuous_classicalDiscriminantGradient (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    Continuous (classicalDiscriminantGradient Φ z) := by
  have ha := continuous_classicalSolution Φ z (1,0)
  have hb := continuous_classicalSolution Φ z (0,1)
  unfold classicalDiscriminantGradient
  fun_prop

theorem fderiv_classicalDiscriminant_eq_potentialVariations
    (Φ H : Curve (ℂ × ℂ)) (z : ℂ) :
    (fderiv ℂ (fun Ψ : Curve (ℂ × ℂ) => classicalDiscriminant Ψ z) Φ) H =
      (classicalPotentialVariation Φ H z (1,0) 1).1+
        (classicalPotentialVariation Φ H z (0,1) 1).2 := by
  let t : Icc (0 : ℝ) 1 := ⟨1,by constructor <;> norm_num⟩
  have h₁ := (analyticOnNhd_classicalSolution_joint (1,0) t (z,Φ) (mem_univ _)).comp
    (f := fun Ψ : Curve (ℂ × ℂ) => (z,Ψ)) (analyticAt_const.prod analyticAt_id)
  have h₂ := (analyticOnNhd_classicalSolution_joint (0,1) t (z,Φ) (mem_univ _)).comp
    (f := fun Ψ : Curve (ℂ × ℂ) => (z,Ψ)) (analyticAt_const.prod analyticAt_id)
  have hfd := congrArg (fun L => L H)
    ((h₁.differentiableAt.hasFDerivAt.fst).add (h₂.differentiableAt.hasFDerivAt.snd)).fderiv
  have heq : (fun Ψ : Curve (ℂ × ℂ) =>
      (classicalSolution Ψ z (1,0) t).1+(classicalSolution Ψ z (0,1) t).2) =
      (fun Ψ => classicalDiscriminant Ψ z) := by
    funext Ψ
    simp [classicalDiscriminant,classicalMonodromy,classicalFundamentalMatrix,Matrix.trace_fin_two,t]
  change (fderiv ℂ (fun Ψ : Curve (ℂ × ℂ) =>
    (classicalSolution Ψ z (1,0) t).1+(classicalSolution Ψ z (0,1) t).2) Φ) H = _ at hfd
  rw [heq] at hfd
  simp only [Function.comp_def,add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd'] at hfd
  rw [fderiv_classicalSolution_potential Φ H z (1,0) t,
    fderiv_classicalSolution_potential Φ H z (0,1) t] at hfd
  exact hfd

theorem fderiv_classicalDiscriminant_eq_gradient_integral
    (Φ H : Curve (ℂ × ℂ)) (z : ℂ) :
    (fderiv ℂ (fun Ψ : Curve (ℂ × ℂ) => classicalDiscriminant Ψ z) Φ) H =
      ∫ s in (0 : ℝ)..1, (classicalDiscriminantGradient Φ z s).1*(extend H s).1+
        (classicalDiscriminantGradient Φ z s).2*(extend H s).2 := by
  let t : Icc (0 : ℝ) 1 := ⟨1,by constructor <;> norm_num⟩
  let g₁ := classicalPotentialVariationSource Φ H z (1,0)
  let g₂ := classicalPotentialVariationSource Φ H z (0,1)
  let L₁ : (ℂ × ℂ) →L[ℂ] ℂ :=
    (classicalSolution Φ z (1,0) 1).1 • ContinuousLinearMap.fst ℂ ℂ ℂ+
      (classicalSolution Φ z (0,1) 1).1 • ContinuousLinearMap.snd ℂ ℂ ℂ
  let L₂ : (ℂ × ℂ) →L[ℂ] ℂ :=
    (classicalSolution Φ z (1,0) 1).2 • ContinuousLinearMap.fst ℂ ℂ ℂ+
      (classicalSolution Φ z (0,1) 1).2 • ContinuousLinearMap.snd ℂ ℂ ℂ
  have hv (v : ℂ × ℂ) : classicalPotentialVariation Φ H z v 1 =
      classicalForcedKernelSolution Φ (classicalPotentialVariationSource Φ H z v) z 1 :=
    (classicalForcedKernelSolution_eq_forcedSolution Φ (classicalPotentialVariationSource Φ H z v) z t).symm
  have hv₁ : (classicalPotentialVariation Φ H z (1,0) 1).1 =
      L₁ (∫ s in (0 : ℝ)..1, classicalForcedKernelIntegrand Φ g₁ z s) := by
    rw [hv]
    simp only [classicalForcedKernelSolution,classicalForcedKernelPrimitive,L₁,g₁,
      Prod.fst_add,Prod.smul_fst,smul_eq_mul,add_apply,smul_apply,
      ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd']
    ring
  have hv₂ : (classicalPotentialVariation Φ H z (0,1) 1).2 =
      L₂ (∫ s in (0 : ℝ)..1, classicalForcedKernelIntegrand Φ g₂ z s) := by
    rw [hv]
    simp only [classicalForcedKernelSolution,classicalForcedKernelPrimitive,L₂,g₂,
      Prod.snd_add,Prod.smul_snd,smul_eq_mul,add_apply,smul_apply,
      ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd']
    ring
  have hc₁ := continuous_classicalForcedKernelIntegrand Φ g₁ z
  have hc₂ := continuous_classicalForcedKernelIntegrand Φ g₂ z
  have hi₁ : IntervalIntegrable (fun s : ℝ => L₁ (classicalForcedKernelIntegrand Φ g₁ z s)) volume 0 1 :=
    (L₁.continuous.comp hc₁).intervalIntegrable 0 1
  have hi₂ : IntervalIntegrable (fun s : ℝ => L₂ (classicalForcedKernelIntegrand Φ g₂ z s)) volume 0 1 :=
    (L₂.continuous.comp hc₂).intervalIntegrable 0 1
  rw [fderiv_classicalDiscriminant_eq_potentialVariations,hv₁,hv₂,
    ← L₁.intervalIntegral_comp_comm (hc₁.intervalIntegrable 0 1),
    ← L₂.intervalIntegral_comp_comm (hc₂.intervalIntegrable 0 1),
    ← intervalIntegral.integral_add hi₁ hi₂]
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs
  simp only [L₁,L₂,classicalForcedKernelIntegrand,g₁,g₂,smul_apply,add_apply,smul_eq_mul,
    ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',
    NLS.LinearVolterra.extend,projIcc_of_mem _ hs',classicalPotentialVariationSource_apply,
    classicalDiscriminantGradient,classicalMonodromy,classicalFundamentalMatrix]
  dsimp
  ring

/-- The initial fundamental matrix is the identity, giving the exact
boundary value with the original two component signs. -/
@[simp] theorem classicalDiscriminantGradient_zero (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    classicalDiscriminantGradient Φ z 0 =
      (I*classicalMonodromy Φ z 1 0,-I*classicalMonodromy Φ z 0 1) := by
  simp [classicalDiscriminantGradient]

/-- Determinant one gives the same gradient value at the other endpoint,
without requiring the potential itself to have matching endpoint values. -/
@[simp] theorem classicalDiscriminantGradient_one (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    classicalDiscriminantGradient Φ z 1 =
      (I*classicalMonodromy Φ z 1 0,-I*classicalMonodromy Φ z 0 1) := by
  have hdet := det_classicalMonodromy Φ z
  simp only [Matrix.det_fin_two] at hdet
  let T := classicalMonodromy Φ z
  change T 0 0*T 1 1-T 0 1*T 1 0 = 1 at hdet
  change (I*((T 0 0-T 1 1)*T 1 0*T 1 1-T 0 1*(T 1 0)^2+T 1 0*(T 1 1)^2),
    I*((T 0 0-T 1 1)*T 0 0*T 0 1-T 0 1*(T 0 0)^2+T 1 0*(T 0 1)^2)) =
      (I*T 1 0,-I*T 0 1)
  apply Prod.ext <;> dsimp
  · linear_combination I*(T 1 0)*hdet
  · linear_combination -I*(T 0 1)*hdet

/-- The actual potential gradient has matching endpoints. -/
theorem classicalDiscriminantGradient_endpoints (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    classicalDiscriminantGradient Φ z 1 = classicalDiscriminantGradient Φ z 0 := by
  rw [classicalDiscriminantGradient_one,classicalDiscriminantGradient_zero]

end NLS.ZakharovShabat
