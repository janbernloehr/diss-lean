import NLS.ZakharovShabat.SobolevHierarchyNonlocalIntegral
import NLS.ZakharovShabat.SobolevSignedReflectionProjection
import NLS.ZakharovShabat.ClassicalHierarchyReflectionIntegral

/-! # The reflected Lenard integral graph on the full original Sobolev domain

The top gradient stays L2. All continuous nonlinear factors are integrated
through bounded primitive operators. A bounded signed-reflection projection
keeps the exact constraint throughout smooth approximation.
-/
noncomputable section
open Set Complex MeasureTheory NLS.Fourier NLS.LinearVolterra NLS.FunctionalAnalysis
open scoped ContDiff
namespace NLS.ZakharovShabat

def hierarchyFTCLeft (s k : ℕ) (ab : SobolevSource s) (t : Icc (0:ℝ) 1) : ℂ × ℂ :=
  ((hierarchyUnitGradient s k ab).1 t-(hierarchyUnitGradient s k ab).1 ⟨0,by norm_num⟩,
   (hierarchyUnitGradient s k ab).2 t-(hierarchyUnitGradient s k ab).2 ⟨0,by norm_num⟩)

def hierarchyFTCRight (s k : ℕ) (ab : SobolevSource s) (t : Icc (0:ℝ) 1) : ℂ × ℂ :=
  (I*circlePrimitive t.val (sobolevNLSHierarchyCircleGradient s (k+1) ab).1-
      (2*I)*(hierarchyIntegratedNonlocal s k ab).1 t,
   -I*circlePrimitive t.val (sobolevNLSHierarchyCircleGradient s (k+1) ab).2-
      (2*I)*(hierarchyIntegratedNonlocal s k ab).2 t)

theorem continuous_hierarchyFTCLeft (s k : ℕ) (t : Icc (0:ℝ) 1) :
    Continuous (fun ab => hierarchyFTCLeft s k ab t) := by
  have hG := continuous_hierarchyUnitGradient s k
  have hEval := (ContinuousMap.evalCLM ℂ t : Curve ℂ →L[ℂ] ℂ).continuous
  have hZero := (ContinuousMap.evalCLM ℂ (⟨0,by norm_num⟩ : Icc (0:ℝ) 1) : Curve ℂ →L[ℂ] ℂ).continuous
  exact ((hEval.comp hG.fst).sub (hZero.comp hG.fst)).prodMk
    ((hEval.comp hG.snd).sub (hZero.comp hG.snd))

theorem continuous_hierarchyFTCRight (s k : ℕ) (t : Icc (0:ℝ) 1) :
    Continuous (fun ab => hierarchyFTCRight s k ab t) := by
  have hE : Continuous (sobolevNLSHierarchyCircleGradient s (k+1)) :=
    continuous_iff_continuousAt.mpr fun ab => (analyticAt_sobolevNLSHierarchyCircleGradient s (k+1) ab).continuousAt
  have hN := continuous_hierarchyIntegratedNonlocal s k
  have hEval := (ContinuousMap.evalCLM ℂ t : Curve ℂ →L[ℂ] ℂ).continuous
  have hInt := (circlePrimitiveCLM t.val ⟨t.property.1,t.property.2.trans (by norm_num)⟩).continuous
  exact ((continuous_const.mul (hInt.comp hE.fst)).sub
    (continuous_const.mul (hEval.comp hN.fst))).prodMk
      ((continuous_const.mul (hInt.comp hE.snd)).sub (continuous_const.mul (hEval.comp hN.snd)))

theorem hierarchyFTC_eq_of_smooth_reflection
    (m : ℕ) (ε : ℂ) (hε : ε=1 ∨ ε = -1) (ab : SobolevSource (2*m+1)) (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (haq : ∀ j, ab.1.val j = periodOneCoefficient a j)
    (hbq : ∀ j, ab.2.val j = periodOneCoefficient b j)
    (hTa : ∀ x, ε*a (1-x)=a x) (hTb : ∀ x, ε*b (1-x)=b x) (t : Icc (0:ℝ) 1) :
    hierarchyFTCLeft (2*m+1) (2*m+1) ab t = hierarchyFTCRight (2*m+1) (2*m+1) ab t := by
  have hG := hierarchyUnitGradient_eq_classical (2*m+1) (2*m+1) (by omega) le_rfl
    ab a b ha hb hpa hpb haq hbq
  have hE := sobolevNLSHierarchyCircleGradient_eq_classical (2*m+1) (2*m+2) (by omega) (by omega)
    ab a b ha hb hpa hpb haq hbq
  have hN := hierarchyIntegratedNonlocal_eq_classical (2*m+1) (2*m+1) (by omega) le_rfl
    ab a b ha hb hpa hpb haq hbq t
  have hG₁ := congrArg Prod.fst (hG t)
  have hG₂ := congrArg Prod.snd (hG t)
  have hG₀₁ := congrArg Prod.fst (hG ⟨0,by norm_num⟩)
  have hG₀₂ := congrArg Prod.snd (hG ⟨0,by norm_num⟩)
  have hN₁ := congrArg Prod.fst hN
  have hN₂ := congrArg Prod.snd hN
  dsimp only at hG₁ hG₂ hG₀₁ hG₀₂ hN₁ hN₂
  have hE₁ := circlePrimitive_eq_of_ae_unit _ _ (hE.fun_comp Prod.fst) t
  have hE₂ := circlePrimitive_eq_of_ae_unit _ _ (hE.fun_comp Prod.snd) t
  unfold hierarchyFTCLeft hierarchyFTCRight
  rw [hG₁,hG₂,hG₀₁,hG₀₂,hE₁,hE₂,hN₁,hN₂]
  exact classicalNLSHierarchyGradient_reflection_integral ε hε a b ha hb hpa hpb hTa hTb m t.val

/-- No smoothness strengthening or unconstrained density assumption is used. -/
theorem hierarchyFTC_eq_of_reflection
    (m : ℕ) (ε : ℂ) (hε : ε=1 ∨ ε = -1) (ab : SobolevSource (2*m+1))
    (hT : hierarchyMidpointReflection (2*m+1) ab=ε • ab) (t : Icc (0:ℝ) 1) :
    hierarchyFTCLeft (2*m+1) (2*m+1) ab t = hierarchyFTCRight (2*m+1) (2*m+1) ab t := by
  let proj := hierarchySignedReflectionProjection (2*m+1) ε
  let F := fun cd => hierarchyFTCLeft (2*m+1) (2*m+1) (proj cd) t
  let G := fun cd => hierarchyFTCRight (2*m+1) (2*m+1) (proj cd) t
  have hF : Continuous F := (continuous_hierarchyFTCLeft (2*m+1) (2*m+1) t).comp proj.continuous
  have hG : Continuous G := (continuous_hierarchyFTCRight (2*m+1) (2*m+1) t).comp proj.continuous
  have he := eq_of_continuous_of_smooth_sobolevSource (2*m+1) F G hF hG (by
    intro cd a b ha hb hpa hpb haq hbq
    have hcoef := hierarchySignedReflectionProjection_coefficients (2*m+1) ε cd a b
      ha.continuous hb.continuous haq hbq
    exact hierarchyFTC_eq_of_smooth_reflection m ε hε (proj cd)
      (signedReflectedProfile ε a) (signedReflectedProfile ε b)
      (contDiff_signedReflectedProfile ε a ha) (contDiff_signedReflectedProfile ε b hb)
      (periodic_signedReflectedProfile ε a hpa) (periodic_signedReflectedProfile ε b hpb)
      (fun j => (hcoef j).1) (fun j => (hcoef j).2)
      (signedReflectedProfile_reflection ε hε a) (signedReflectedProfile_reflection ε hε b) t)
  have h := congrFun he ab
  change hierarchyFTCLeft (2*m+1) (2*m+1) (proj ab) t = hierarchyFTCRight (2*m+1) (2*m+1) (proj ab) t at h
  rw [hierarchySignedReflectionProjection_fixed (2*m+1) ε hε ab hT] at h
  exact h

end NLS.ZakharovShabat
