import NLS.MKdV.QuasiHillZSComparison
import NLS.KdV.ClassicalFreePrimitive
import NLS.ZakharovShabat.ClassicalFreeDiscriminant

/-! # Joint analytic dependence of the independent Miura IVP

The original quasi-derivative coefficient is affine in both the energy and
the continuous profile. Its actual Volterra trace is therefore jointly
entire, including at zero energy and on the full complex curve space.
-/
noncomputable section
open Set Complex NLS.LinearVolterra NLS.ZakharovShabat
namespace NLS.MKdV

def quasiHillSourceCurveCLM :
    Curve ℂ →L[ℂ] Curve ((ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) :=
  ContinuousLinearMap.compLeftContinuous ℂ (Icc (0 : ℝ) 1)
    (ContinuousLinearMap.toSpanSingleton ℂ
      ((ContinuousLinearMap.fst ℂ ℂ ℂ).prod (-ContinuousLinearMap.snd ℂ ℂ ℂ)))

@[simp] theorem quasiHillSourceCurveCLM_apply (U : Curve ℂ) (s : Icc (0 : ℝ) 1) (v : ℂ × ℂ) :
    quasiHillSourceCurveCLM U s v = (U s) • (v.1,-v.2) := rfl

def quasiHillEnergyCurveCLM : ℂ →L[ℂ] Curve ((ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) :=
  ContinuousLinearMap.toSpanSingleton ℂ (ContinuousMap.const _
    ((0 : (ℂ × ℂ) →L[ℂ] ℂ).prod (-ContinuousLinearMap.fst ℂ ℂ ℂ)))

@[simp] theorem quasiHillEnergyCurveCLM_apply (μ : ℂ) (s : Icc (0 : ℝ) 1) (v : ℂ × ℂ) :
    quasiHillEnergyCurveCLM μ s v = μ • (0,-v.1) := rfl

theorem quasiHillCoefficientCurve_eq_affine (U : Curve ℂ) (μ : ℂ) :
    quasiHillCoefficientCurve U μ = ContinuousMap.const _ (quasiHillCoefficient 0 0)+
      quasiHillSourceCurveCLM U+quasiHillEnergyCurveCLM μ := by
  apply ContinuousMap.ext
  intro s
  apply ContinuousLinearMap.ext
  intro v
  simp only [quasiHillCoefficientCurve_apply,ContinuousMap.add_apply,add_apply,
    ContinuousMap.const_apply,quasiHillSourceCurveCLM_apply,quasiHillEnergyCurveCLM_apply,
    quasiHillCoefficient_apply]
  apply Prod.ext <;> dsimp <;> ring

theorem analyticOnNhd_quasiHillCoefficientCurve_joint :
    AnalyticOnNhd ℂ (fun t : ℂ × Curve ℂ => quasiHillCoefficientCurve t.2 t.1) univ := by
  intro t _
  have hU : AnalyticAt ℂ (fun p : ℂ × Curve ℂ => quasiHillSourceCurveCLM p.2) t := by
    convert! ContinuousLinearMap.analyticAt (𝕜 := ℂ)
      (F := Curve ((ℂ × ℂ) →L[ℂ] (ℂ × ℂ)))
      (quasiHillSourceCurveCLM.comp (ContinuousLinearMap.snd ℂ ℂ (Curve ℂ))) t
  have hμ : AnalyticAt ℂ (fun p : ℂ × Curve ℂ => quasiHillEnergyCurveCLM p.1) t := by
    convert! ContinuousLinearMap.analyticAt (𝕜 := ℂ)
      (F := Curve ((ℂ × ℂ) →L[ℂ] (ℂ × ℂ)))
      (quasiHillEnergyCurveCLM.comp (ContinuousLinearMap.fst ℂ ℂ (Curve ℂ))) t
  have hA : AnalyticAt ℂ (fun p : ℂ × Curve ℂ =>
      ContinuousMap.const _ (quasiHillCoefficient 0 0)+quasiHillSourceCurveCLM p.2+
        quasiHillEnergyCurveCLM p.1) t := (analyticAt_const.add hU).add hμ
  exact hA.congr (Filter.Eventually.of_forall (fun p => (quasiHillCoefficientCurve_eq_affine p.2 p.1).symm))

theorem analyticOnNhd_quasiHillDiscriminant_joint :
    AnalyticOnNhd ℂ (fun t : ℂ × Curve ℂ => quasiHillDiscriminant t.2 t.1) univ := by
  intro t _
  simp only [quasiHillDiscriminant,trace_pairCLM,solutionMap_apply]
  have hC := analyticOnNhd_quasiHillCoefficientCurve_joint t (mem_univ _)
  have h1 := (analyticOnNhd_solution_coefficient (E := ℂ × ℂ) (1,0)
    ⟨1,by constructor <;> norm_num⟩ (quasiHillCoefficientCurve t.2 t.1) (mem_univ _)).comp
      (f := fun p : ℂ × Curve ℂ => quasiHillCoefficientCurve p.2 p.1) hC
  have h2 := (analyticOnNhd_solution_coefficient (E := ℂ × ℂ) (0,1)
    ⟨1,by constructor <;> norm_num⟩ (quasiHillCoefficientCurve t.2 t.1) (mem_univ _)).comp
      (f := fun p : ℂ × Curve ℂ => quasiHillCoefficientCurve p.2 p.1) hC
  exact (analyticAt_fst.comp h1).add (analyticAt_snd.comp h2)

theorem quasiHillDiscriminant_zero (μ : ℂ) :
    quasiHillDiscriminant 0 μ = NLS.KdV.classicalHillDiscriminant 0 μ := by
  have hs : (Complex.sqrt μ)^2 = μ := by
    have h := Complex.cpow_nat_inv_pow μ (Nat.succ_ne_zero 1)
    norm_num at h
    simpa only [Complex.sqrt,one_div] using h
  rw [← hs,quasiHillDiscriminant_eq_ZS 0 0 (fun _ => rfl),classicalDiscriminant_free]
  rw [NLS.KdV.classicalHillDiscriminant_zero]
  rw [hs]
  rfl

end NLS.MKdV
