import NLS.MKdV.QuasiHillJointAnalytic
import NLS.ZakharovShabat.ClassicalPhaseMonodromy
import NLS.ZakharovShabat.ClassicalSeparatedGradient

/-! # The independent scalar Dirichlet characteristic and the rotated ZS boundary

The initial scalar position is zero and its quasi-derivative is one.
The original ZS separated characteristic at the fixed source phase is
exactly z times this independently constructed scalar characteristic.
-/
noncomputable section
open Set Complex Filter Topology
open NLS.LinearVolterra NLS.ZakharovShabat
namespace NLS.MKdV

def quasiHillDirichletCharacteristic (U : Curve ℂ) (E : ℂ) : ℂ :=
  (quasiHillSolution U E (0,1) 1).1

theorem analyticOnNhd_quasiHillDirichletCharacteristic_joint :
    AnalyticOnNhd ℂ (fun t : ℂ × Curve ℂ => quasiHillDirichletCharacteristic t.2 t.1) univ := by
  intro t _
  have h := (analyticOnNhd_solution_coefficient (E := ℂ × ℂ) (0,1)
    ⟨1,by norm_num⟩ (quasiHillCoefficientCurve t.2 t.1) (mem_univ _)).comp
      (f := fun p : ℂ × Curve ℂ => quasiHillCoefficientCurve p.2 p.1)
      (analyticOnNhd_quasiHillCoefficientCurve_joint t (mem_univ _))
  exact analyticAt_fst.comp h

theorem quasiHillDirichletCharacteristic_eq_rotatedZS (U : Curve ℂ) (Φ : Curve (ℂ × ℂ))
    (hΦ : ∀ t, Φ t = (U t,U t)) (z : ℂ) :
    z*quasiHillDirichletCharacteristic U (z^2) =
      classicalSeparatedCharacteristic .dirichlet (classicalSourcePhase Φ) z := by
  let t : Icc (0 : ℝ) 1 := ⟨1,by norm_num⟩
  have hv : miuraStateMap 0 z (1,I) = (-2*I*z) • (0,1) := by
    apply Prod.ext
    · change (1 : ℂ)+I*I = (-2*I*z)*0
      norm_num [I_sq]
    · change (0 : ℂ)*(1+I*I)-I*z*(1-I*I) = (-2*I*z)*1
      rw [show I*I = -1 by norm_num]
      ring
  have hscale : quasiHillSolution U (z^2) (miuraStateMap 0 z (1,I)) t =
      (-2*I*z) • quasiHillSolution U (z^2) (0,1) t := by
    rw [hv]
    simpa only [solutionMap_apply,quasiHillSolution] using
      (map_smul (solutionMap (quasiHillCoefficientCurve U (z^2)) t) (-2*I*z) (0,1))
  have ht := congrArg Prod.fst (quasiHillSolution_eq_transformedZS U Φ hΦ z (1,I) t)
  rw [hscale] at ht
  have hphase := classicalSolution_auxiliaryPhase Φ z (1,1) t
  have hinit : auxiliaryPhase ℂ (1,1) = (1,I) := by simp [auxiliaryPhase_apply,smul_eq_mul]
  rw [hinit] at hphase
  rw [hphase] at ht
  simp only [miuraStateMap_apply,auxiliaryPhase_apply,Prod.smul_fst,smul_eq_mul] at ht
  simp only [← mul_assoc,show I*I = -1 by norm_num] at ht
  have hchar := classicalSeparatedCharacteristic_eq_endpoint .dirichlet (classicalSourcePhase Φ) z
  rw [classicalSeparatedEndpointCLM_apply] at hchar
  simp only [BoundaryCondition.extensionSign,one_mul] at hchar
  change classicalSeparatedCharacteristic .dirichlet (classicalSourcePhase Φ) z =
    ((classicalSolution (classicalSourcePhase Φ) z (1,1) t).2-
      (classicalSolution (classicalSourcePhase Φ) z (1,1) t).1)/(2*I) at hchar
  rw [hchar]
  apply (eq_div_iff (by norm_num : (2*I : ℂ) ≠ 0)).mpr
  change (z*(quasiHillSolution U (z^2) (0,1) t).1)*(2*I) = _
  linear_combination -ht

end NLS.MKdV
