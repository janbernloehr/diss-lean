import NLS.MKdV.QuasiHillJointAnalytic
import NLS.MKdV.MiuraHillSpectralBridge
import NLS.KdV.ClassicalHillDirichlet

/-! A fixed invertible state transformation realizes the quasi-Hill equation
as a ZS system with coefficients affine in the energy. No square root,
spectral division, or excluded zero energy enters this realization. -/
noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra NLS.ZakharovShabat
namespace NLS.MKdV

/-- Fixed conversion from ZS coordinates to position/quasi-derivative. -/
def quasiHillEnergyStateMap : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
  (ContinuousLinearMap.fst ℂ ℂ ℂ+ContinuousLinearMap.snd ℂ ℂ ℂ).prod
    (I • (ContinuousLinearMap.fst ℂ ℂ ℂ-ContinuousLinearMap.snd ℂ ℂ ℂ))

@[simp] theorem quasiHillEnergyStateMap_apply (v : ℂ × ℂ) :
    quasiHillEnergyStateMap v = (v.1+v.2,I*(v.1-v.2)) := rfl

/-- Exact inverse initial data for every scalar state. -/
def quasiHillEnergyInitialVector (v : ℂ × ℂ) : ℂ × ℂ :=
  ((v.1-I*v.2)/2,(v.1+I*v.2)/2)

theorem quasiHillEnergyStateMap_initialVector (v : ℂ × ℂ) :
    quasiHillEnergyStateMap (quasiHillEnergyInitialVector v) = v := by
  apply Prod.ext <;> simp only [quasiHillEnergyStateMap_apply,quasiHillEnergyInitialVector]
  · ring
  · ring_nf
    simp [I_sq]

/-- The constant frequency and affine off-diagonal entries of the energy realization. -/
theorem quasiHillEnergyStateMap_ode (u lambda : ℂ) (v : ℂ × ℂ) :
    quasiHillCoefficient u lambda (quasiHillEnergyStateMap v) =
      quasiHillEnergyStateMap (classicalODECoefficient
        (-I*u+(lambda-1)/2,I*u+(lambda-1)/2) (-(lambda+1)/2) v) := by
  apply Prod.ext <;>
    simp only [quasiHillCoefficient_apply,quasiHillEnergyStateMap_apply,classicalODECoefficient_apply] <;>
    ring_nf <;> simp [I_sq]
  all_goals ring

/-- Actual continuous ZS coefficient curve, affine in the energy and profile. -/
def quasiHillEnergyCurve (U : Curve ℂ) (lambda : ℂ) : Curve (ℂ × ℂ) :=
  ⟨fun t => (-I*U t+(lambda-1)/2,I*U t+(lambda-1)/2),by fun_prop⟩

/-- Actual solution identity on the whole interval, including zero energy. -/
theorem quasiHillSolution_eq_energyZS (U : Curve ℂ) (lambda : ℂ) (v : ℂ × ℂ)
    (t : Icc (0:ℝ) 1) :
    quasiHillSolution U lambda (quasiHillEnergyStateMap v) t =
      quasiHillEnergyStateMap (classicalSolution (quasiHillEnergyCurve U lambda) (-(lambda+1)/2) v t) := by
  have h := solutionMap_intertwine (classicalCoefficientCurveCLM
    (-(lambda+1)/2,quasiHillEnergyCurve U lambda))
    (quasiHillCoefficientCurve U lambda) quasiHillEnergyStateMap (by
      intro s w
      rw [quasiHillCoefficientCurve_apply,classicalCoefficientCurveCLM_apply]
      exact quasiHillEnergyStateMap_ode (U s) lambda w) v t
  simpa only [solutionMap_apply,realCoefficient_classicalCoefficientCurve,
    quasiHillSolution,classicalSolution] using h

/-- The actual independent scalar Dirichlet characteristic. -/
def quasiHillDirichlet (U : Curve ℂ) (lambda : ℂ) : ℂ :=
  (quasiHillSolution U lambda (0,1) 1).1

/-- The fixed-state energy realization retains the exact Dirichlet normalization. -/
theorem quasiHillDirichlet_eq_energyZS (U : Curve ℂ) (lambda : ℂ) :
    quasiHillDirichlet U lambda =
      let v := classicalSolution (quasiHillEnergyCurve U lambda) (-(lambda+1)/2)
        (quasiHillEnergyInitialVector (0,1)) 1
      v.1+v.2 := by
  have h := quasiHillSolution_eq_energyZS U lambda (quasiHillEnergyInitialVector (0,1))
    ⟨1,by constructor <;> norm_num⟩
  rw [quasiHillEnergyStateMap_initialVector] at h
  exact congrArg Prod.fst h

/-- Joint analyticity in the actual energy and continuous Miura profile. -/
theorem analyticOnNhd_quasiHillDirichlet_joint :
    AnalyticOnNhd ℂ (fun p : ℂ × Curve ℂ => quasiHillDirichlet p.2 p.1) univ := by
  intro p _
  have hC := analyticOnNhd_quasiHillCoefficientCurve_joint p (mem_univ _)
  have hs := (analyticOnNhd_solution_coefficient (E := ℂ × ℂ) (0,1)
    ⟨1,by constructor <;> norm_num⟩ (quasiHillCoefficientCurve p.2 p.1) (mem_univ _)).comp
      (f := fun t : ℂ × Curve ℂ => quasiHillCoefficientCurve t.2 t.1) hC
  exact analyticAt_fst.comp hs

/-- The scalar characteristic agrees with the physical Hill IVP for every
absolutely continuous Miura profile with the stated continuous potential. -/
theorem quasiHillDirichlet_eq_classical_of_ac
    (U : Curve ℂ) (u : ℝ → ℂ) (hU : ∀ t, U t = u t)
    (hu : AbsolutelyContinuousOnInterval u 0 1) (q : Curve ℂ)
    (hq : ∀ᵐ x : ℝ, x ∈ Icc (0:ℝ) 1 → extend q x = miuraPotential u x)
    (lambda : ℂ) :
    quasiHillDirichlet U lambda = NLS.KdV.classicalHillDirichlet q lambda := by
  have h := congrArg Prod.fst (physicalMiuraState_eq_classicalHillFlow U u hU hu q hq lambda (0,1)
    (by norm_num : (1:ℝ) ∈ Icc (0:ℝ) 1))
  simpa only [quasiHillDirichlet,NLS.KdV.classicalHillDirichlet,physicalMiuraSolution,
    mul_zero,sub_zero] using h

/-- Exact physical Dirichlet comparison on every C1 profile; matching
endpoint values of the profile are unnecessary for the Dirichlet condition. -/
theorem quasiHillDirichlet_profile_eq_classicalHill
    (u : ℝ → ℂ) (hu : ContDiff ℝ 1 u) (lambda : ℂ) :
    quasiHillDirichlet (miuraProfileCurve u hu.continuous) lambda =
      NLS.KdV.classicalHillDirichlet (miuraHillProfileCurve u hu) lambda := by
  apply quasiHillDirichlet_eq_classical_of_ac _ u (fun _ => rfl)
    hu.contDiffOn.absolutelyContinuousOnInterval
  exact Filter.Eventually.of_forall (fun x hx => by
    rw [extend_coe _ ⟨x,hx⟩]
    rfl)

end NLS.MKdV
