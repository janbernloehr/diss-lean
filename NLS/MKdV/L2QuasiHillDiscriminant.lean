import NLS.MKdV.L2QuasiHillSolution
import NLS.ZakharovShabat.L2FundamentalInitialValue

/-! # The rough quasi-Hill monodromy trace at every energy

This trace uses the two actual prescribed-data solutions. It is jointly
entire in the physical scalar L2 class and energy, equals the independent
continuous-profile Hill trace on continuous inputs, and is calibrated to
the original diagonal physical AKNS trace by density.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology
open NLS.LinearVolterra NLS.ZakharovShabat
namespace NLS.MKdV

def l2QuasiHillDiscriminant (u : IntervalL2) (μ : ℂ) : ℂ :=
  (l2QuasiHillSolution u μ (1,0) ⟨1,by constructor <;> norm_num⟩).1+
    (l2QuasiHillSolution u μ (0,1) ⟨1,by constructor <;> norm_num⟩).2

theorem analyticOnNhd_l2QuasiHillDiscriminant_joint :
    AnalyticOnNhd ℂ (fun p : ℂ × IntervalL2 => l2QuasiHillDiscriminant p.2 p.1) univ := by
  intro p _
  let t : Icc (0 : ℝ) 1 := ⟨1,by constructor <;> norm_num⟩
  have h₁ := ((ContinuousMap.evalCLM ℂ t).analyticAt _).comp
    (f := fun p : ℂ × IntervalL2 => l2QuasiHillSolution p.2 p.1 (1,0))
    (analyticOnNhd_l2QuasiHillSolution_joint (1,0) p (mem_univ p))
  have h₂ := ((ContinuousMap.evalCLM ℂ t).analyticAt _).comp
    (f := fun p : ℂ × IntervalL2 => l2QuasiHillSolution p.2 p.1 (0,1))
    (analyticOnNhd_l2QuasiHillSolution_joint (0,1) p (mem_univ p))
  exact (analyticAt_fst.comp h₁).add (analyticAt_snd.comp h₂)

theorem l2QuasiHillDiscriminant_eq_affine_AKNS (u : IntervalL2) (μ : ℂ) :
    l2QuasiHillDiscriminant u μ = l2Discriminant (l2QuasiHillPotential u μ) (quasiHillAffineFrequency μ) := by
  let t : Icc (0 : ℝ) 1 := ⟨1,by constructor <;> norm_num⟩
  let W := fun v => l2SolutionCurve (l2QuasiHillPotential u μ) (quasiHillAffineFrequency μ) v t
  have h (v : ℂ × ℂ) : W v = v.1 • W (1,0)+v.2 • W (0,1) := by
    exact congrArg (fun w : Curve (ℂ × ℂ) => w t)
      (l2SolutionCurve_linearCombination (l2QuasiHillPotential u μ) (quasiHillAffineFrequency μ) v)
  change (quasiHillFixedState (W (quasiHillFixedStateInv (1,0)))).1+
    (quasiHillFixedState (W (quasiHillFixedStateInv (0,1)))).2 = _
  rw [h (quasiHillFixedStateInv (1,0)),h (quasiHillFixedStateInv (0,1))]
  simp only [l2Discriminant,l2Monodromy,l2FundamentalMatrix,Matrix.trace_fin_two]
  change (quasiHillFixedState ((quasiHillFixedStateInv (1,0)).1 • W (1,0)+
      (quasiHillFixedStateInv (1,0)).2 • W (0,1))).1+
    (quasiHillFixedState ((quasiHillFixedStateInv (0,1)).1 • W (1,0)+
      (quasiHillFixedStateInv (0,1)).2 • W (0,1))).2 = (W (1,0)).1+(W (0,1)).2
  simp only [quasiHillFixedStateInv,smul_apply,quasiHillFixedState,
    miuraStateMap_apply,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,Prod.fst_add,Prod.snd_add,
    zero_mul,zero_sub,mul_zero,mul_one,add_zero,zero_add,sub_zero]
  ring_nf
  simp [I_sq]
  ring

theorem l2QuasiHillSolution_continuous (u : Curve ℂ) (μ : ℂ) (v : ℂ × ℂ)
    (t : Icc (0 : ℝ) 1) :
    l2QuasiHillSolution (continuousQuasiHillL2 u) μ v t = quasiHillSolution u μ v t := by
  rw [l2QuasiHillSolution_apply,l2QuasiHillPotential_continuous,l2SolutionCurve_of_continuous,
    classicalSolutionCurve_apply]
  have he := solutionMap_intertwine
    (classicalCoefficientCurveCLM (quasiHillAffineFrequency μ,quasiHillAffineCurve u μ))
    (quasiHillCoefficientCurve u μ) quasiHillFixedState (by
      intro s w
      rw [quasiHillCoefficientCurve_apply,classicalCoefficientCurveCLM_apply]
      exact quasiHillCoefficient_affine_intertwine (u s) μ w) (quasiHillFixedStateInv v) t
  rw [quasiHillFixedState_right_inv] at he
  simpa only [solutionMap_apply,realCoefficient_classicalCoefficientCurve,quasiHillSolution,classicalSolution] using he.symm

theorem l2QuasiHillDiscriminant_continuous (u : Curve ℂ) (μ : ℂ) :
    l2QuasiHillDiscriminant (continuousQuasiHillL2 u) μ = quasiHillDiscriminant u μ := by
  rw [l2QuasiHillDiscriminant,l2QuasiHillSolution_continuous,l2QuasiHillSolution_continuous,
    quasiHillDiscriminant,trace_pairCLM,solutionMap_apply,solutionMap_apply]
  rfl

theorem intervalL2Diagonal_continuous (u : Curve ℂ) :
    intervalL2Diagonal (continuousQuasiHillL2 u) = continuousPotentialL2Class (u.prodMk u) := by
  apply intervalL2Representative_injective
  filter_upwards [continuousQuasiHillL2_representative u,
    continuousPotentialL2Class_representative (u.prodMk u)] with x hu hp
  change (continuousQuasiHillL2 u x,continuousQuasiHillL2 u x) = _
  rw [hu,hp]
  rfl

/-- The all-energy rough trace recovers the original square-frequency
normalization, including z=0, without a singular coordinate formula. -/
theorem l2QuasiHillDiscriminant_sq_eq_diagonal (u : IntervalL2) (z : ℂ) :
    l2QuasiHillDiscriminant u (z^2) = l2Discriminant (intervalL2Diagonal u) z := by
  have hcL : Continuous (fun p : ℂ × IntervalL2 => l2QuasiHillDiscriminant p.2 p.1) :=
    analyticOnNhd_l2QuasiHillDiscriminant_joint.continuous
  have hcR : Continuous (fun p : ℂ × IntervalPairL2 => l2Discriminant p.2 p.1) :=
    continuous_l2Discriminant_joint
  have hL : Continuous (fun v : IntervalL2 => l2QuasiHillDiscriminant v (z^2)) :=
    hcL.comp (f := fun v : IntervalL2 => (z^2,v)) (show Continuous (fun v : IntervalL2 => (z^2,v)) from continuous_const.prodMk continuous_id)
  have hR : Continuous (fun v : IntervalL2 => l2Discriminant (intervalL2Diagonal v) z) :=
    hcR.comp (f := fun v : IntervalL2 => (z,intervalL2Diagonal v)) (show Continuous (fun v : IntervalL2 => (z,intervalL2Diagonal v)) from
      continuous_const.prodMk intervalL2Diagonal.continuous)
  have he : (fun v : IntervalL2 => l2QuasiHillDiscriminant v (z^2)) =
      (fun v : IntervalL2 => l2Discriminant (intervalL2Diagonal v) z) := by
    apply denseRange_continuousQuasiHillL2.equalizer hL hR
    funext v
    calc
      l2QuasiHillDiscriminant (continuousQuasiHillL2 v) (z^2) = quasiHillDiscriminant v (z^2) :=
        l2QuasiHillDiscriminant_continuous v (z^2)
      _ = classicalDiscriminant (v.prodMk v) z :=
        quasiHillDiscriminant_eq_ZS v (v.prodMk v) (fun _ => rfl) z
      _ = l2Discriminant (continuousPotentialL2Class (v.prodMk v)) z :=
        (l2Discriminant_of_continuous (v.prodMk v) z).symm
      _ = l2Discriminant (intervalL2Diagonal (continuousQuasiHillL2 v)) z :=
        congrArg (fun p => l2Discriminant p z) (intervalL2Diagonal_continuous v).symm
  exact congrFun he u

end NLS.MKdV
