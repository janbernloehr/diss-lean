import NLS.MKdV.QuasiHillJointAnalytic
import NLS.ZakharovShabat.ClassicalBoundaryDeterminants

/-! # The actual independent quasi-Hill fundamental matrix

The original Volterra columns have Wronskian one and propagate arbitrary
initial vectors. These identities hold at every complex energy, including
zero, with only continuity of the profile.
-/
noncomputable section
open Set Complex Matrix MeasureTheory intervalIntegral
open NLS.LinearVolterra NLS.ZakharovShabat
namespace NLS.MKdV

def quasiHillFundamentalMatrix (U : Curve ℂ) (E : ℂ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(quasiHillSolution U E (1,0) t).1,(quasiHillSolution U E (0,1) t).1;
    (quasiHillSolution U E (1,0) t).2,(quasiHillSolution U E (0,1) t).2]

@[simp] theorem quasiHillFundamentalMatrix_zero (U : Curve ℂ) (E : ℂ) :
    quasiHillFundamentalMatrix U E 0 = 1 := by
  simp [quasiHillFundamentalMatrix,Matrix.one_fin_two]

theorem quasiHillSolution_eq_columns (U : Curve ℂ) (E : ℂ) (v : ℂ × ℂ) (t : Icc (0:ℝ) 1) :
    quasiHillSolution U E v t = v.1 • quasiHillSolution U E (1,0) t+v.2 • quasiHillSolution U E (0,1) t := by
  have hv : v = v.1 • (1,0)+v.2 • (0,1) := by simp
  have h := congrArg (solutionMap (quasiHillCoefficientCurve U E) t) hv
  rw [map_add,map_smul,map_smul] at h
  simpa only [solutionMap_apply,quasiHillSolution] using h

theorem quasiHillFundamentalMatrix_mulVec (U : Curve ℂ) (E : ℂ) (v : Fin 2 → ℂ) (t : Icc (0:ℝ) 1) :
    quasiHillFundamentalMatrix U E t *ᵥ v =
      ![(quasiHillSolution U E (v 0,v 1) t).1,(quasiHillSolution U E (v 0,v 1) t).2] := by
  rw [quasiHillSolution_eq_columns]
  ext i
  fin_cases i <;> simp [quasiHillFundamentalMatrix,Matrix.mulVec,Matrix.vecHead,Matrix.vecTail,smul_eq_mul] <;> ring

theorem hasDerivAt_det_quasiHillFundamentalMatrix (U : Curve ℂ) (E : ℂ) (t : Icc (0:ℝ) 1) :
    HasDerivAt (fun s => (quasiHillFundamentalMatrix U E s).det) 0 t := by
  have h₁ := hasDerivAt_quasiHillSolution U E (1,0) t
  have h₂ := hasDerivAt_quasiHillSolution U E (0,1) t
  have h := ((HasFDerivAt.hasDerivAt h₁.fst).mul (HasFDerivAt.hasDerivAt h₂.snd)).sub
    ((HasFDerivAt.hasDerivAt h₂.fst).mul (HasFDerivAt.hasDerivAt h₁.snd))
  simp only [quasiHillCoefficient_apply] at h
  have hz := h.congr_deriv (show _ = (0:ℂ) by
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.toSpanSingleton_apply,one_smul]
    dsimp
    ring)
  simp only [quasiHillFundamentalMatrix,Matrix.det_fin_two_of]
  convert! hz using 1

theorem det_quasiHillFundamentalMatrix (U : Curve ℂ) (E : ℂ) (t : Icc (0:ℝ) 1) :
    (quasiHillFundamentalMatrix U E t).det = 1 := by
  have hc : Continuous (fun s => (quasiHillFundamentalMatrix U E s).det) := by
    simp only [quasiHillFundamentalMatrix,Matrix.det_fin_two]
    exact ((continuous_solution _ _).fst.mul (continuous_solution _ _).snd).sub
      ((continuous_solution _ _).fst.mul (continuous_solution _ _).snd)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le t.property.1 hc.continuousOn
    (fun s (hs : s ∈ Ioo (0:ℝ) t.val) =>
      hasDerivAt_det_quasiHillFundamentalMatrix U E ⟨s,hs.1.le,hs.2.le.trans t.property.2⟩)
    (continuous_const.intervalIntegrable (0:ℝ) t.val)
  have he : (quasiHillFundamentalMatrix U E t).det-1 = 0 := by
    simpa only [intervalIntegral.integral_zero,quasiHillFundamentalMatrix_zero,Matrix.det_one] using hi.symm
  exact sub_eq_zero.mp he

theorem quasiHillFundamentalMatrix_trace_one (U : Curve ℂ) (E : ℂ) :
    (quasiHillFundamentalMatrix U E 1).trace = quasiHillDiscriminant U E := by
  simp only [quasiHillDiscriminant,trace_pairCLM,solutionMap_apply,quasiHillFundamentalMatrix,Matrix.trace_fin_two]
  rfl

end NLS.MKdV
