import NLS.MKdV.QuasiHillFundamentalMatrix
import NLS.MKdV.QuasiHillDirichletCharacteristic

/-! # Energy regularity and scalar exclusion for the actual quasi-Hill monodromy

The original Volterra columns are entire in energy. Differentiating their
unit determinant excludes scalar monodromy whenever the actual trace has
nonzero energy derivative.
-/
noncomputable section
open Set Complex Matrix NLS.LinearVolterra
namespace NLS.MKdV

theorem analyticAt_quasiHillFundamentalMatrix_entry (U : Curve ℂ) (E : ℂ)
    (t : Icc (0:ℝ) 1) (i j : Fin 2) :
    AnalyticAt ℂ (fun w => quasiHillFundamentalMatrix U w t i j) E := by
  have h1 := (analyticOnNhd_solution_coefficient (E := ℂ × ℂ) (1,0)
    t (quasiHillCoefficientCurve U E) (mem_univ _)).comp
      (analyticAt_quasiHillCoefficientCurve U E)
  have h2 := (analyticOnNhd_solution_coefficient (E := ℂ × ℂ) (0,1)
    t (quasiHillCoefficientCurve U E) (mem_univ _)).comp
      (analyticAt_quasiHillCoefficientCurve U E)
  fin_cases i <;> fin_cases j
  · exact analyticAt_fst.comp h1
  · exact analyticAt_fst.comp h2
  · exact analyticAt_snd.comp h1
  · exact analyticAt_snd.comp h2

theorem deriv_quasiHillDiscriminant_eq_zero_of_scalar_monodromy
    (U : Curve ℂ) (E ε : ℂ) (hε : ε ≠ 0)
    (hM : quasiHillFundamentalMatrix U E 1 = !![ε,0;0,ε]) :
    deriv (quasiHillDiscriminant U) E = 0 := by
  let t : Icc (0:ℝ) 1 := ⟨1,by norm_num⟩
  let M : ℂ → Matrix (Fin 2) (Fin 2) ℂ := fun w => quasiHillFundamentalMatrix U w t
  have hd (i j : Fin 2) := (analyticAt_quasiHillFundamentalMatrix_entry U E t i j).differentiableAt.hasDerivAt
  have hdet := ((hd 0 0).mul (hd 1 1)).sub ((hd 0 1).mul (hd 1 0))
  have heq : (fun w => M w 0 0*M w 1 1-M w 0 1*M w 1 0) = fun _ => (1:ℂ) := by
    funext w
    exact (Matrix.det_fin_two (M w)).symm.trans (det_quasiHillFundamentalMatrix U w t)
  change HasDerivAt (fun w => M w 0 0*M w 1 1-M w 0 1*M w 1 0) _ E at hdet
  have hzero := hdet.deriv
  rw [heq,deriv_const] at hzero
  have hME : M E = !![ε,0;0,ε] := hM
  change 0 = deriv (fun w => M w 0 0) E*M E 1 1+M E 0 0*deriv (fun w => M w 1 1) E-
    (deriv (fun w => M w 0 1) E*M E 1 0+M E 0 1*deriv (fun w => M w 1 0) E) at hzero
  rw [hME] at hzero
  change 0 = deriv (fun w => M w 0 0) E*ε+ε*deriv (fun w => M w 1 1) E-
    (deriv (fun w => M w 0 1) E*0+0*deriv (fun w => M w 1 0) E) at hzero
  have hsum : deriv (fun w => M w 0 0) E+deriv (fun w => M w 1 1) E = 0 := by
    apply (mul_eq_zero.mp (show ε*(deriv (fun w => M w 0 0) E+deriv (fun w => M w 1 1) E) = 0 by
      linear_combination -hzero)).resolve_left hε
  have htrace := ((hd 0 0).add (hd 1 1)).deriv
  have hfun : (fun w => M w 0 0+M w 1 1) = quasiHillDiscriminant U := by
    funext w
    exact (Matrix.trace_fin_two (M w)).symm.trans (quasiHillFundamentalMatrix_trace_one U w)
  change deriv (fun w => M w 0 0+M w 1 1) E =
    deriv (fun w => M w 0 0) E+deriv (fun w => M w 1 1) E at htrace
  rw [hfun] at htrace
  exact htrace.trans hsum

theorem quasiHillMonodromy_parabolic_of_Dirichlet_trace
    (U : Curve ℂ) (E ε : ℂ) (hε : ε^2 = 1)
    (hD : quasiHillDirichletCharacteristic U E = 0)
    (htrace : quasiHillDiscriminant U E = 2*ε) :
    quasiHillFundamentalMatrix U E 1 =
      !![ε,0;quasiHillFundamentalMatrix U E 1 1 0,ε] := by
  let M := quasiHillFundamentalMatrix U E 1
  have hdet := det_quasiHillFundamentalMatrix U E ⟨1,by norm_num⟩
  have ht := (quasiHillFundamentalMatrix_trace_one U E).trans htrace
  have h01 : M 0 1 = 0 := hD
  change M.det = 1 at hdet
  change M.trace = 2*ε at ht
  rw [Matrix.det_fin_two,h01,zero_mul,sub_zero] at hdet
  rw [Matrix.trace_fin_two] at ht
  have hsq : (M 0 0-ε)^2 = 0 := by
    linear_combination -(hdet)+(M 0 0)*ht+hε
  have h00 : M 0 0 = ε := sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)
  have h11 : M 1 1 = ε := by linear_combination ht-h00
  change M = _
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · rfl
  · exact h11

theorem quasiHillMonodromy_lower_ne_zero_of_Dirichlet_trace_deriv
    (U : Curve ℂ) (E ε : ℂ) (hε : ε^2 = 1)
    (hD : quasiHillDirichletCharacteristic U E = 0)
    (htrace : quasiHillDiscriminant U E = 2*ε)
    (hd : deriv (quasiHillDiscriminant U) E ≠ 0) :
    quasiHillFundamentalMatrix U E 1 1 0 ≠ 0 := by
  intro hc
  have hM := quasiHillMonodromy_parabolic_of_Dirichlet_trace U E ε hε hD htrace
  rw [hc] at hM
  have he : ε ≠ 0 := by intro he;simp [he] at hε
  exact hd (deriv_quasiHillDiscriminant_eq_zero_of_scalar_monodromy U E ε he hM)

end NLS.MKdV
