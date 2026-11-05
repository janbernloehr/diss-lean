import NLS.MKdV.MiuraL2DirichletTerminal

/-! The trace and prescribed difference of actual diagonal fundamental entries.
The determinant-one identity identifies both from the nonzero Dirichlet
terminal quasi-derivative at a characteristic zero. -/
noncomputable section
open Set Complex NLS.LinearVolterra NLS.ZakharovShabat NLS.KdV
namespace NLS.MKdV

theorem hillMiuraL2Discriminant_eq_quasiHillL2_trace (u : Coeff 2) (lambda : ℂ) :
    hillMiuraL2Discriminant u lambda =
      (quasiHillL2SolutionCurve u lambda (1,0) ⟨1,by constructor <;> norm_num⟩).1+
        quasiHillL2DirichletTerminal u lambda := by
  have hm : Continuous (fun a : Coeff 2 => (lambda,a)) := continuous_const.prodMk continuous_id
  have hc : Continuous (fun a : Coeff 2 => hillMiuraL2Discriminant a lambda) := by
    have h : Continuous (fun p : ℂ × Coeff 2 => hillMiuraL2Discriminant p.2 p.1) :=
      analyticOnNhd_hillMiuraL2Discriminant_joint.continuous
    simpa only [Function.comp_def] using h.comp hm
  have hs (v : ℂ × ℂ) : Continuous (fun a : Coeff 2 =>
      quasiHillL2SolutionCurve a lambda v (⟨1,by constructor <;> norm_num⟩ : Icc (0:ℝ) 1)) := by
    have h : Continuous (fun p : ℂ × Coeff 2 => quasiHillL2SolutionCurve p.2 p.1 v) :=
      (analyticOnNhd_quasiHillL2SolutionCurve_joint v).continuous
    exact (ContinuousMap.evalCLM ℂ (⟨1,by constructor <;> norm_num⟩ : Icc (0:ℝ) 1)).continuous.comp
      (h.comp hm)
  have he := (scalarInclusion_denseRange (p := 2) (by simp)).equalizer hc
    ((continuous_fst.comp (hs (1,0))).add (continuous_snd.comp (hs (0,1)))) (by
      funext a
      change hillMiuraL2Discriminant (scalarInclusion a) lambda =
        (quasiHillL2SolutionCurve (scalarInclusion a) lambda (1,0) ⟨1,by constructor <;> norm_num⟩).1+
          (quasiHillL2SolutionCurve (scalarInclusion a) lambda (0,1) ⟨1,by constructor <;> norm_num⟩).2
      rw [hillMiuraL2Discriminant_scalarInclusion,hillL2Discriminant_miura,
        quasiHillL2SolutionCurve_scalarInclusion,quasiHillL2SolutionCurve_scalarInclusion]
      simp only [quasiHillDiscriminant,trace_pairCLM,solutionMap_apply,quasiHillSolution])
  exact congrFun he u

/-- The actual Dirichlet monodromy sheet, before any choice of square root. -/
def quasiHillL2DirichletSheet (u : Coeff 2) (lambda : ℂ) : ℂ :=
  (quasiHillL2SolutionCurve u lambda (1,0) ⟨1,by constructor <;> norm_num⟩).1-
    quasiHillL2DirichletTerminal u lambda

theorem quasiHillL2Dirichlet_first_diagonal_of_root (u : Coeff 2) (lambda : ℂ)
    (hz : quasiHillL2Dirichlet u lambda = 0) :
    (quasiHillL2SolutionCurve u lambda (1,0) ⟨1,by constructor <;> norm_num⟩).1 =
      (quasiHillL2DirichletTerminal u lambda)⁻¹ := by
  have hd := quasiHillL2_fundamental_determinant u lambda
  change _*quasiHillL2DirichletTerminal u lambda-_*quasiHillL2Dirichlet u lambda = 1 at hd
  rw [hz,mul_zero,sub_zero] at hd
  have hn := quasiHillL2DirichletTerminal_ne_zero u lambda hz
  apply (mul_right_cancel₀ hn)
  rw [hd,inv_mul_cancel₀ hn]

theorem quasiHillL2DirichletSheet_of_root (u : Coeff 2) (lambda : ℂ)
    (hz : quasiHillL2Dirichlet u lambda = 0) :
    quasiHillL2DirichletSheet u lambda =
      (quasiHillL2DirichletTerminal u lambda)⁻¹-quasiHillL2DirichletTerminal u lambda := by
  rw [quasiHillL2DirichletSheet,quasiHillL2Dirichlet_first_diagonal_of_root u lambda hz]

theorem hillMiuraL2Discriminant_of_dirichlet_root (u : Coeff 2) (lambda : ℂ)
    (hz : quasiHillL2Dirichlet u lambda = 0) :
    hillMiuraL2Discriminant u lambda =
      (quasiHillL2DirichletTerminal u lambda)⁻¹+quasiHillL2DirichletTerminal u lambda := by
  rw [hillMiuraL2Discriminant_eq_quasiHillL2_trace,
    quasiHillL2Dirichlet_first_diagonal_of_root u lambda hz]

theorem quasiHillL2DirichletSheet_sq (u : Coeff 2) (lambda : ℂ)
    (hz : quasiHillL2Dirichlet u lambda = 0) :
    (quasiHillL2DirichletSheet u lambda)^2 = (hillMiuraL2Discriminant u lambda)^2-4 := by
  rw [quasiHillL2DirichletSheet_of_root u lambda hz,
    hillMiuraL2Discriminant_of_dirichlet_root u lambda hz]
  have hn := quasiHillL2DirichletTerminal_ne_zero u lambda hz
  field_simp
  ring

end NLS.MKdV
