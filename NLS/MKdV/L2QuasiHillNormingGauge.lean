import NLS.MKdV.L2QuasiHillDirichletGauge

/-! # Actual terminal norming factors in the rotated NLS Dirichlet problem

At a nonzero Dirichlet frequency the terminal NLS eigenfunction factor
is the normalized rough Hill quasi-derivative. Determinant one then
identifies the anti-discriminant with gamma-gamma^-1.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open NLS.LinearVolterra NLS.ZakharovShabat
namespace NLS.MKdV

theorem dirichlet_matrix_antiTrace (a b c d s : ℂ)
    (h1 : a+b = s) (h2 : c+d = s) (hdet : a*d-b*c = 1) :
    s ≠ 0 ∧ b+c = s-s⁻¹ := by
  have ha : a = s-b := by linear_combination h1
  have hd : d = s-c := by linear_combination h2
  rw [ha,hd] at hdet
  have hs : s ≠ 0 := by intro h; rw [h] at hdet; ring_nf at hdet; exact zero_ne_one hdet
  refine ⟨hs,?_⟩
  field_simp [hs]
  linear_combination -hdet

theorem l2QuasiHillMomentum_eq_dirichletMiura_factor (u : IntervalL2) (z : ℂ) (hz : z ≠ 0)
    (hzero : l2SeparatedCharacteristic .dirichlet (intervalL2DirichletMiura u) z = 0) :
    extend (l2QuasiHillMomentum u (z^2) (0,1)) 1 =
      (l2SolutionCurve (intervalL2DirichletMiura u) z (1,1) ⟨1,by constructor <;> norm_num⟩).1 := by
  let t : Icc (0 : ℝ) 1 := ⟨1,by constructor <;> norm_num⟩
  let F := l2SolutionCurve (intervalL2DirichletMiura u) z (1,1)
  have hb : (F t).1 = (F t).2 := by
    simpa only [BoundaryCondition.extensionSign,one_mul] using
      (l2SeparatedCharacteristic_eq_zero_iff .dirichlet _ z).mp hzero
  have he := congrArg (fun f : Curve (ℂ × ℂ) => (f t).2)
    (l2QuasiHillSolution_eq_dirichletMiura u z (1,1))
  have hinit : dirichletMiuraState z (1,1) = (-2*I*z) • ((0,1) : ℂ × ℂ) := by
    apply Prod.ext <;> simp only [dirichletMiuraState_apply,Prod.smul_fst,Prod.smul_snd,smul_eq_mul] <;> ring
  rw [hinit,l2QuasiHillSolution_smul_initial] at he
  have hh : (-2*I*z)*extend (l2QuasiHillMomentum u (z^2) (0,1)) 1 = -I*z*((F t).1+(F t).2) := by
    rw [extend_coe _ t]
    exact he
  have hn : (-2*I*z : ℂ) ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero) hz
  apply (mul_left_cancel₀ hn)
  rw [hh,← hb]
  ring

theorem l2AntiDiscriminant_dirichletMiura (u : IntervalL2) (z : ℂ) (hz : z ≠ 0)
    (hzero : l2SeparatedCharacteristic .dirichlet (intervalL2DirichletMiura u) z = 0) :
    l2AntiDiscriminant (intervalL2DirichletMiura u) z =
      extend (l2QuasiHillMomentum u (z^2) (0,1)) 1-
        (extend (l2QuasiHillMomentum u (z^2) (0,1)) 1)⁻¹ := by
  let U := intervalL2DirichletMiura u
  let t : Icc (0 : ℝ) 1 := ⟨1,by constructor <;> norm_num⟩
  let F := l2SolutionCurve U z (1,1)
  have hb : (F t).1 = (F t).2 := by
    simpa only [BoundaryCondition.extensionSign,one_mul] using
      (l2SeparatedCharacteristic_eq_zero_iff .dirichlet U z).mp hzero
  have hlin := congrArg (fun f : Curve (ℂ × ℂ) => f t) (l2SolutionCurve_linearCombination U z (1,1))
  have h1 : (l2Monodromy U z) 0 0+(l2Monodromy U z) 0 1 = (F t).1 := by
    simpa only [l2Monodromy,l2FundamentalMatrix,ContinuousMap.add_apply,ContinuousMap.smul_apply,
      Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,one_mul,
      Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one] using (congrArg Prod.fst hlin).symm
  have h2 : (l2Monodromy U z) 1 0+(l2Monodromy U z) 1 1 = (F t).1 := by
    have hh := (congrArg Prod.snd hlin).symm.trans hb.symm
    simpa only [l2Monodromy,l2FundamentalMatrix,ContinuousMap.add_apply,ContinuousMap.smul_apply,
      Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,one_mul,
      Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one] using hh
  have hd : (l2Monodromy U z) 0 0*(l2Monodromy U z) 1 1-
      (l2Monodromy U z) 0 1*(l2Monodromy U z) 1 0 = 1 := by
    simpa only [l2Monodromy,Matrix.det_fin_two] using det_l2FundamentalMatrix U z t
  have hm := (dirichlet_matrix_antiTrace _ _ _ _ _ h1 h2 hd).2
  rw [l2QuasiHillMomentum_eq_dirichletMiura_factor u z hz hzero]
  exact hm

end NLS.MKdV
