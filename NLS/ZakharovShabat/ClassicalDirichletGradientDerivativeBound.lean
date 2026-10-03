import NLS.ZakharovShabat.ClassicalDirichletGradientTimeRegularity

/-! # Uniform time derivative of the normalized Dirichlet error -/

noncomputable section
open Set Complex NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- The normalized free gradient has norm at most one at every real frequency. -/
theorem norm_classicalDirichletNormalizedGradient_free_le (x : ℝ) (t : Icc (0 : ℝ) 1) :
    ‖classicalDirichletNormalizedGradient 0 (x : ℂ) t‖ ≤ 1 := by
  rw [classicalDirichletNormalizedGradient_free]
  norm_num [Prod.norm_def,Complex.norm_exp]

/-- A value error of size A/|n| gives a uniform derivative bound. All
constants depend only on the H¹ bound, root displacement bound, and A. -/
theorem norm_deriv_classicalDirichletGradientError_sobolev_le
    (M B A : ℝ) (hB : 0 ≤ B) (a : Domain 2) (ha : ‖a‖ ≤ M)
    (n : ℤ) (hn : 1 ≤ (n.natAbs : ℝ)) (z : ℂ)
    (hδ : ‖z-(Real.pi : ℂ)*n‖ ≤ B/(n.natAbs : ℝ))
    (hQ : ‖(classicalDirichletNormalization (classicalSobolevPotential a) z)⁻¹‖ ≤ 1)
    (t : Icc (0 : ℝ) 1)
    (hR : ‖classicalDirichletGradientError (classicalSobolevPotential a) z ((Real.pi : ℂ)*n) t‖ ≤
      A/(n.natAbs : ℝ)) :
    ‖deriv (classicalDirichletGradientError (classicalSobolevPotential a) z ((Real.pi : ℂ)*n)) t‖ ≤
      2*(Real.pi+B)*A+2*B+8*M*(Real.exp (4*M+B))^2 := by
  have hM : 0 ≤ M := (norm_nonneg a).trans ha
  have hnpos : 0 < (n.natAbs : ℝ) := by linarith
  have hφ : ‖classicalSobolevPotential a‖ ≤ 4*M := (norm_classicalSobolevPotential_le a).trans (by linarith)
  have hφt : ‖classicalSobolevPotential a t‖ ≤ 4*M :=
    ((classicalSobolevPotential a).norm_coe_le_norm t).trans hφ
  have hδB := hδ.trans (div_le_self hB hn)
  have him : |z.im| ≤ B := by
    simpa using (Complex.abs_im_le_norm (z-(Real.pi : ℂ)*n)).trans hδB
  have hzn : ‖z‖ ≤ (Real.pi+B)*(n.natAbs : ℝ) := by
    have h := norm_le_norm_sub_add z ((Real.pi : ℂ)*n)
    have he : ‖(Real.pi : ℂ)*n‖ = Real.pi*(n.natAbs : ℝ) := by
      simp [Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
    rw [he] at h
    nlinarith
  have hg : ‖classicalDirichletEigenfunction (classicalSobolevPotential a) z t‖ ≤ Real.exp (4*M+B) :=
    norm_classicalSolution_unit_strip_le (4*M) B _ hφ z him (1,1) (by simp) t
  have hf : ‖classicalDirichletNormalizedGradient 0 ((Real.pi : ℂ)*n) t‖ ≤ 1 := by
    simpa using norm_classicalDirichletNormalizedGradient_free_le (Real.pi*n) t
  apply (norm_deriv_classicalDirichletGradientError_le _ _ _ t).trans
  calc
    _ ≤ 2*((Real.pi+B)*(n.natAbs : ℝ))*(A/(n.natAbs : ℝ))+
        2*B*1+2*(Real.exp (4*M+B))^2*1*(4*M) := by gcongr
    _ = _ := by field_simp [hnpos.ne']; ring

end NLS.ZakharovShabat
