import NLS.MKdV.L2QuasiHillFreeSolution

/-! # The actual cosine-normalized free rough Hill solution -/
noncomputable section
set_option autoImplicit false
open Set Complex
open NLS.LinearVolterra NLS.ZakharovShabat NLS.KdV
namespace NLS.MKdV

theorem l2QuasiHillSolution_zero_profile_cosine (z : ℂ) (t : Icc (0 : ℝ) 1) :
    l2QuasiHillSolution 0 (z^2) (1,0) t = (cos (z*t.val),-z*sin (z*t.val)) := by
  rw [l2QuasiHillSolution_zero_profile]
  apply Eq.symm
  apply solution_unique (classicalHillCoefficientCurve 0 (z^2)) (1,0)
    (fun x : ℝ => (cos (z*x),-z*sin (z*x))) (by fun_prop) (by simp) _ t.property
  intro s _
  have harg : HasDerivAt (fun w : ℂ => z*w) z (s.val : ℂ) := by
    convert! (hasDerivAt_id (s.val : ℂ)).const_mul z using 1
    ring
  have hcos := harg.ccos.comp_ofReal
  have hsin := (harg.csin.const_mul (-z)).comp_ofReal
  change HasDerivAt (fun x : ℝ => (cos (z*x),-z*sin (z*x)))
    (-z*sin (z*s.val),(0-z^2)*cos (z*s.val)) s.val
  convert! hcos.prodMk hsin using 1
  apply Prod.ext <;> dsimp <;> ring

theorem l2QuasiHillPosition_zero_profile_cosine (z : ℂ) (t : Icc (0 : ℝ) 1) :
    l2QuasiHillPosition 0 (z^2) (1,0) t = cos (z*t.val) := by
  change (l2QuasiHillSolution 0 (z^2) (1,0) t).1 = _
  rw [l2QuasiHillSolution_zero_profile_cosine]

theorem l2QuasiHillMomentum_zero_profile_cosine (z : ℂ) (t : Icc (0 : ℝ) 1) :
    l2QuasiHillMomentum 0 (z^2) (1,0) t = -z*sin (z*t.val) := by
  change (l2QuasiHillSolution 0 (z^2) (1,0) t).2 = _
  rw [l2QuasiHillSolution_zero_profile_cosine]

end NLS.MKdV
