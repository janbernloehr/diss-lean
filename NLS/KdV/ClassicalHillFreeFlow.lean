import NLS.KdV.HillL2DirichletTerminal

/-! The exact free scalar Hill flow, with the ACTUAL normalized position
and derivative. Its terminal formulas retain the Dirichlet multiplier sign. -/
noncomputable section
open Set Complex NLS.LinearVolterra NLS.Fourier NLS.ZakharovShabat
namespace NLS.KdV

theorem classicalHillFlow_free_sq (z : ℂ) (hz : z ≠ 0) (v : ℂ × ℂ)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    classicalHillFlow 0 (z^2) v t =
      (cos (z*(t:ℂ))*v.1+sin (z*(t:ℂ))/z*v.2,
        -z*sin (z*(t:ℂ))*v.1+cos (z*(t:ℂ))*v.2) := by
  let u : ℝ → ℂ × ℂ := fun x =>
    (cos (z*(x:ℂ))*v.1+sin (z*(x:ℂ))/z*v.2,
      -z*sin (z*(x:ℂ))*v.1+cos (z*(x:ℂ))*v.2)
  have hd (x : ℝ) : HasDerivAt u ((u x).2,-z^2*(u x).1) x := by
    have hs := ((Complex.hasDerivAt_sin (z*(x:ℂ))).comp (x:ℂ)
      ((hasDerivAt_id (x:ℂ)).const_mul z)).comp_ofReal
    have hc := ((Complex.hasDerivAt_cos (z*(x:ℂ))).comp (x:ℂ)
      ((hasDerivAt_id (x:ℂ)).const_mul z)).comp_ofReal
    have hf := (hc.mul_const v.1).add ((hs.div_const z).mul_const v.2)
    have hg := ((hs.const_mul (-z)).mul_const v.1).add (hc.mul_const v.2)
    convert hf.prodMk hg using 1
    · rfl
    · apply Prod.ext
      · dsimp only [u]
        field_simp [hz]
      · dsimp only [u]
        field_simp [hz]
        ring
  have he := solution_unique (classicalHillCoefficientCurve 0 (z^2)) v u
    (by dsimp only [u]; fun_prop) (by simp only [u,ofReal_zero,mul_zero,cos_zero,sin_zero,
      one_mul,zero_div,zero_mul,add_zero,zero_add,Prod.mk.eta]) (by
      intro x _
      simpa only [classicalHillCoefficientCurve,ContinuousMap.coe_mk,
        ContinuousLinearMap.coe_restrictScalars',classicalHillCoefficient_apply,
        ContinuousMap.zero_apply,zero_sub] using hd x.val)
  exact (he ht).symm

theorem classicalHillDirichlet_free_sq (z : ℂ) (hz : z ≠ 0) :
    classicalHillDirichlet 0 (z^2) = sin z/z := by
  rw [classicalHillDirichlet,classicalHillFlow_free_sq z hz _ 1 (by constructor <;> norm_num)]
  simp

theorem classicalHillDirichletTerminal_free_sq (z : ℂ) (hz : z ≠ 0) :
    classicalHillDirichletTerminal 0 (z^2) = cos z := by
  rw [classicalHillDirichletTerminal,classicalHillFlow_free_sq z hz _ 1 (by constructor <;> norm_num)]
  simp

theorem hillL2DirichletTerminal_free_sq (z : ℂ) (hz : z ≠ 0) :
    hillL2DirichletTerminal 0 (z^2) = cos z := by
  have hc : SpectralWeight.one.toCoeff (hillContinuousCoefficients (0 : C(AddCircle (2:ℝ),ℂ))) = 0 := by
    ext k
    simp [hillContinuousCoefficients_apply,fourierCoeff]
  have hcurve : hillUnitPotentialCurve (0 : C(AddCircle (2:ℝ),ℂ)) = 0 := by ext t; rfl
  rw [← hc,hillL2DirichletTerminal_eq_classical,hcurve,classicalHillDirichletTerminal_free_sq z hz]

end NLS.KdV
