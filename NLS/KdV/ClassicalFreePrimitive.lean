import NLS.KdV.ClassicalLocalPrimitive

/-! # Free normalization of the actual Hill primitive

The free scalar potential corresponds to the triangular ZS pair (-1,0),
not to the zero ZS pair. Direct IVP uniqueness and a scalar integrating
factor compute its actual trace. The resulting primitive has precisely
the normalization -i*sqrt(lambda) on the slit plane.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory intervalIntegral NLS.ZakharovShabat
namespace NLS.KdV

theorem classicalSolution_constantUpper_zero_first (z : ℂ) (t : Icc (0 : ℝ) 1) :
    classicalSolution (constantUpperPotential 0) z (1,0) t =
      (exp (-I*z*t.val),0) := by
  have h := classicalSolution_unique (constantUpperPotential 0) z (1,0)
    (fun s : ℝ => (exp (-I*z*s),0)) (by fun_prop) (by simp) (by
      intro s _
      have hd : HasDerivAt (fun r : ℝ => exp (-I*z*r))
          (exp (-I*z*s.val)*(-I*z)) s.val := by
        simpa using (Complex.ofRealCLM.hasDerivAt.const_mul (-I*z)).cexp
      have hp := hd.prodMk (hasDerivAt_const s.val (0 : ℂ))
      convert! hp using 1
      simp only [classicalODECoefficient_apply,constantUpperPotential_apply,
        ContinuousMap.zero_apply,mul_zero,add_zero]
      apply Prod.ext <;> dsimp <;> ring)
  exact (h t.property).symm

theorem classicalSolution_constantUpper_zero_snd (z : ℂ) (v : ℂ × ℂ)
    (t : Icc (0 : ℝ) 1) :
    (classicalSolution (constantUpperPotential 0) z v t).2 = exp (I*z*t.val)*v.2 := by
  let Y : ℝ → ℂ := fun s => exp (-I*z*s)*(classicalSolution (constantUpperPotential 0) z v s).2
  have hc : Continuous Y := by
    exact (by fun_prop : Continuous (fun s : ℝ => exp (-I*z*s))).mul
      (continuous_classicalSolution (constantUpperPotential 0) z v).snd
  have hd (s : Icc (0 : ℝ) 1) : HasDerivAt Y 0 s.val := by
    have he : HasDerivAt (fun r : ℝ => exp (-I*z*r))
        (exp (-I*z*s.val)*(-I*z)) s.val := by
      simpa using (Complex.ofRealCLM.hasDerivAt.const_mul (-I*z)).cexp
    have hs := HasFDerivAt.hasDerivAt (hasDerivAt_classicalSolution (constantUpperPotential 0) z v s).snd
    have hp := he.mul hs
    convert! hp using 1
    simp only [classicalODECoefficient_apply,constantUpperPotential_apply,ContinuousMap.zero_apply]
    dsimp
    ring
  have hi := integral_eq_sub_of_hasDerivAt_of_le t.property.1 hc.continuousOn
    (fun s (hs : s ∈ Ioo (0 : ℝ) t.val) => hd ⟨s,hs.1.le,hs.2.le.trans t.property.2⟩)
    (continuous_const.intervalIntegrable (0 : ℝ) t.val)
  have hy : Y t.val = v.2 := by
    have hzero : Y t.val-Y 0 = 0 := by simpa only [intervalIntegral.integral_zero] using hi.symm
    simpa [Y] using sub_eq_zero.mp hzero
  have hmul := congrArg (fun c : ℂ => exp (I*z*t.val)*c) hy
  have he : exp (I*z*t.val)*exp (-I*z*t.val) = 1 := by
    rw [← exp_add]
    rw [show I*z*t.val+(-I*z*t.val) = 0 by ring,exp_zero]
  dsimp only [Y] at hmul
  rwa [← mul_assoc,he,one_mul] at hmul

/-- The actual free Hill trace, for the nonzero triangular ZS pair. -/
theorem classicalDiscriminant_constantUpper_zero (z : ℂ) :
    classicalDiscriminant (constantUpperPotential 0) z = 2*cos z := by
  let t : Icc (0 : ℝ) 1 := ⟨1,by constructor <;> norm_num⟩
  have h1 := classicalSolution_constantUpper_zero_first z t
  have h2 := classicalSolution_constantUpper_zero_snd z (0,1) t
  simp only [classicalDiscriminant,classicalMonodromy,classicalFundamentalMatrix,Matrix.trace_fin_two_of]
  rw [h1,h2]
  simp only [t,ofReal_one,mul_one]
  rw [Complex.two_cos,add_comm]
  congr 1 <;> congr 1 <;> ring

@[simp] theorem classicalHillDiscriminant_zero (lam : ℂ) :
    classicalHillDiscriminant 0 lam = 2*cos (Complex.sqrt lam) :=
  classicalDiscriminant_constantUpper_zero _

/-- Free normalized primitive on the energy slit plane. -/
def classicalHillFreePrimitive (lam : ℂ) : ℂ := -I*Complex.sqrt lam

/-- Its canonical radicand root, with the same sheet as the primitive. -/
def classicalHillFreeRoot (lam : ℂ) : ℂ := 2*sinh (classicalHillFreePrimitive lam)

theorem analyticOnNhd_classicalHillFreePrimitive :
    AnalyticOnNhd ℂ classicalHillFreePrimitive slitPlane := by
  intro lam hlam
  exact analyticAt_const.mul (Complex.differentiableOn_sqrt.analyticAt
    (isOpen_slitPlane.mem_nhds hlam))

theorem analyticOnNhd_classicalHillFreeRoot :
    AnalyticOnNhd ℂ classicalHillFreeRoot slitPlane := by
  intro lam hlam
  exact analyticAt_const.mul (Complex.analyticAt_sinh.comp
    (analyticOnNhd_classicalHillFreePrimitive lam hlam))

theorem two_cosh_classicalHillFreePrimitive (lam : ℂ) :
    2*cosh (classicalHillFreePrimitive lam) = classicalHillDiscriminant 0 lam := by
  rw [classicalHillDiscriminant_zero]
  simp only [classicalHillFreePrimitive,neg_mul,cosh_neg]
  rw [mul_comm I,cosh_mul_I]

theorem classicalHillFreeRoot_sq (lam : ℂ) :
    classicalHillFreeRoot lam ^ 2 = classicalHillRadicand (lam,0) := by
  dsimp only [classicalHillRadicand]
  rw [← two_cosh_classicalHillFreePrimitive]
  dsimp only [classicalHillFreeRoot]
  linear_combination -4*cosh_sq_sub_sinh_sq (classicalHillFreePrimitive lam)

theorem exp_classicalHillFreePrimitive (lam : ℂ) :
    exp (classicalHillFreePrimitive lam) =
      (classicalHillDiscriminant 0 lam+classicalHillFreeRoot lam)/2 := by
  rw [← two_cosh_classicalHillFreePrimitive]
  dsimp only [classicalHillFreeRoot]
  rw [← cosh_add_sinh]
  ring

end NLS.KdV
