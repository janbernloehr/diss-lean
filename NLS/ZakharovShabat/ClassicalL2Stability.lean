import NLS.ZakharovShabat.ContinuousPotentialL2Class
import NLS.ZakharovShabat.ClassicalSolutionGrowth
import NLS.ZakharovShabat.ClassicalChainOperator
import NLS.FunctionalAnalysis.VariableIntegralGronwall

/-! # Stability of actual fundamental solutions in the L2 potential distance

The constants are uniform in time and on L2-bounded potential sets. These
estimates construct the L2 extension; the sharper weighted Hermitian G.1
estimate is retained separately for passage to the limit.
-/
noncomputable section
open Set Complex MeasureTheory
open NLS.LinearVolterra NLS.FunctionalAnalysis
namespace NLS.ZakharovShabat

/-- The actual L1 potential norm on any truncated interval is bounded by
its Hilbert L2 norm on the unit interval. -/
theorem integral_potential_norm_le_L2 (φ : Curve (ℂ × ℂ)) (t : Icc (0:ℝ) 1) :
    (∫ s in (0:ℝ)..t.val, ‖extend φ s‖) ≤ classicalPotentialL2Norm φ := by
  have h := integral_mul_le_sqrt_sq_mul_sqrt_sq (fun s => ‖extend φ s‖) (fun _ => 1)
    (continuous_extend φ).norm continuous_const t t.property.1
    (fun s _ => norm_nonneg _) (by intros; norm_num)
  simp only [mul_one,one_pow,intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_one] at h
  exact h.trans ((mul_le_mul_of_nonneg_left (Real.sqrt_le_one.mpr t.property.2) (Real.sqrt_nonneg _)).trans
    (by simpa only [mul_one] using sqrt_integral_potential_norm_sq_le φ t))

/-- An integral bound for the actual ODE coefficient, uniform in time. -/
theorem integral_classicalCoefficient_norm_budget (φ : Curve (ℂ × ℂ)) (z : ℂ)
    (t : Icc (0:ℝ) 1) :
    (∫ s in (0:ℝ)..t.val, ‖z‖+‖extend φ s‖) ≤ ‖z‖+classicalPotentialL2Norm φ := by
  rw [intervalIntegral.integral_add (continuous_const.intervalIntegrable 0 t)
    ((continuous_extend φ).norm.intervalIntegrable 0 t)]
  simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul]
  exact add_le_add (mul_le_of_le_one_left (norm_nonneg _) t.property.2) (integral_potential_norm_le_L2 φ t)

/-- Growth depends on the L2 potential norm, not its supremum. -/
theorem norm_classicalSolution_le_exp_L2 (φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ)
    (t : Icc (0:ℝ) 1) :
    ‖classicalSolution φ z v t‖ ≤ ‖v‖*Real.exp (‖z‖+classicalPotentialL2Norm φ) := by
  have h := norm_le_exp_integral_of_norm_deriv_le
    (f := classicalSolution φ z v)
    (f' := fun s => classicalODECoefficient (extend φ s) z (classicalSolution φ z v s))
    (α := fun s => ‖z‖+‖extend φ s‖) (a := 0) (b := 1)
    (continuous_classicalSolution φ z v).continuousOn (by
      intro s hs
      have hs' : s ∈ Icc (0:ℝ) 1 := ⟨hs.1,hs.2.le⟩
      simpa only [NLS.LinearVolterra.extend,projIcc_of_mem _ hs'] using
        (hasDerivAt_classicalSolution φ z v ⟨s,hs'⟩).hasDerivWithinAt)
    (continuous_const.add (continuous_extend φ).norm)
    (fun s _ => norm_classicalODECoefficient_apply_le _ _ _)
  have hh := h t t.property
  rw [classicalSolution_zero] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (integral_classicalCoefficient_norm_budget φ z t)) (norm_nonneg _))

/-- The potential difference enters the actual ODE linearly with no spectral term. -/
theorem classicalODECoefficient_sub_apply (φ ψ u v : ℂ × ℂ) (z : ℂ) :
    classicalODECoefficient φ z u-classicalODECoefficient ψ z v =
      classicalODECoefficient φ z (u-v)+classicalODECoefficient (φ-ψ) 0 v := by
  ext <;> simp [classicalODECoefficient_apply] <;> ring

/-- Pointwise stability of the actual solutions in the Hilbert L2 potential distance. -/
theorem norm_classicalSolution_sub_le_L2 (φ ψ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ)
    (t : Icc (0:ℝ) 1) :
    ‖classicalSolution φ z v t-classicalSolution ψ z v t‖ ≤
      ‖v‖*Real.exp (2*‖z‖+classicalPotentialL2Norm φ+classicalPotentialL2Norm ψ)*
        classicalPotentialL2Norm (φ-ψ) := by
  let u (s : ℝ) := classicalSolution φ z v s-classicalSolution ψ z v s
  let g (s : ℝ) := classicalODECoefficient (extend φ s) z (classicalSolution φ z v s)-
    classicalODECoefficient (extend ψ s) z (classicalSolution ψ z v s)
  let a (s : ℝ) := ‖z‖+‖extend φ s‖
  let C := ‖v‖*Real.exp (‖z‖+classicalPotentialL2Norm ψ)
  let D := classicalPotentialL2Norm (φ-ψ)
  have hu : Continuous u := (continuous_classicalSolution φ z v).sub (continuous_classicalSolution ψ z v)
  have hg : Continuous g := by
    have hφ := continuous_extend φ
    have hψ := continuous_extend ψ
    have hU := continuous_classicalSolution φ z v
    have hV := continuous_classicalSolution ψ z v
    dsimp only [g,classicalODECoefficient_apply]
    exact ((continuous_const.mul hU.fst).add ((continuous_const.mul hφ.fst).mul hU.snd)).prodMk
      (((continuous_const.mul hφ.snd).mul hU.fst).add (continuous_const.mul hU.snd)) |>.sub
      (((continuous_const.mul hV.fst).add ((continuous_const.mul hψ.fst).mul hV.snd)).prodMk
        (((continuous_const.mul hψ.snd).mul hV.fst).add (continuous_const.mul hV.snd)))
  have ha : Continuous a := continuous_const.add (continuous_extend φ).norm
  have hC : 0 ≤ C := mul_nonneg (norm_nonneg _) (Real.exp_nonneg _)
  have hD : 0 ≤ D := Real.sqrt_nonneg _
  have hbound (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      ‖u s‖ ≤ C*D+∫ r in (0:ℝ)..s, a r*‖u r‖ := by
    have hi : (∫ r in (0:ℝ)..s, g r) = u s := by
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs.1 hu.continuousOn (fun r hr => by
        have hr' : r ∈ Icc (0:ℝ) 1 := ⟨hr.1.le,hr.2.le.trans hs.2⟩
        simpa only [g,u,Pi.sub_def,NLS.LinearVolterra.extend,projIcc_of_mem _ hr'] using
          (hasDerivAt_classicalSolution φ z v ⟨r,hr'⟩).sub
            (hasDerivAt_classicalSolution ψ z v ⟨r,hr'⟩)) (hg.intervalIntegrable 0 s)
      simpa only [u,classicalSolution_zero,sub_self,sub_zero] using h
    have hm : ‖∫ r in (0:ℝ)..s, g r‖ ≤
        ∫ r in (0:ℝ)..s, a r*‖u r‖+‖extend (φ-ψ) r‖*C := by
      apply intervalIntegral.norm_integral_le_of_norm_le hs.1
      · filter_upwards [] with r hr
        have hr' : r ∈ Icc (0:ℝ) 1 := ⟨hr.1.le,hr.2.trans hs.2⟩
        have he := norm_classicalSolution_le_exp_L2 ψ z v ⟨r,hr'⟩
        have hp := norm_classicalODECoefficient_apply_le (extend φ r-extend ψ r) 0
          (classicalSolution ψ z v r)
        simp only [norm_zero,zero_add] at hp
        dsimp only [g]
        rw [classicalODECoefficient_sub_apply]
        apply (norm_add_le _ _).trans
        exact add_le_add (norm_classicalODECoefficient_apply_le _ _ _)
          (hp.trans (mul_le_mul_of_nonneg_left he (norm_nonneg _)))
      · exact ((ha.mul hu.norm).add ((continuous_extend (φ-ψ)).norm.mul continuous_const)).intervalIntegrable 0 s
    rw [hi,intervalIntegral.integral_add (f := fun r => a r*‖u r‖)
      (g := fun r => ‖extend (φ-ψ) r‖*C) ((ha.mul hu.norm).intervalIntegrable 0 s)
      (((continuous_extend (φ-ψ)).norm.mul continuous_const).intervalIntegrable 0 s),
      intervalIntegral.integral_mul_const] at hm
    have hδ := mul_le_mul_of_nonneg_right (integral_potential_norm_le_L2 (φ-ψ) ⟨s,hs⟩) hC
    exact hm.trans (by dsimp [D] at *; linarith)
  have h := le_exp_integral_of_le_const_add_integral (fun s => ‖u s‖) a hu.norm ha 1 (C*D)
    (mul_nonneg hC hD) (fun s _ => norm_nonneg _) (fun s _ => add_nonneg (norm_nonneg _) (norm_nonneg _)) hbound
    t t.property
  have hE := Real.exp_le_exp.mpr (integral_classicalCoefficient_norm_budget φ z t)
  apply h.trans ((mul_le_mul_of_nonneg_left hE (mul_nonneg hC hD)).trans_eq ?_)
  dsimp [C,D]
  rw [show (‖v‖*Real.exp (‖z‖+classicalPotentialL2Norm ψ)*classicalPotentialL2Norm (φ-ψ))*
      Real.exp (‖z‖+classicalPotentialL2Norm φ) =
      ‖v‖*(Real.exp (‖z‖+classicalPotentialL2Norm ψ)*Real.exp (‖z‖+classicalPotentialL2Norm φ))*
        classicalPotentialL2Norm (φ-ψ) by ring,← Real.exp_add]
  exact congrArg (fun x => ‖v‖*Real.exp x*classicalPotentialL2Norm (φ-ψ)) (by ring)

/-- Uniform stability of the whole solution curve on L2-bounded potential sets. -/
theorem dist_classicalSolutionCurve_le_L2 (φ ψ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ)
    (R : ℝ) (hφ : ‖continuousPotentialL2Class φ‖ ≤ R) (hψ : ‖continuousPotentialL2Class ψ‖ ≤ R) :
    dist (classicalSolutionCurve φ z v) (classicalSolutionCurve ψ z v) ≤
      (‖v‖*Real.exp (2*‖z‖+2*R))*dist (continuousPotentialL2Class φ) (continuousPotentialL2Class ψ) := by
  rw [norm_continuousPotentialL2Class] at hφ hψ
  rw [dist_continuousPotentialL2Class]
  apply (ContinuousMap.dist_le (mul_nonneg
    (mul_nonneg (norm_nonneg _) (Real.exp_nonneg _)) (Real.sqrt_nonneg _))).mpr
  intro t
  rw [classicalSolutionCurve_apply,classicalSolutionCurve_apply,dist_eq_norm]
  exact (norm_classicalSolution_sub_le_L2 φ ψ z v t).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by linarith)) (norm_nonneg _)) (Real.sqrt_nonneg _))

end NLS.ZakharovShabat
