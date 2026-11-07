import NLS.ZakharovShabat.ClassicalRemainderL2Bound

/-! Uniform fundamental-solution errors with exponential growth controlled
only by the physical L2 norm. The derivative budget enters linearly. -/
noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- A uniform first-Born bound propagates with a physical L2 multiplier;
the potential supremum does not enter the exponential. -/
theorem classicalNormalizedRemainder_le_uniform_firstBorn_L2
    (φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) (A : ℝ) (hA : 0 ≤ A)
    (hfirst : ∀ t : Icc (0:ℝ) 1, classicalNormalizedFirstBorn φ z v t ≤ A)
    (t : Icc (0:ℝ) 1) :
    classicalNormalizedRemainder φ z v t ≤
      A*(1+classicalPotentialL2Norm φ*Real.exp (classicalPotentialL2Norm φ)) := by
  let F := classicalNormalizedFirstBorn φ z v
  have hF : Continuous F := continuous_classicalNormalizedFirstBorn φ z v
  have hFn (s : ℝ) : 0 ≤ F s := mul_nonneg (Real.exp_nonneg _) (norm_nonneg _)
  have hi : (∫ s in (0:ℝ)..t.val, (F s)^2) ≤ A^2 := by
    calc
      _ ≤ ∫ _s in (0:ℝ)..t.val, A^2 :=
        intervalIntegral.integral_mono_on t.property.1 ((hF.pow 2).intervalIntegrable _ _)
          (continuous_const.intervalIntegrable _ _) (fun s hs =>
            pow_le_pow_left₀ (hFn s) (hfirst ⟨s,hs.1,hs.2.trans t.property.2⟩) 2)
      _ = t.val*A^2 := by rw [intervalIntegral.integral_const]; simp only [sub_zero,smul_eq_mul]
      _ ≤ A^2 := mul_le_of_le_one_left (sq_nonneg A) t.property.2
  have hsqrt : Real.sqrt (∫ s in (0:ℝ)..t.val, (F s)^2) ≤ A :=
    Real.sqrt_le_iff.mpr ⟨hA,hi⟩
  have hL : 0 ≤ classicalPotentialL2Norm φ := Real.sqrt_nonneg _
  calc
    _ ≤ F t+classicalPotentialL2Norm φ*Real.exp (classicalPotentialL2Norm φ)*
        Real.sqrt (∫ s in (0:ℝ)..t.val, (F s)^2) :=
      classicalNormalizedRemainder_le_L2_firstBorn φ z v t
    _ ≤ A+classicalPotentialL2Norm φ*Real.exp (classicalPotentialL2Norm φ)*A :=
      add_le_add (hfirst t) (mul_le_mul_of_nonneg_left hsqrt (by positivity))
    _ = _ := by ring

/-- The inverse-frequency estimate has only a linear endpoint/derivative
budget and an L2-controlled exponential. This remains useful for growing
Fourier truncations with a fixed L2 bound. -/
theorem classicalNormalizedRemainder_le_inverse_frequency_L2
    (φ : Curve (ℂ × ℂ))
    (hf : AbsolutelyContinuousOnInterval (fun s => (extend φ s).1) 0 1)
    (hg : AbsolutelyContinuousOnInterval (fun s => (extend φ s).2) 0 1)
    (hfi : IntervalIntegrable (deriv (fun s => (extend φ s).1)) volume 0 1)
    (hgi : IntervalIntegrable (deriv (fun s => (extend φ s).2)) volume 0 1)
    (z : ℂ) (hz : z ≠ 0) (v : ℂ × ℂ) (t : Icc (0:ℝ) 1) :
    classicalNormalizedRemainder φ z v t ≤
      classicalFirstBornUniformBudget φ*‖v‖/(2*‖z‖)*
        (1+classicalPotentialL2Norm φ*Real.exp (classicalPotentialL2Norm φ)) := by
  have hB := classicalFirstBornUniformBudget_nonneg φ
  exact classicalNormalizedRemainder_le_uniform_firstBorn_L2 φ z v
    (classicalFirstBornUniformBudget φ*‖v‖/(2*‖z‖)) (by positivity)
    (norm_classicalFirstBornVector_weighted_uniform_le φ hf hg hfi hgi z hz v) t

end NLS.ZakharovShabat
