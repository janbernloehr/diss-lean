import NLS.ZakharovShabat.SourceLemmaG1

/-! # Uniform first Born bounds imply bounds for the actual L2 solution

This is the consequence step in G.2. It works on the full physical L2 space
and retains the exact coefficient from G.1, with a sharper sqrt(time) factor.
-/
noncomputable section
open Set MeasureTheory
open NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- A uniform bound on the actual Born operator gives the corresponding
remainder bound, retaining the length of the time interval. -/
theorem l2HermitianRemainder_le_of_firstBorn_uniform
    (φ : IntervalPairL2) (z : ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hF : ∀ s : Icc (0 : ℝ) 1, l2NormalizedHermitianFirstBorn φ z s ≤ B)
    (t : Icc (0 : ℝ) 1) :
    l2NormalizedHermitianRemainder φ z t ≤
      (1+‖φ‖*Real.exp ‖φ‖*Real.sqrt t.val)*B := by
  let F := l2NormalizedHermitianFirstBorn φ z
  have hsq : (∫ s in (0 : ℝ)..t.val, (extend F s)^2) ≤ t.val*B^2 := by
    calc
      _ ≤ ∫ s in (0 : ℝ)..t.val, B^2 := by
        apply intervalIntegral.integral_mono_on t.property.1
          (((continuous_extend F).pow 2).intervalIntegrable 0 t) (intervalIntegrable_const)
        intro s hs
        have he : extend F s = F ⟨s,hs.1,hs.2.trans t.property.2⟩ :=
          extend_coe F ⟨s,hs.1,hs.2.trans t.property.2⟩
        change (extend F s)^2 ≤ B^2
        rw [he]
        have h0 : 0 ≤ F ⟨s,hs.1,hs.2.trans t.property.2⟩ := by
          exact mul_nonneg (Real.exp_nonneg _) (norm_nonneg _)
        exact pow_le_pow_left₀ h0 (hF _) 2
      _ = _ := by simp
  have hsqrt : Real.sqrt (∫ s in (0 : ℝ)..t.val, (extend F s)^2) ≤ Real.sqrt t.val*B := by
    exact (Real.sqrt_le_sqrt hsq).trans_eq (by rw [Real.sqrt_mul t.property.1,Real.sqrt_sq hB])
  calc
    _ ≤ F t+‖φ‖*Real.exp ‖φ‖*Real.sqrt (∫ s in (0 : ℝ)..t.val, (extend F s)^2) :=
      sourceLemmaG1 φ z t
    _ ≤ B+‖φ‖*Real.exp ‖φ‖*(Real.sqrt t.val*B) :=
      add_le_add (hF t) (mul_le_mul_of_nonneg_left hsqrt (by positivity))
    _ = _ := by ring

/-- On the unit interval the exact multiplier is 1 + ||phi|| exp(||phi||). -/
theorem l2HermitianRemainder_le_of_firstBorn_uniform_unit
    (φ : IntervalPairL2) (z : ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hF : ∀ s : Icc (0 : ℝ) 1, l2NormalizedHermitianFirstBorn φ z s ≤ B)
    (t : Icc (0 : ℝ) 1) :
    l2NormalizedHermitianRemainder φ z t ≤ (1+‖φ‖*Real.exp ‖φ‖)*B := by
  apply (l2HermitianRemainder_le_of_firstBorn_uniform φ z B hB hF t).trans
  exact mul_le_mul_of_nonneg_right (add_le_add le_rfl
    (mul_le_of_le_one_right (by positivity) (Real.sqrt_le_one.mpr t.property.2))) hB

end NLS.ZakharovShabat
