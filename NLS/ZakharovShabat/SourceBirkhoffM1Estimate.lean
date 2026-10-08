import NLS.ZakharovShabat.SourceBirkhoffM1Coordinates

/-! # Theorem 23.4: the real weighted Birkhoff-map bound

One existing Birkhoff map obeys these estimates simultaneously for every
M₁ weight. The complex-neighborhood action estimate is a separate result.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
namespace SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)}
  {s : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k}

/-- The squared weighted Birkhoff norm inherits the real action constant exactly. -/
theorem m1Coordinates_norm_sq_le
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (w : SpectralWeight) (hw : w.HasLinearFactor) (a : realTypeSourceSubmodule 2) :
    ‖D.m1Coordinates w hw a‖^2 ≤
      (2:ℝ)^21*(w.realExtension (16*‖a.val‖^2))^2*‖a.val‖^2 := by
  rw [D.m1Coordinates_norm_sq]
  have h := mul_le_mul_of_nonneg_left (sourceM1_real_weighted_actions_normalized w hw a).2
    (by norm_num : (0:ℝ) ≤ 2)
  calc
    _ ≤ 2*((2:ℝ)^20*(w.realExtension (16*‖a.val‖^2))^2*‖a.val‖^2) := h
    _ = _ := by ring

/-- The real Birkhoff-map conclusion of Theorem 23.4, with the universal
positive constant 2048 and the exact source weight and norm. -/
theorem m1Coordinates_norm_le
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (w : SpectralWeight) (hw : w.HasLinearFactor) (a : realTypeSourceSubmodule 2) :
    ‖D.m1Coordinates w hw a‖ ≤ 2048*w.realExtension (16*‖a.val‖^2)*‖a.val‖ := by
  have h := D.m1Coordinates_norm_sq_le w hw a
  have hW := (w.one_le_realExtension (16*‖a.val‖^2))
  have hright : 0 ≤ 2048*w.realExtension (16*‖a.val‖^2)*‖a.val‖ := by positivity
  apply (sq_le_sq₀ (norm_nonneg _) hright).mp
  have hnonneg := mul_nonneg (sq_nonneg (w.realExtension (16*‖a.val‖^2))) (sq_nonneg ‖a.val‖)
  norm_num at h
  nlinarith

/-- The weighted image of the zero source is the zero Hilbert pair. -/
@[simp] theorem m1Coordinates_zero
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (w : SpectralWeight) (hw : w.HasLinearFactor) : D.m1Coordinates w hw 0 = 0 := by
  have h := D.m1Coordinates_norm_le w hw 0
  simp only [ZeroMemClass.coe_zero,norm_zero,mul_zero] at h
  exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))

end SourceBirkhoffMapComplexData

/-- A single constructed Birkhoff map satisfies the real weighted conclusion
of Theorem 23.4 simultaneously for all M₁ weights. -/
theorem exists_sourceBirkhoffMap_M1_bound :
    ∃ W₀ B W : Set (CoeffPair 2), ∃ s : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k,
      ∃ D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s,
        ∀ w : SpectralWeight, ∀ hw : w.HasLinearFactor, ∀ a : realTypeSourceSubmodule 2,
          ‖D.m1Coordinates w hw a‖ ≤ 2048*w.realExtension (16*‖a.val‖^2)*‖a.val‖ := by
  obtain ⟨W₀,B,W,s,D⟩ := exists_sourceBirkhoffMap_complex_analytic
    (by simp : (2:ℝ≥0∞) ≠ ⊤) (by norm_num : (1:ℝ≥0∞) < 2)
  exact ⟨W₀,B,W,s,D,fun w hw a => D.m1Coordinates_norm_le w hw a⟩

end NLS.ZakharovShabat
