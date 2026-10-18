import NLS.ZakharovShabat.ClassicalSeparatedCharacteristics

/-! # Scalar spectral errors from endpoint columns

Both column errors control the actual trace, off-diagonal anti-discriminant, and either source-normalized separated characteristic with factor two.
-/

noncomputable section
open Set Complex Matrix NLS.LinearVolterra
namespace NLS.ZakharovShabat
open BoundaryCondition

/-- Two vector error bounds control all the source-normalized scalar
monodromy combinations, including either separated boundary condition. -/
theorem norm_characteristic_column_combinations_le
    (X Y : ℂ × ℂ) (ε : ℝ) (hX : ‖X‖ ≤ ε) (hY : ‖Y‖ ≤ ε) :
    ‖X.1+Y.2‖ ≤ 2*ε ∧ ‖Y.1+X.2‖ ≤ 2*ε ∧
      ∀ θ : BoundaryCondition,
        ‖(Y.2-X.1+extensionSign θ*(X.2-Y.1))/(2*I)‖ ≤ 2*ε := by
  have hx₁ := (norm_fst_le X).trans hX
  have hx₂ := (norm_snd_le X).trans hX
  have hy₁ := (norm_fst_le Y).trans hY
  have hy₂ := (norm_snd_le Y).trans hY
  refine ⟨(norm_add_le _ _).trans (by linarith),
    (norm_add_le _ _).trans (by linarith),?_⟩
  intro θ
  have he : ‖extensionSign θ‖ = 1 := by cases θ <;> norm_num [extensionSign]
  have hd : ‖Y.2-X.1‖ ≤ 2*ε := (norm_sub_le _ _).trans (by linarith)
  have ho : ‖X.2-Y.1‖ ≤ 2*ε := (norm_sub_le _ _).trans (by linarith)
  rw [norm_div]
  have hn : ‖Y.2-X.1+extensionSign θ*(X.2-Y.1)‖ ≤ 4*ε := by
    apply (norm_add_le _ _).trans
    rw [norm_mul,he,one_mul]
    linarith
  norm_num only [norm_mul,norm_ofNat,norm_I,mul_one]
  exact (div_le_iff₀ (by norm_num : (0:ℝ) < 2)).mpr (by linarith)

/-- Approximate endpoint columns give actual discriminant,
anti-discriminant, and separated-characteristic errors with factor two. -/
theorem norm_classical_characteristic_errors_of_columns
    (Φ : Curve (ℂ × ℂ)) (z : ℂ) (U V : ℂ × ℂ) (ε : ℝ)
    (hU : ‖classicalSolution Φ z (1,0) 1-U‖ ≤ ε)
    (hV : ‖classicalSolution Φ z (0,1) 1-V‖ ≤ ε) :
    ‖classicalDiscriminant Φ z-(U.1+V.2)‖ ≤ 2*ε ∧
    ‖classicalAntiDiscriminant Φ z-(V.1+U.2)‖ ≤ 2*ε ∧
    ∀ θ : BoundaryCondition,
      ‖classicalSeparatedCharacteristic θ Φ z-
        (V.2-U.1+extensionSign θ*(U.2-V.1))/(2*I)‖ ≤ 2*ε := by
  have h := norm_characteristic_column_combinations_le
    (classicalSolution Φ z (1,0) 1-U) (classicalSolution Φ z (0,1) 1-V) ε hU hV
  simp only [Prod.fst_sub,Prod.snd_sub] at h
  refine ⟨?_,?_,?_⟩
  · simp only [classicalDiscriminant,classicalMonodromy,classicalFundamentalMatrix,
      Matrix.trace_fin_two_of]
    convert h.1 using 1
    · congr 1
      ring
  · simp only [classicalAntiDiscriminant,classicalMonodromy,classicalFundamentalMatrix,
      Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
    convert h.2.1 using 1
    · congr 1
      ring
  · intro θ
    simp only [classicalSeparatedCharacteristic,classicalMonodromy,classicalFundamentalMatrix,
      Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
    convert h.2.2 θ using 1
    · congr 1
      ring

end NLS.ZakharovShabat
