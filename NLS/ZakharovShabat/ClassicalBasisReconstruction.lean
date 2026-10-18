import NLS.ZakharovShabat.ClassicalBoundaryDeterminants

/-! # Reconstruction from a perturbed initial basis

Exact basis reconstruction and a controlled inverse determinant preserve the order of both column errors.
-/

noncomputable section
open Set Complex NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- The two perturbed coordinate vectors reconstruct the first actual column. -/
theorem classicalSolution_from_basis_left (Φ : Curve (ℂ × ℂ)) (z p q : ℂ)
    (hpq : 1-p*q ≠ 0) (t : Icc (0:ℝ) 1) :
    classicalSolution Φ z (1,0) t = (1-p*q)⁻¹ •
      (classicalSolution Φ z (1,p) t-p • classicalSolution Φ z (q,1) t) := by
  rw [classicalSolution_eq_columns Φ z (1,p) t,classicalSolution_eq_columns Φ z (q,1) t]
  apply Prod.ext <;> simp only [Prod.fst_add,Prod.snd_add,Prod.fst_sub,Prod.snd_sub,
    Prod.smul_fst,Prod.smul_snd,smul_eq_mul,one_mul] <;> field_simp [hpq] <;> ring

/-- The same initial basis reconstructs the second actual column. -/
theorem classicalSolution_from_basis_right (Φ : Curve (ℂ × ℂ)) (z p q : ℂ)
    (hpq : 1-p*q ≠ 0) (t : Icc (0:ℝ) 1) :
    classicalSolution Φ z (0,1) t = (1-p*q)⁻¹ •
      (classicalSolution Φ z (q,1) t-q • classicalSolution Φ z (1,p) t) := by
  rw [classicalSolution_eq_columns Φ z (1,p) t,classicalSolution_eq_columns Φ z (q,1) t]
  apply Prod.ext <;> simp only [Prod.fst_add,Prod.snd_add,Prod.fst_sub,Prod.snd_sub,
    Prod.smul_fst,Prod.smul_snd,smul_eq_mul,one_mul] <;> field_simp [hpq] <;> ring

/-- A small product of the off-diagonal initial coordinates gives a
uniform inverse determinant bound. -/
theorem norm_inv_one_sub_mul_le_two (p q : ℂ) (hpq : ‖p*q‖ ≤ 1/2) :
    1-p*q ≠ 0 ∧ ‖(1-p*q)⁻¹‖ ≤ 2 := by
  have hn : (1/2:ℝ) ≤ ‖1-p*q‖ := by
    have h := norm_sub_norm_le (1:ℂ) (p*q)
    simp only [norm_one] at h
    linarith
  refine ⟨norm_pos_iff.mp (by linarith),?_⟩
  rw [norm_inv]
  have h := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1/2) hn
  norm_num [one_div] at h
  exact h

/-- Reconstruction propagates approximation errors without losing an
inverse-frequency power. -/
theorem norm_basis_reconstruction_sub_le
    (p q : ℂ) (hpq : ‖p*q‖ ≤ 1/2) (hp : ‖p‖ ≤ 1) (hq : ‖q‖ ≤ 1)
    (U V A B : ℂ × ℂ) (ε : ℝ) (hU : ‖U-A‖ ≤ ε) (hV : ‖V-B‖ ≤ ε) :
    ‖(1-p*q)⁻¹ • (U-p • V)-(1-p*q)⁻¹ • (A-p • B)‖ ≤ 4*ε ∧
    ‖(1-p*q)⁻¹ • (V-q • U)-(1-p*q)⁻¹ • (B-q • A)‖ ≤ 4*ε := by
  have hε : 0 ≤ ε := (norm_nonneg _).trans hU
  have hi := (norm_inv_one_sub_mul_le_two p q hpq).2
  have h (c : ℂ) (hc : ‖c‖ ≤ 1) (X Y A B : ℂ × ℂ)
      (hx : ‖X-A‖ ≤ ε) (hy : ‖Y-B‖ ≤ ε) :
      ‖(1-p*q)⁻¹ • (X-c • Y)-(1-p*q)⁻¹ • (A-c • B)‖ ≤ 4*ε := by
    rw [← smul_sub]
    have he : X-c • Y-(A-c • B) = (X-A)-c • (Y-B) := by
      simp only [smul_sub]
      abel
    rw [he,norm_smul]
    have hb : ‖X-A-c • (Y-B)‖ ≤ 2*ε := by
      apply (norm_sub_le _ _).trans
      rw [norm_smul]
      have hm := mul_le_mul hc hy (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
      linarith
    exact (mul_le_mul hi hb (norm_nonneg _) (by norm_num)).trans_eq (by ring)
  exact ⟨h p hp U V A B hU hV,h q hq V U B A hV hU⟩

end NLS.ZakharovShabat
