import NLS.ZakharovShabat.SobolevWKBCharacteristicModels

/-! # Componentwise decomposition of the actual anti-discriminant error

The exact identity retains the initial-coordinate factors on the diagonal WKB remainders, isolating the two off-diagonal terms that need sharp sampling estimates.
-/

noncomputable section
open Set Complex Matrix NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- The first actual solution error after subtracting the explicit leading
integral. The second component is the off-diagonal remainder. -/
def nlsWKBFirstRemainder (a b : ℝ → ℂ) (ha : Continuous a) (hb : Continuous b)
    (N : ℕ) (z : ℂ) (t : Icc (0:ℝ) 1) : ℂ × ℂ :=
  nlsWKBVector a b N z t-
    classicalSolution (classicalPotentialOfFunctions a b ha hb) z
      (nlsWKBVector a b N z 0) t-(0,nlsWKBLeadingTerm a b N z t)

/-- The reflected actual solution error. Its first component is the
second off-diagonal remainder. -/
def nlsWKBSecondRemainder (a b : ℝ → ℂ) (ha : Continuous a) (hb : Continuous b)
    (N : ℕ) (z : ℂ) (t : Icc (0:ℝ) 1) : ℂ × ℂ :=
  nlsWKBSecondVector a b N z t-
    classicalSolution (classicalPotentialOfFunctions a b ha hb) z
      (nlsWKBSecondVector a b N z 0) t-(nlsWKBLeadingTerm (-b) (-a) N (-z) t,0)

/-- The anti-discriminant error uses the off-diagonal remainders directly,
whereas both diagonal remainders carry an extra initial-coordinate factor. -/
theorem classicalAntiDiscriminant_sub_wkb_model_exact
    (a b : ℝ → ℂ) (ha : Continuous a) (hb : Continuous b) (N : ℕ) (z : ℂ)
    (hd : 1-nlsWKBInitialLower a b N z*nlsWKBInitialUpper a b N z ≠ 0) :
    let p := nlsWKBInitialLower a b N z
    let q := nlsWKBInitialUpper a b N z
    let E := nlsWKBFirstRemainder a b ha hb N z 1
    let F := nlsWKBSecondRemainder a b ha hb N z 1
    (1-p*q)*(classicalAntiDiscriminant (classicalPotentialOfFunctions a b ha hb) z-
      nlsWKBAntiDiscriminantModel a b N z) = q*E.1+p*F.2-E.2-F.1 := by
  dsimp only
  simp only [classicalAntiDiscriminant,classicalMonodromy,classicalFundamentalMatrix,
    Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  rw [classicalSolution_from_basis_left _ z _ _ hd ⟨1,by constructor <;> norm_num⟩,
    classicalSolution_from_basis_right _ z _ _ hd ⟨1,by constructor <;> norm_num⟩]
  simp only [nlsWKBAntiDiscriminantModel,nlsWKBFirstColumnModel,nlsWKBSecondColumnModel,
    nlsWKBFirstRemainder,nlsWKBSecondRemainder,nlsWKBVector_initial,nlsWKBSecondVector_initial,
    Prod.fst_sub,Prod.snd_sub,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,Set.Icc.coe_one]
  field_simp [hd]
  ring

/-- Componentwise anti-discriminant control retains the small factors on
the diagonal errors instead of replacing all four components by one norm. -/
theorem norm_classicalAntiDiscriminant_sub_wkb_model_le
    (a b : ℝ → ℂ) (ha : Continuous a) (hb : Continuous b) (N : ℕ) (z : ℂ)
    (hpq : ‖nlsWKBInitialLower a b N z*nlsWKBInitialUpper a b N z‖ ≤ 1/2) :
    let p := nlsWKBInitialLower a b N z
    let q := nlsWKBInitialUpper a b N z
    let E := nlsWKBFirstRemainder a b ha hb N z 1
    let F := nlsWKBSecondRemainder a b ha hb N z 1
    ‖classicalAntiDiscriminant (classicalPotentialOfFunctions a b ha hb) z-
      nlsWKBAntiDiscriminantModel a b N z‖ ≤
      2*(‖q‖*‖E.1‖+‖p‖*‖F.2‖+‖E.2‖+‖F.1‖) := by
  dsimp only
  obtain ⟨hd,hdi⟩ := norm_inv_one_sub_mul_le_two _ _ hpq
  have hid := classicalAntiDiscriminant_sub_wkb_model_exact a b ha hb N z hd
  dsimp only at hid
  have he := congrArg (fun x : ℂ => (1-nlsWKBInitialLower a b N z*nlsWKBInitialUpper a b N z)⁻¹*x) hid
  rw [← mul_assoc,inv_mul_cancel₀ hd,one_mul] at he
  rw [he,norm_mul]
  have htriangle (u v x y : ℂ) : ‖u+v-x-y‖ ≤ ‖u‖+‖v‖+‖x‖+‖y‖ := by
    linarith [norm_sub_le (u+v-x) y,norm_sub_le (u+v) x,norm_add_le u v]
  simpa only [norm_mul] using mul_le_mul hdi
    (htriangle (nlsWKBInitialUpper a b N z*(nlsWKBFirstRemainder a b ha hb N z 1).1)
      (nlsWKBInitialLower a b N z*(nlsWKBSecondRemainder a b ha hb N z 1).2)
      (nlsWKBFirstRemainder a b ha hb N z 1).2 (nlsWKBSecondRemainder a b ha hb N z 1).1)
    (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 2)

end NLS.ZakharovShabat
