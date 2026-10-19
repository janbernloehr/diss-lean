import NLS.ZakharovShabat.SobolevWKBInitialDecay

/-! # Quadratic carrier errors for the actual diagonal entries

The diagonal fundamental entries differ from the first WKB carriers by two inverse-frequency powers on original Sobolev balls.
-/

noncomputable section
open Set Complex NLS.Fourier NLS.LinearVolterra
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- The actual two diagonal fundamental entries agree with the first-order
WKB carriers up to two inverse-frequency powers, uniformly on original Hs
balls. The off-diagonal free-column errors provide the additional factor. -/
theorem exists_uniform_classical_diagonal_carrier_error_bound
    (s : ℕ) (hs : 1 ≤ s) (R : ℝ) (hR : 0 ≤ R) (H : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ∀ ha : ContDiff ℝ ∞ a, ∀ hb : ContDiff ℝ ∞ b,
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ z : ℂ, 1 ≤ ‖z‖ → |z.im| ≤ H → ∀ t : Icc (0:ℝ) 1,
        ‖(classicalSolution (classicalPotentialOfFunctions a b ha.continuous hb.continuous) z (1,0) t).1-
          nlsWKBCarrier a b 1 z t‖ ≤ C*‖(2*I*z)⁻¹‖^2 ∧
        ‖(classicalSolution (classicalPotentialOfFunctions a b ha.continuous hb.continuous) z (0,1) t).2-
          nlsWKBCarrier (-b) (-a) 1 (-z) t‖ ≤ C*‖(2*I*z)⁻¹‖^2 := by
  obtain ⟨B,hB,hinit⟩ := exists_uniform_nlsWKB_initial_coordinate_decay s 1 hs R hR
  obtain ⟨C₁,hC₁,hfirst⟩ := exists_uniform_nlsWKB_leading_oscillatory_error_bound s 1 hs hs R hR H
  obtain ⟨C₂,hC₂,hsecond⟩ := exists_uniform_nlsWKB_second_leading_oscillatory_error_bound s 1 hs hs R hR H
  let D := 2*classicalSobolevErrorConstant (2*R) H
  have hD : 0 ≤ D := mul_nonneg (by norm_num) (classicalSobolevErrorConstant_nonneg _ _ (by positivity))
  refine ⟨C₁+C₂+B*D,by positivity,?_⟩
  intro ab hab a b ha hb hpa hpb hca hcb z hz hzH t
  let Φ := classicalPotentialOfFunctions a b ha.continuous hb.continuous
  let w := ‖(2*I*z)⁻¹‖
  let A := classicalSolution Φ z (1,0) t
  let V := classicalSolution Φ z (0,1) t
  let p := nlsWKBInitialLower a b 1 z
  let q := nlsWKBInitialUpper a b 1 z
  obtain ⟨hp,hq⟩ := hinit ab hab a b ha hb hpa hpb hca hcb z hz
  have hfree (v : ℂ × ℂ) : ‖classicalSolution Φ z v t-classicalFreeVector z v t‖ ≤ D*‖v‖*w :=
    norm_classicalSolution_sub_free_higherSobolev_le s hs R H ab hab a b ha.continuous hb.continuous
      hpa hpb hca hcb z (norm_pos_iff.mp (by linarith)) hzH v t
  have hA : ‖A.2‖ ≤ D*w := by
    have h := (norm_snd_le _).trans (hfree (1,0))
    simpa only [A,Prod.snd_sub,classicalFreeVector,mul_zero,sub_zero,Prod.norm_def,norm_one,norm_zero,
      max_eq_left zero_le_one,mul_one] using h
  have hV : ‖V.1‖ ≤ D*w := by
    have h := (norm_fst_le _).trans (hfree (0,1))
    simpa only [V,Prod.fst_sub,classicalFreeVector,mul_zero,sub_zero,Prod.norm_def,norm_one,norm_zero,
      max_eq_right zero_le_one,mul_one] using h
  have h₁ := (norm_fst_le _).trans (hfirst ab hab a b ha hb hpa hpb hca hcb z hz hzH t)
  have h₂ := (norm_snd_le _).trans (hsecond ab hab a b ha hb hpa hpb hca hcb z hz hzH t)
  rw [nlsWKBVector_initial,classicalSolution_eq_columns] at h₁
  rw [nlsWKBSecondVector_initial,classicalSolution_eq_columns] at h₂
  simp only [Prod.fst_sub,Prod.snd_sub,Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,
    smul_eq_mul,one_mul,sub_zero] at h₁ h₂
  change ‖nlsWKBCarrier a b 1 z t-(A.1+p*V.1)‖ ≤ C₁*w^2 at h₁
  change ‖nlsWKBCarrier (-b) (-a) 1 (-z) t-(q*A.2+V.2)‖ ≤ C₂*w^2 at h₂
  have hleft : ‖A.1-nlsWKBCarrier a b 1 z t‖ ≤ (C₁+B*D)*w^2 := by
    have he : A.1-nlsWKBCarrier a b 1 z t =
        -(nlsWKBCarrier a b 1 z t-(A.1+p*V.1))-p*V.1 := by ring
    rw [he]
    apply (norm_sub_le _ _).trans
    rw [norm_neg,norm_mul]
    exact (add_le_add h₁ (mul_le_mul hp hV (norm_nonneg _) (by positivity))).trans_eq (by ring)
  have hright : ‖V.2-nlsWKBCarrier (-b) (-a) 1 (-z) t‖ ≤ (C₂+B*D)*w^2 := by
    have he : V.2-nlsWKBCarrier (-b) (-a) 1 (-z) t =
        -(nlsWKBCarrier (-b) (-a) 1 (-z) t-(q*A.2+V.2))-q*A.2 := by ring
    rw [he]
    apply (norm_sub_le _ _).trans
    rw [norm_neg,norm_mul]
    exact (add_le_add h₂ (mul_le_mul hq hA (norm_nonneg _) (by positivity))).trans_eq (by ring)
  exact ⟨hleft.trans (by nlinarith [mul_nonneg hC₂ (sq_nonneg w)]),
    hright.trans (by nlinarith [mul_nonneg hC₁ (sq_nonneg w)])⟩

end NLS.ZakharovShabat
