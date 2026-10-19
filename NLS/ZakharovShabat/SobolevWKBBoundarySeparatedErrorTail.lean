import NLS.ZakharovShabat.SobolevWKBBoundaryFactorDecay
import NLS.ZakharovShabat.SobolevWKBCharacteristicModels
import NLS.SequenceSpaces.SobolevInversePowerBound

/-! # The phase-elimination separated error

Multiplication by the separated boundary factor makes the actual model error an H^(s+1) tail.
-/

noncomputable section
open Set Complex NLS.Fourier NLS.LinearVolterra
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat
open BoundaryCondition

/-- The separated-characteristic model error gains one Sobolev order
when multiplied by its phase-elimination factor. No root equation is
needed, and every larger cutoff is allowed. -/
theorem exists_uniform_nlsWKB_boundary_separated_error_tail_bound
    (s : ℕ) (hs : 1 ≤ s) (R D M : ℝ) (hR : 0 ≤ R) (hD : 0 ≤ D) :
    ∃ K : ℕ, 0 < K ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ K' : ℕ, K ≤ K' → ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ∀ ha : ContDiff ℝ ∞ a, ∀ hb : ContDiff ℝ ∞ b,
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ δ : NLS.Coeff ⊤, ‖δ‖ ≤ D →
      (∀ n : ℤ, (1+|(n:ℝ)|)*‖δ n‖ ≤ M) → ∀ θ : BoundaryCondition,
      ∃ f : ScalarSobolev (s+1),
        (∀ n, f.val n = if K' ≤ n.natAbs then
          let z := (Real.pi:ℂ)*n+δ n
          let p := nlsWKBInitialLower a b s z
          let q := nlsWKBInitialUpper a b s z
          (-2*I*(p-q)/(1+p*q-extensionSign θ*(p+q)))*
            (nlsWKBSeparatedCharacteristicModel θ a b s z-
              classicalSeparatedCharacteristic θ (classicalPotentialOfFunctions a b ha.continuous hb.continuous) z)
          else 0) ∧ ‖f‖ ≤ C := by
  classical
  obtain ⟨K₀,hK₀,C₀,hC₀,hfactor⟩ := exists_uniform_nlsWKB_boundary_factor_decay s s le_rfl R D M hR hD
  obtain ⟨K₁,_,hgeom⟩ := exists_wkb_leading_frequency_cutoff D M hD
  obtain ⟨T,_,C₁,hC₁,hchar⟩ := exists_uniform_nlsWKB_characteristic_models_error_bound s s hs le_rfl R hR D
  obtain ⟨L,hL⟩ := exists_nat_ge T
  let K := max K₀ (max K₁ L)
  refine ⟨K,hK₀.trans_le (le_max_left _ _),2*(C₀*C₁),by positivity,?_⟩
  intro K' hK' ab hab a b ha hb hpa hpb hca hcb δ hδD hδM θ
  have hK₀ : K₀ ≤ K' := (le_max_left _ _).trans hK'
  have hK₁ : K₁ ≤ K' := (le_max_left _ _).trans ((le_max_right _ _).trans hK')
  have hLK : L ≤ K' := (le_max_right _ _).trans ((le_max_right _ _).trans hK')
  let ν (n : ℤ) := (Real.pi:ℂ)*n+δ n
  let p (n : ℤ) := nlsWKBInitialLower a b s (ν n)
  let q (n : ℤ) := nlsWKBInitialUpper a b s (ν n)
  let m (n : ℤ) := -2*I*(p n-q n)/(1+p n*q n-extensionSign θ*(p n+q n))
  let E (n : ℤ) := nlsWKBSeparatedCharacteristicModel θ a b s (ν n)-
    classicalSeparatedCharacteristic θ (classicalPotentialOfFunctions a b ha.continuous hb.continuous) (ν n)
  let F (n : ℤ) := if K' ≤ n.natAbs then m n*E n else 0
  have hδ (n : ℤ) : ‖δ n‖ ≤ D := (lp.norm_apply_le_norm (by simp) δ n).trans hδD
  have hF (n : ℤ) : (1+|(n:ℝ)|)^((s+1)+1)*‖F n‖ ≤ C₀*C₁ := by
    by_cases hn : K' ≤ n.natAbs
    · have hz := (hgeom δ hδ hδM n (hK₁.trans hn)).2
      change 1+|(n:ℝ)| ≤ ‖ν n‖ at hz
      have hnL : (L:ℝ) ≤ (n.natAbs:ℝ) := by exact_mod_cast hLK.trans hn
      have hzT : T ≤ ‖ν n‖ := by
        have habs : |(n:ℝ)| = (n.natAbs:ℝ) := by simp
        rw [habs] at hz
        linarith
      have hzD : |(ν n).im| ≤ D := by
        have he : (ν n).im = (δ n).im := by simp [ν,Complex.mul_im]
        rw [he]
        exact (Complex.abs_im_le_norm _).trans (hδ n)
      have he : ‖E n‖ ≤ C₁*‖(2*I*ν n)⁻¹‖^(s+1) := by
        dsimp only [E]
        rw [norm_sub_rev]
        exact (hchar ab hab a b ha hb hpa hpb hca hcb (ν n) hzT hzD).2.2 θ
      have hm : (1+|(n:ℝ)|)*‖m n‖ ≤ C₀ :=
        (hfactor ab hab a b ha hb hpa hpb hca hcb δ hδD hδM n (hK₀.trans hn) θ).2.2.2.2.2.2
      have hw : (1+|(n:ℝ)|)*‖(2*I*ν n)⁻¹‖ ≤ 1 := by
        simp only [norm_inv,norm_mul,norm_ofNat,norm_I,mul_one]
        rw [← div_eq_mul_inv]
        apply (div_le_one (by linarith [abs_nonneg (n:ℝ)] : 0 < 2*‖ν n‖)).mpr
        linarith [abs_nonneg (n:ℝ)]
      have hp := pow_le_pow_left₀ (by positivity) hw (s+1)
      rw [mul_pow,one_pow] at hp
      simp only [F,if_pos hn,norm_mul]
      calc
        _ ≤ (1+|(n:ℝ)|)^((s+1)+1)*(‖m n‖*(C₁*‖(2*I*ν n)⁻¹‖^(s+1))) := by gcongr
        _ = ((1+|(n:ℝ)|)*‖m n‖)*C₁*((1+|(n:ℝ)|)^(s+1)*‖(2*I*ν n)⁻¹‖^(s+1)) := by rw [pow_succ]; ring
        _ ≤ C₀*C₁*1 := mul_le_mul (mul_le_mul_of_nonneg_right hm hC₁) hp (by positivity) (by positivity)
        _ = _ := mul_one _
    · simpa only [F,if_neg hn,norm_zero,mul_zero] using mul_nonneg hC₀ hC₁
  obtain ⟨f,hf,hfn⟩ := WeightedCoeff.exists_sobolev_coeff_of_inverse_power_bound (s+1) F (C₀*C₁) (by positivity) hF
  exact ⟨f,hf,hfn⟩

end NLS.ZakharovShabat
