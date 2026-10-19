import NLS.ZakharovShabat.SobolevWKBInitialDecay
import NLS.ZakharovShabat.WKBLeadingFrequencyCutoff
import NLS.ZakharovShabat.WKBBoundaryLeadingFactors

/-! # Decay of the boundary phase-elimination factors

The leading factors differ from one by an inverse-index symbol and the separated factor has the same decay.
-/

noncomputable section
open Set Complex NLS.Fourier
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat
open BoundaryCondition

/-- The two phase-elimination multipliers are bounded and differ from one
by an inverse-index symbol, uniformly on original Sobolev balls. The
separated-model factor has the same inverse-index bound. -/
theorem exists_uniform_nlsWKB_boundary_factor_decay
    (s N : ℕ) (hNs : N ≤ s) (R D M : ℝ) (hR : 0 ≤ R) (hD : 0 ≤ D) :
    ∃ K : ℕ, 0 < K ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ δ : NLS.Coeff ⊤, ‖δ‖ ≤ D →
      (∀ n : ℤ, (1+|(n:ℝ)|)*‖δ n‖ ≤ M) →
      ∀ n : ℤ, K ≤ n.natAbs → ∀ θ : BoundaryCondition,
        let z := (Real.pi:ℂ)*n+δ n
        let p := nlsWKBInitialLower a b N z
        let q := nlsWKBInitialUpper a b N z
        ‖p‖ ≤ 1/2 ∧ ‖q‖ ≤ 1/2 ∧
        ‖wkbBoundaryLeadingFactor θ p q‖ ≤ 6 ∧
        ‖wkbBoundaryLeadingFactor θ q p‖ ≤ 6 ∧
        (1+|(n:ℝ)|)*‖wkbBoundaryLeadingFactor θ p q-1‖ ≤ C ∧
        (1+|(n:ℝ)|)*‖wkbBoundaryLeadingFactor θ q p-1‖ ≤ C ∧
        (1+|(n:ℝ)|)*‖(-2*I*(p-q))/(1+p*q-extensionSign θ*(p+q))‖ ≤ C := by
  obtain ⟨K₀,hK₀,hgeom⟩ := exists_wkb_leading_frequency_cutoff D M hD
  obtain ⟨T,hT,hbasis⟩ := exists_uniform_nlsWKB_initial_basis_bounds s N hNs R hR
  obtain ⟨B,hB,hdecay⟩ := exists_uniform_nlsWKB_initial_coordinate_decay s N hNs R hR
  obtain ⟨L,hL⟩ := exists_nat_ge T
  let K := max K₀ L
  refine ⟨K,hK₀.trans_le (le_max_left _ _),16*B,by positivity,?_⟩
  intro ab hab a b ha hb hpa hpb hca hcb δ hδD hδM n hn θ
  let z := (Real.pi:ℂ)*n+δ n
  let p := nlsWKBInitialLower a b N z
  let q := nlsWKBInitialUpper a b N z
  have hδ (j : ℤ) : ‖δ j‖ ≤ D := (lp.norm_apply_le_norm (by simp) δ j).trans hδD
  have hz := (hgeom δ hδ hδM n ((le_max_left _ _).trans hn)).2
  change 1+|(n:ℝ)| ≤ ‖z‖ at hz
  have hnL : (L:ℝ) ≤ (n.natAbs:ℝ) := by exact_mod_cast (le_max_right _ _).trans hn
  have hzT : T ≤ ‖z‖ := by
    have habs : |(n:ℝ)| = (n.natAbs:ℝ) := by simp
    rw [habs] at hz
    linarith
  obtain ⟨hp,hq,_⟩ := hbasis ab hab a b ha hb hpa hpb hca hcb z hzT
  obtain ⟨hpd,hqd⟩ := hdecay ab hab a b ha hb hpa hpb hca hcb z (hT.trans hzT)
  have hw : (1+|(n:ℝ)|)*‖(2*I*z)⁻¹‖ ≤ 1 := by
    simp only [norm_inv,norm_mul,norm_ofNat,norm_I,mul_one]
    rw [← div_eq_mul_inv]
    apply (div_le_one (by linarith : 0 < 2*‖z‖)).mpr
    linarith [abs_nonneg (n:ℝ)]
  have hpq : (1+|(n:ℝ)|)*(‖p‖+‖q‖) ≤ 2*B := by
    have h := mul_le_mul_of_nonneg_left (add_le_add hpd hqd) (by positivity : 0 ≤ 1+|(n:ℝ)|)
    dsimp only [p,q] at h ⊢
    nlinarith [mul_le_mul_of_nonneg_left hw hB]
  have hf := norm_wkbBoundaryLeadingFactor_bounds θ p q hp hq
  have hg := norm_wkbBoundaryLeadingFactor_bounds θ q p hq hp
  have hsep := norm_wkb_boundary_separated_factor_le θ p q hp hq
  refine ⟨hp,hq,hf.1,hg.1,?_,?_,?_⟩
  · have hh := mul_le_mul_of_nonneg_left hf.2 (by positivity : 0 ≤ 1+|(n:ℝ)|)
    nlinarith
  · have hh := mul_le_mul_of_nonneg_left hg.2 (by positivity : 0 ≤ 1+|(n:ℝ)|)
    nlinarith
  · have hh := mul_le_mul_of_nonneg_left hsep (by positivity : 0 ≤ 1+|(n:ℝ)|)
    nlinarith

end NLS.ZakharovShabat
