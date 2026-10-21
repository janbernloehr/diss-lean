import NLS.ZakharovShabat.WKBBoundaryNextLeadingFactors
import NLS.ZakharovShabat.SobolevWKBInitialDecay
import NLS.ZakharovShabat.WKBBoundedFrequencyCutoff

/-! # Decay of the next-phase leading factors

Both multipliers differ from one by a uniform inverse-index symbol on original Sobolev balls.
-/

noncomputable section
open Set Complex NLS.Fourier
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat
open BoundaryCondition

/-- Both next-phase leading multipliers differ from one by an inverse-index
symbol, uniformly on original Sobolev balls and bounded displacements. -/
theorem exists_uniform_nlsWKB_boundary_next_factor_decay
    (s N : ℕ) (hNs : N ≤ s) (R D : ℝ) (hR : 0 ≤ R) (hD : 0 ≤ D) :
    ∃ K : ℕ, 0 < K ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ δ : NLS.Coeff ⊤, ‖δ‖ ≤ D →
      ∀ n : ℤ, K ≤ n.natAbs → ∀ θ : BoundaryCondition,
        let z := (Real.pi:ℂ)*n+δ n
        let p := nlsWKBInitialLower a b N z
        let q := nlsWKBInitialUpper a b N z
        ‖p‖ ≤ 1/2 ∧ ‖q‖ ≤ 1/2 ∧
        ‖wkbBoundaryNextLeadingFactor θ p‖ ≤ 2 ∧
        ‖wkbBoundaryNextLeadingFactor θ q‖ ≤ 2 ∧
        (1+|(n:ℝ)|)*‖wkbBoundaryNextLeadingFactor θ p-1‖ ≤ C ∧
        (1+|(n:ℝ)|)*‖wkbBoundaryNextLeadingFactor θ q-1‖ ≤ C := by
  obtain ⟨K₀,hK₀,hgeom⟩ := exists_wkb_bounded_frequency_cutoff D hD
  obtain ⟨T,hT,hbasis⟩ := exists_uniform_nlsWKB_initial_basis_bounds s N hNs R hR
  obtain ⟨B,hB,hdecay⟩ := exists_uniform_nlsWKB_initial_coordinate_decay s N hNs R hR
  obtain ⟨L,hL⟩ := exists_nat_ge T
  let K := max K₀ L
  refine ⟨K,hK₀.trans_le (le_max_left _ _),4*B,by positivity,?_⟩
  intro ab hab a b ha hb hpa hpb hca hcb δ hδD n hn θ
  let z := (Real.pi:ℂ)*n+δ n
  let p := nlsWKBInitialLower a b N z
  let q := nlsWKBInitialUpper a b N z
  have hδ (j : ℤ) : ‖δ j‖ ≤ D := (lp.norm_apply_le_norm (by simp) δ j).trans hδD
  have hz := (hgeom δ hδ n ((le_max_left _ _).trans hn)).2
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
  have hf := norm_wkbBoundaryNextLeadingFactor_bounds θ p hp
  have hg := norm_wkbBoundaryNextLeadingFactor_bounds θ q hq
  refine ⟨hp,hq,hf.1,hg.1,?_,?_⟩
  · have hh := mul_le_mul_of_nonneg_left hf.2 (by positivity : 0 ≤ 1+|(n:ℝ)|)
    nlinarith [norm_nonneg q,mul_nonneg (by positivity : 0 ≤ 1+|(n:ℝ)|) (norm_nonneg q)]
  · have hh := mul_le_mul_of_nonneg_left hg.2 (by positivity : 0 ≤ 1+|(n:ℝ)|)
    nlinarith [norm_nonneg p,mul_nonneg (by positivity : 0 ≤ 1+|(n:ℝ)|) (norm_nonneg p)]

end NLS.ZakharovShabat
