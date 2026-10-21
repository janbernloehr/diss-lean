import NLS.ZakharovShabat.SobolevHamiltonianNextPhaseFree
import NLS.ZakharovShabat.WKBLeadingFrequencyCutoff

/-! # Uniform smallness of the next Hamiltonian phase offset

One high-frequency cutoff gives inverse-index decay and any prescribed positive phase radius on original Sobolev balls.
-/

noncomputable section
open Set Complex NLS.Fourier
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- An inverse-index displacement gives a small inverse-index next-phase
offset, uniformly on original Hs balls and at every sufficiently large mode.
The cutoff may enforce any prescribed positive phase radius. -/
theorem exists_uniform_nlsHamiltonian_next_phase_offset_bounds
    (s : ℕ) (hs : 1 ≤ s) (R D M : ℝ) (hR : 0 ≤ R) (hD : 0 ≤ D) (hM : 0 ≤ M)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, 0 < K ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ δ : NLS.Coeff ⊤, ‖δ‖ ≤ D →
      (∀ n : ℤ, (1+|(n:ℝ)|)*‖δ n‖ ≤ M) →
      ∀ n : ℤ, K ≤ n.natAbs →
        1 ≤ ‖(Real.pi:ℂ)*n+δ n‖ ∧
        (1+|(n:ℝ)|)*‖nlsHamiltonianPhase a b (s+1) ((Real.pi:ℂ)*n+δ n)+I*(Real.pi:ℂ)*n‖ ≤ C ∧
        ‖nlsHamiltonianPhase a b (s+1) ((Real.pi:ℂ)*n+δ n)+I*(Real.pi:ℂ)*n‖ < ε := by
  obtain ⟨K₀,hK₀,hgeom⟩ := exists_wkb_leading_frequency_cutoff D M hD
  obtain ⟨A,hA,hfree⟩ := exists_uniform_nlsHamiltonian_next_phase_free_bound s (s+1) hs le_rfl R hR
  obtain ⟨L,hL⟩ := exists_nat_gt ((A+M)/ε)
  let K := max K₀ L
  refine ⟨K,hK₀.trans_le (le_max_left _ _),A+M,add_nonneg hA hM,?_⟩
  intro ab hab a b ha hb hpa hpb hca hcb δ hδD hδM n hn
  let ν := (Real.pi:ℂ)*n+δ n
  let u := nlsHamiltonianPhase a b (s+1) ν+I*(Real.pi:ℂ)*n
  have hδ (j : ℤ) : ‖δ j‖ ≤ D := (lp.norm_apply_le_norm (by simp) δ j).trans hδD
  have hzgeom := (hgeom δ hδ hδM n ((le_max_left _ _).trans hn)).2
  change 1+|(n:ℝ)| ≤ ‖ν‖ at hzgeom
  have hz : 1 ≤ ‖ν‖ := by linarith [abs_nonneg (n:ℝ)]
  have hw : (1+|(n:ℝ)|)*‖(2*I*ν)⁻¹‖ ≤ 1 := by
    simp only [norm_inv,norm_mul,norm_ofNat,norm_I,mul_one]
    rw [← div_eq_mul_inv]
    apply (div_le_one (by linarith : 0 < 2*‖ν‖)).mpr
    linarith
  have hu : ‖u‖ ≤ A*‖(2*I*ν)⁻¹‖+‖δ n‖ := by
    have he : u = (nlsHamiltonianPhase a b (s+1) ν+I*ν)-I*δ n := by dsimp [u,ν]; ring
    rw [he]
    exact (norm_sub_le _ _).trans (by
      simpa only [norm_mul,norm_I,one_mul] using
        add_le_add (hfree ab hab a b ha hb hpa hpb hca hcb ν hz) le_rfl)
  have hweighted : (1+|(n:ℝ)|)*‖u‖ ≤ A+M := by
    calc
      _ ≤ (1+|(n:ℝ)|)*(A*‖(2*I*ν)⁻¹‖+‖δ n‖) := mul_le_mul_of_nonneg_left hu (by positivity)
      _ = A*((1+|(n:ℝ)|)*‖(2*I*ν)⁻¹‖)+(1+|(n:ℝ)|)*‖δ n‖ := by ring
      _ ≤ A*1+M := add_le_add (mul_le_mul_of_nonneg_left hw hA) (hδM n)
      _ = A+M := by ring
  refine ⟨hz,hweighted,?_⟩
  have hnL : (L:ℝ) ≤ |(n:ℝ)| := by
    have hh : (L:ℝ) ≤ (n.natAbs:ℝ) := by exact_mod_cast (le_max_right _ _).trans hn
    simpa using hh
  have he := (div_lt_iff₀ hε).mp hL
  change ‖u‖ < ε
  nlinarith [abs_nonneg (n:ℝ)]

end NLS.ZakharovShabat
