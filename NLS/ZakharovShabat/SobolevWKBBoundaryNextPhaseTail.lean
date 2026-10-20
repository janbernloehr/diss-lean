import NLS.ZakharovShabat.SobolevWKBNextSeparatedTail
import NLS.ZakharovShabat.NLSWKBBoundaryPhaseElimination

/-! # The next Hamiltonian phase at actual boundary roots

The boundary-root equation and the invertible phase factor give an H^(s+1) error between the hyperbolic sine phase and normalized leading integrals.
-/

noncomputable section
open Set Complex NLS.Fourier
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat
open BoundaryCondition

/-- At actual separated roots, the next Hamiltonian sine phase differs
from the normalized leading integrals by an H^(s+1) tail. -/
theorem exists_uniform_nlsWKB_boundary_next_phase_tail_bound
    (s : ℕ) (hs : 1 ≤ s) (R D : ℝ) (hR : 0 ≤ R) (hD : 0 ≤ D) :
    ∃ K : ℕ, 0 < K ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ K' : ℕ, K ≤ K' → ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ∀ ha : ContDiff ℝ ∞ a, ∀ hb : ContDiff ℝ ∞ b,
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ δ : NLS.Coeff ⊤, ‖δ‖ ≤ D → ∀ θ : BoundaryCondition,
      (∀ n : ℤ, K' ≤ n.natAbs → classicalSeparatedCharacteristic θ
        (classicalPotentialOfFunctions a b ha.continuous hb.continuous) ((Real.pi:ℂ)*n+δ n) = 0) →
      ∃ f : ScalarSobolev (s+1),
        (∀ n, f.val n = if K' ≤ n.natAbs then
          let z := (Real.pi:ℂ)*n+δ n
          let p := nlsWKBInitialLower a b s z
          let q := nlsWKBInitialUpper a b s z
          let η := extensionSign θ
          sinh (nlsHamiltonianPhase a b (s+1) z)-
            ((q-η)*nlsWKBLeadingTerm a b s z 1+(η-p)*nlsWKBLeadingTerm (-b) (-a) s (-z) 1)/
              (2*(1+p*q-η*(p+q)))
          else 0) ∧ ‖f‖ ≤ C := by
  classical
  obtain ⟨K₀,hK₀,C,hC,hphase⟩ := exists_uniform_nlsWKB_next_separated_fourier_tail_bound_of_bounded_displacement s hs R D hR hD
  obtain ⟨K₁,_,hgeom⟩ := exists_wkb_bounded_frequency_cutoff D hD
  obtain ⟨T,_,hbasis⟩ := exists_uniform_nlsWKB_initial_basis_bounds s s le_rfl R hR
  obtain ⟨L,hL⟩ := exists_nat_ge T
  let K := max K₀ (max K₁ L)
  refine ⟨K,hK₀.trans_le (le_max_left _ _),2*C,by positivity,?_⟩
  intro K' hKK' ab hab a b ha hb hpa hpb hca hcb δ hδD θ hroot
  have hKs : K₀ ≤ K' ∧ K₁ ≤ K' ∧ L ≤ K' := by dsimp only [K] at hKK'; omega
  obtain ⟨f,hf,hfn⟩ := hphase K' hKs.1 ab hab a b ha hb hpa hpb hca hcb δ hδD θ
  let ν (n : ℤ) := (Real.pi:ℂ)*n+δ n
  let p (n : ℤ) := nlsWKBInitialLower a b s (ν n)
  let q (n : ℤ) := nlsWKBInitialUpper a b s (ν n)
  let η := extensionSign θ
  let A (n : ℤ) := 1+p n*q n-η*(p n+q n)
  let S (n : ℤ) := nlsWKBLeadingTerm a b s (ν n) 1
  let T' (n : ℤ) := nlsWKBLeadingTerm (-b) (-a) s (-(ν n)) 1
  let g (n : ℤ) := if K' ≤ n.natAbs then
    sinh (nlsHamiltonianPhase a b (s+1) (ν n))-((q n-η)*S n+(η-p n)*T' n)/(2*A n) else 0
  have hbase (n : ℤ) (hn : K' ≤ n.natAbs) : A n ≠ 0 ∧ ‖(A n)⁻¹‖ ≤ 4 := by
    have hδ (j : ℤ) : ‖δ j‖ ≤ D := (lp.norm_apply_le_norm (by simp) δ j).trans hδD
    have hz := (hgeom δ hδ n (hKs.2.1.trans hn)).2
    have hnL : (L:ℝ) ≤ (n.natAbs:ℝ) := by exact_mod_cast hKs.2.2.trans hn
    have hT : T ≤ ‖ν n‖ := by
      change 1+|(n:ℝ)| ≤ ‖ν n‖ at hz
      have habs : |(n:ℝ)| = (n.natAbs:ℝ) := by simp
      rw [habs] at hz
      linarith
    have h := hbasis ab hab a b ha hb hpa hpb hca hcb (ν n) hT
    exact norm_inv_wkb_boundary_phase_factor_le_four θ (p n) (q n) h.1 h.2.1
  have hg (n : ℤ) : ‖g n‖ ≤ 2*‖f.val n‖ := by
    by_cases hn : K' ≤ n.natAbs
    · have he : f.val n = 2*A n*sinh (nlsHamiltonianPhase a b (s+1) (ν n))-
          (q n-η)*S n-(η-p n)*T' n := by
        rw [hf n,if_pos hn]
        simp only [hroot n hn,mul_zero,zero_add]
        rfl
      have hrep : g n = (2*A n)⁻¹*f.val n := by
        rw [he]
        simp only [g,if_pos hn]
        field_simp [(hbase n hn).1]
        ring
      rw [hrep,norm_mul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      rw [mul_inv_rev]
      simp only [norm_mul,norm_inv,norm_ofNat]
      have h := (hbase n hn).2
      rw [norm_inv] at h
      linarith
    · simp only [g,if_neg hn,norm_zero]
      positivity
  obtain ⟨e,he,hen⟩ := WeightedCoeff.exists_of_norm_le _ f g 2 (by norm_num) hg
  exact ⟨e,he,hen.trans (mul_le_mul_of_nonneg_left hfn (by norm_num))⟩

end NLS.ZakharovShabat
