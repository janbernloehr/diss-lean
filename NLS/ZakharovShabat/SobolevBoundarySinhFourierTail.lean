import NLS.ZakharovShabat.SobolevWKBBoundaryNextLeadingTails
import NLS.ZakharovShabat.SobolevWKBBoundaryNextPhaseTail

/-! # The actual boundary hyperbolic-sine Fourier tail

The boundary-root equation and the leading approximations give the signed Fourier half-sum with a one-derivative remainder.
-/

noncomputable section
open Set Complex NLS.Fourier
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat
open BoundaryCondition

/-- At actual roots of either separated characteristic, the next
Hamiltonian sine phase has the signed half-sum of the original Fourier
coefficients with a uniformly bounded H^(s+1) tail error. -/
theorem exists_uniform_boundary_sinh_fourier_tail_bound
    (s : ℕ) (hs : 1 ≤ s) (R D M : ℝ) (hR : 0 ≤ R) (hD : 0 ≤ D) (hM : 0 ≤ M) :
    ∃ K : ℕ, 0 < K ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ K' : ℕ, K ≤ K' → ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ∀ ha : ContDiff ℝ ∞ a, ∀ hb : ContDiff ℝ ∞ b,
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ δ : NLS.Coeff ⊤, ‖δ‖ ≤ D →
      (∀ n : ℤ, (1+|(n:ℝ)|)*‖δ n‖ ≤ M) → ∀ θ : BoundaryCondition,
      (∀ n : ℤ, K' ≤ n.natAbs → classicalSeparatedCharacteristic θ
        (classicalPotentialOfFunctions a b ha.continuous hb.continuous) ((Real.pi:ℂ)*n+δ n) = 0) →
      ∃ f : ScalarSobolev (s+1),
        (∀ n, f.val n = if K' ≤ n.natAbs then
          sinh (nlsHamiltonianPhase a b (s+1) ((Real.pi:ℂ)*n+δ n))+
            (extensionSign θ*I/2)*(exp (I*((Real.pi:ℂ)*n))*ab.2.val n+
              exp (-I*((Real.pi:ℂ)*n))*ab.1.val (-n))
          else 0) ∧ ‖f‖ ≤ C := by
  classical
  obtain ⟨K₀,hK₀,C₀,hC₀,hphase⟩ := exists_uniform_nlsWKB_boundary_next_phase_tail_bound s hs R D hR hD
  obtain ⟨K₁,_,C₁,hC₁,hlead⟩ := exists_uniform_nlsWKB_boundary_next_leading_fourier_tail_bound s R D M hR hD hM
  obtain ⟨K₂,_,_,_,hfactor⟩ := exists_uniform_nlsWKB_boundary_next_factor_decay s s le_rfl R D hR hD
  let K := max K₀ (max K₁ K₂)
  refine ⟨K,hK₀.trans_le (le_max_left _ _),C₀+C₁+C₁,by positivity,?_⟩
  intro K' hK' ab hab a b ha hb hpa hpb hca hcb δ hδD hδM θ hroot
  have hKs : K₀ ≤ K' ∧ K₁ ≤ K' ∧ K₂ ≤ K' := by dsimp only [K] at hK'; omega
  obtain ⟨e,he,hen⟩ := hphase K' hKs.1 ab hab a b ha hb hpa hpb hca hcb δ hδD θ hroot
  obtain ⟨f,g,hf,hg,hfn,hgn⟩ := hlead K' hKs.2.1 ab hab a b ha hb hpa hpb hca hcb δ hδD hδM θ
  refine ⟨e-(extensionSign θ/2) • (f-g),?_,?_⟩
  · intro n
    rw [WeightedCoeff.sub_val,WeightedCoeff.smul_val,WeightedCoeff.sub_val,he n,hf n,hg n]
    by_cases hn : K' ≤ n.natAbs
    · simp only [if_pos hn]
      have hfac := hfactor ab hab a b ha hb hpa hpb hca hcb δ hδD n (hKs.2.2.trans hn) θ
      have hh := wkb_boundary_next_leading_combination θ
        (nlsWKBInitialLower a b s ((Real.pi:ℂ)*n+δ n))
        (nlsWKBInitialUpper a b s ((Real.pi:ℂ)*n+δ n))
        (nlsWKBLeadingTerm a b s ((Real.pi:ℂ)*n+δ n) 1)
        (nlsWKBLeadingTerm (-b) (-a) s (-((Real.pi:ℂ)*n+δ n)) 1) hfac.1 hfac.2.1
      linear_combination -hh
    · simp only [if_neg hn,sub_self,mul_zero]
  · have hη : ‖extensionSign θ/2‖ ≤ 1 := by cases θ <;> norm_num [extensionSign,norm_div]
    have hm : ‖(extensionSign θ/2) • (f-g)‖ ≤ C₁+C₁ := by
      rw [norm_smul]
      apply (mul_le_mul_of_nonneg_right hη (norm_nonneg _)).trans
      simpa only [one_mul] using (norm_sub_le f g).trans (add_le_add hfn hgn)
    exact (norm_sub_le _ _).trans ((add_le_add hen hm).trans_eq (by ring))

end NLS.ZakharovShabat
