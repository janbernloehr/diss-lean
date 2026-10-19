import NLS.ZakharovShabat.SobolevWKBAntiModelFourierTail
import NLS.ZakharovShabat.SobolevWKBBoundaryLeadingTails
import NLS.ZakharovShabat.SobolevWKBBoundarySeparatedErrorTail
import NLS.ZakharovShabat.NLSWKBBoundaryLeadingCombination

/-! # The actual boundary anti-discriminant Fourier tail

At zeros of either separated characteristic, the actual anti-discriminant has its signed Fourier leading terms and an H^(s+1) tail.
-/

noncomputable section
open Set Complex NLS.Fourier NLS.LinearVolterra
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- At zeros of either actual separated characteristic, the actual
anti-discriminant has its original two Fourier coefficients with a
uniform H^(s+1) tail on the original Hs ball. The cutoff is uniform and
may be increased without changing the bound. -/
theorem exists_uniform_boundary_anti_fourier_tail_bound
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
          classicalAntiDiscriminant (classicalPotentialOfFunctions a b ha.continuous hb.continuous) ((Real.pi:ℂ)*n+δ n)+
            I*exp (I*((Real.pi:ℂ)*n))*ab.2.val n-I*exp (-I*((Real.pi:ℂ)*n))*ab.1.val (-n)
          else 0) ∧ ‖f‖ ≤ C := by
  classical
  obtain ⟨K₀,hK₀,C₀,hC₀,hanti⟩ := exists_uniform_nlsWKB_anti_model_fourier_tail_bound s hs R D M hR hD
  obtain ⟨K₁,_,C₁,hC₁,hlead⟩ := exists_uniform_nlsWKB_boundary_leading_fourier_tail_bound s R D M hR hD hM
  obtain ⟨K₂,_,C₂,hC₂,hsep⟩ := exists_uniform_nlsWKB_boundary_separated_error_tail_bound s hs R D M hR hD
  obtain ⟨K₃,_,_,_,hfactor⟩ := exists_uniform_nlsWKB_boundary_factor_decay s s le_rfl R D M hR hD
  let K := max K₀ (max K₁ (max K₂ K₃))
  refine ⟨K,hK₀.trans_le (le_max_left _ _),C₀+C₁+C₁+C₂,by positivity,?_⟩
  intro K' hK' ab hab a b ha hb hpa hpb hca hcb δ hδD hδM θ hroot
  have hK₀ : K₀ ≤ K' := (le_max_left _ _).trans hK'
  have hK₁ : K₁ ≤ K' := (le_max_left _ _).trans ((le_max_right _ _).trans hK')
  have hK₂ : K₂ ≤ K' := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hK'))
  have hK₃ : K₃ ≤ K' := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hK'))
  obtain ⟨e,he,hen⟩ := hanti K' hK₀ ab hab a b ha hb hpa hpb hca hcb δ hδD hδM
  obtain ⟨f,g,hf,hg,hfn,hgn⟩ := hlead K' hK₁ ab hab a b ha hb hpa hpb hca hcb δ hδD hδM θ
  obtain ⟨q,hq,hqn⟩ := hsep K' hK₂ ab hab a b ha hb hpa hpb hca hcb δ hδD hδM θ
  refine ⟨e-f-g+q,?_,?_⟩
  · intro n
    rw [WeightedCoeff.add_val,WeightedCoeff.sub_val,WeightedCoeff.sub_val,he n,hf n,hg n,hq n]
    by_cases hn : K' ≤ n.natAbs
    · simp only [if_pos hn,hroot n hn,sub_zero]
      have hfactors := hfactor ab hab a b ha hb hpa hpb hca hcb δ hδD hδM n (hK₃.trans hn) θ
      have hh := nlsWKB_anti_boundary_leading_combination a b ha hb hpa hpb s
        ((Real.pi:ℂ)*n+δ n) θ hfactors.1 hfactors.2.1
      dsimp only at hh
      linear_combination -hh
    · simp [hn]
  · exact (norm_add_le _ _).trans ((add_le_add
      ((norm_sub_le _ _).trans ((add_le_add (norm_sub_le _ _) le_rfl).trans
        (add_le_add (add_le_add hen hfn) hgn))) hqn))

end NLS.ZakharovShabat
