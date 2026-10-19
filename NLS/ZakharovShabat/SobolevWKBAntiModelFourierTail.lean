import NLS.ZakharovShabat.SobolevWKBBothOffDiagonalTails
import NLS.ZakharovShabat.SobolevWKBDiagonalFourierTail
import NLS.SequenceSpaces.WeightedMultiplier

/-! # The sharp anti-discriminant model error

The actual anti-discriminant minus its WKB model has a uniformly bounded H^(s+1) tail on original Hs balls.
-/

noncomputable section
open Set Complex NLS.Fourier NLS.LinearVolterra
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- The actual anti-discriminant minus its WKB model is an H^(s+1) tail
uniformly on the original Hs ball. Every cutoff above the common threshold
is allowed, and no spectral-root equation is assumed. -/
theorem exists_uniform_nlsWKB_anti_model_fourier_tail_bound
    (s : ℕ) (hs : 1 ≤ s) (R D M : ℝ) (hR : 0 ≤ R) (hD : 0 ≤ D) :
    ∃ K : ℕ, 0 < K ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ K' : ℕ, K ≤ K' → ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ∀ ha : ContDiff ℝ ∞ a, ∀ hb : ContDiff ℝ ∞ b,
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ δ : NLS.Coeff ⊤, ‖δ‖ ≤ D →
      (∀ n : ℤ, (1+|(n:ℝ)|)*‖δ n‖ ≤ M) →
      ∃ f : ScalarSobolev (s+1),
        (∀ n, f.val n = if K' ≤ n.natAbs then
          let z := (Real.pi:ℂ)*n+δ n
          classicalAntiDiscriminant (classicalPotentialOfFunctions a b ha.continuous hb.continuous) z-
            nlsWKBAntiDiscriminantModel a b s z
          else 0) ∧ ‖f‖ ≤ C := by
  classical
  obtain ⟨K₀,hK₀,C₀,hC₀,hdiag⟩ := exists_uniform_nlsWKB_diagonal_fourier_tail_bound s hs R D M hR hD
  obtain ⟨K₁,_,C₁,hC₁,hoff⟩ := exists_uniform_nlsWKB_both_offDiagonal_tail_bound s s hs le_rfl R D M hR hD
  obtain ⟨K₂,_,hgeom⟩ := exists_wkb_leading_frequency_cutoff D M hD
  obtain ⟨T,_,hbasis⟩ := exists_uniform_nlsWKB_initial_basis_bounds s s le_rfl R hR
  obtain ⟨L,hL⟩ := exists_nat_ge T
  let K := max K₀ (max K₁ (max K₂ L))
  refine ⟨K,hK₀.trans_le (le_max_left _ _),2*(C₀+C₁+C₁),by positivity,?_⟩
  intro K' hKK' ab hab a b ha hb hpa hpb hca hcb δ hδD hδM
  have hK₀ : K₀ ≤ K' := (le_max_left _ _).trans hKK'
  have hK₁ : K₁ ≤ K' := (le_max_left _ _).trans ((le_max_right _ _).trans hKK')
  have hK₂ : K₂ ≤ K' := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hKK'))
  have hLK : L ≤ K' := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hKK'))
  obtain ⟨q,hq,hqn⟩ := hdiag ab hab a b ha hb hpa hpb hca hcb δ hδD hδM
  obtain ⟨f,g,hf,hg,hfn,hgn⟩ := hoff ab hab a b ha hb hpa hpb hca hcb δ hδD hδM 1
  let ν (n : ℤ) := (Real.pi:ℂ)*n+δ n
  let d (n : ℤ) := 1-nlsWKBInitialLower a b s (ν n)*nlsWKBInitialUpper a b s (ν n)
  have hdet (n : ℤ) (hn : K' ≤ n.natAbs) : d n ≠ 0 ∧ ‖(d n)⁻¹‖ ≤ 2 := by
    have hδ (j : ℤ) : ‖δ j‖ ≤ D := (lp.norm_apply_le_norm (by simp) δ j).trans hδD
    have hz := (hgeom δ hδ hδM n (hK₂.trans hn)).2
    have hnL : (L:ℝ) ≤ (n.natAbs:ℝ) := by exact_mod_cast hLK.trans hn
    have hT : T ≤ ‖ν n‖ := by
      change 1+|(n:ℝ)| ≤ ‖ν n‖ at hz
      have habs : |(n:ℝ)| = (n.natAbs:ℝ) := by simp
      rw [habs] at hz
      linarith
    exact (hbasis ab hab a b ha hb hpa hpb hca hcb (ν n) hT).2.2
  let v := Weight.sobolev ((s+1:ℕ):ℝ)
  let m (n : ℤ) : ℂ := if K' ≤ n.natAbs then (d n)⁻¹ else 0
  have hm (n : ℤ) : v n*‖m n‖ ≤ 2*v n := by
    by_cases hn : K' ≤ n.natAbs
    · simp only [m,if_pos hn]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hdet n hn).2 (v.positive n).le
    · simp only [m,if_neg hn,norm_zero,mul_zero]
      exact mul_nonneg (by norm_num) (v.positive n).le
  refine ⟨WeightedCoeff.weightedMultiplier v v m 2 hm (q-f-g),?_,?_⟩
  · intro n
    change m n*((q-f-g).val n) = _
    rw [WeightedCoeff.sub_val,WeightedCoeff.sub_val,hq n,hf n,hg n]
    by_cases hn : K' ≤ n.natAbs
    · simp only [m,if_pos hn,if_pos (hK₀.trans hn),if_pos (hK₁.trans hn)]
      have he := classicalAntiDiscriminant_sub_wkb_model_exact a b ha.continuous hb.continuous s (ν n) (hdet n hn).1
      dsimp only at he
      change (d n)⁻¹*(_-_-_) = _
      rw [← he]
      change (d n)⁻¹*(d n*_)=_
      rw [← mul_assoc,inv_mul_cancel₀ (hdet n hn).1,one_mul]
    · simp [m,hn]
  · apply (WeightedCoeff.norm_weightedMultiplier_le v v m 2 (by norm_num) hm (q-f-g)).trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
    exact (norm_sub_le _ _).trans ((add_le_add (norm_sub_le _ _) le_rfl).trans
      (add_le_add (add_le_add hqn hfn) hgn))

end NLS.ZakharovShabat
