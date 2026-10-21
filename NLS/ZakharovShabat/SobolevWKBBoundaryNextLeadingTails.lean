import NLS.ZakharovShabat.SobolevWKBBoundaryNextFactorDecay
import NLS.SequenceSpaces.SobolevLeadingMultiplierTail
import NLS.ZakharovShabat.SobolevWKBBothLeadingFourierTails

/-! # Fourier coefficients of the normalized next-phase integrals

The normalized leading integrals retain the two original signed Fourier coefficients with sharp Sobolev tails.
-/

noncomputable section
open Set Complex NLS.Fourier
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- Both next-phase factors preserve the original leading Fourier
coefficients up to H^(s+1) tails on original Hs balls. The bound holds for
both boundary conditions and every larger cutoff. -/
theorem exists_uniform_nlsWKB_boundary_next_leading_fourier_tail_bound
    (s : ℕ) (R D M : ℝ) (hR : 0 ≤ R) (hD : 0 ≤ D) (hM : 0 ≤ M) :
    ∃ K : ℕ, 0 < K ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ K' : ℕ, K ≤ K' → ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ δ : NLS.Coeff ⊤, ‖δ‖ ≤ D →
      (∀ n : ℤ, (1+|(n:ℝ)|)*‖δ n‖ ≤ M) → ∀ θ : BoundaryCondition,
      ∃ f g : ScalarSobolev (s+1),
        (∀ n, f.val n = if K' ≤ n.natAbs then
          let z := (Real.pi:ℂ)*n+δ n
          wkbBoundaryNextLeadingFactor θ (nlsWKBInitialLower a b s z)*
            nlsWKBLeadingTerm a b s z 1-I*exp (I*((Real.pi:ℂ)*n))*ab.2.val n else 0) ∧
        (∀ n, g.val n = if K' ≤ n.natAbs then
          let z := (Real.pi:ℂ)*n+δ n
          wkbBoundaryNextLeadingFactor θ (nlsWKBInitialUpper a b s z)*
            nlsWKBLeadingTerm (-b) (-a) s (-z) 1+I*exp (-I*((Real.pi:ℂ)*n))*ab.1.val (-n) else 0) ∧
        ‖f‖ ≤ C ∧ ‖g‖ ≤ C := by
  obtain ⟨K₀,hK₀,C₀,hC₀,hlead⟩ := exists_uniform_nlsWKB_both_leading_fourier_tail_error_bound s R D M hR hD hM
  obtain ⟨K₁,_,C₁,hC₁,hfactor⟩ := exists_uniform_nlsWKB_boundary_next_factor_decay s s le_rfl R D hR hD
  refine ⟨max K₀ K₁,hK₀.trans_le (le_max_left _ _),2*C₀+C₁*R,by positivity,?_⟩
  intro K' hK' ab hab a b ha hb hpa hpb hca hcb δ hδD hδM θ
  have hK₀ : K₀ ≤ K' := (le_max_left _ _).trans hK'
  have hK₁ : K₁ ≤ K' := (le_max_right _ _).trans hK'
  obtain ⟨e₁,e₂,he₁,he₂,he₁n,he₂n⟩ := hlead ab hab a b ha hb hpa hpb hca hcb δ hδD hδM
  let ν (n : ℤ) := (Real.pi:ℂ)*n+δ n
  let p (n : ℤ) := nlsWKBInitialLower a b s (ν n)
  let q (n : ℤ) := nlsWKBInitialUpper a b s (ν n)
  have hfactors (n : ℤ) (hn : K' ≤ n.natAbs) := hfactor ab hab a b ha hb hpa hpb hca hcb δ hδD n (hK₁.trans hn) θ
  have hphase₁ (n : ℤ) : ‖I*exp (I*((Real.pi:ℂ)*n))‖ ≤ 1 := by
    simp [norm_exp,Complex.mul_re,Complex.mul_im]
  have hphase₂ (n : ℤ) : ‖-I*exp (-I*((Real.pi:ℂ)*n))‖ ≤ 1 := by
    simp [norm_exp,Complex.mul_re,Complex.mul_im]
  obtain ⟨f,hf,hfn⟩ := WeightedCoeff.exists_sobolev_leading_multiplier_tail s K₀ K' hK₀ ab.2 e₁
    (fun n => nlsWKBLeadingTerm a b s (ν n) 1) (fun n => I*exp (I*((Real.pi:ℂ)*n)))
    (fun n => wkbBoundaryNextLeadingFactor θ (p n)) 2 C₁ (by norm_num) hC₁ he₁ hphase₁
    (fun n hn => (hfactors n hn).2.2.1) (fun n hn => (hfactors n hn).2.2.2.2.1)
  let a' := WeightedCoeff.reflection (s:ℝ) ab.1
  have he₂' (n : ℤ) : e₂.val n = if K₀ ≤ n.natAbs then
      nlsWKBLeadingTerm (-b) (-a) s (-(ν n)) 1-(-I*exp (-I*((Real.pi:ℂ)*n)))*a'.val n else 0 := by
    simpa only [a',WeightedCoeff.reflection_apply,neg_mul,sub_neg_eq_add] using he₂ n
  obtain ⟨g,hg,hgn⟩ := WeightedCoeff.exists_sobolev_leading_multiplier_tail s K₀ K' hK₀ a' e₂
    (fun n => nlsWKBLeadingTerm (-b) (-a) s (-(ν n)) 1) (fun n => -I*exp (-I*((Real.pi:ℂ)*n)))
    (fun n => wkbBoundaryNextLeadingFactor θ (q n)) 2 C₁ (by norm_num) hC₁ he₂' hphase₂
    (fun n hn => (hfactors n hn).2.2.2.1) (fun n hn => (hfactors n hn).2.2.2.2.2)
  refine ⟨f,g,hf,?_,?_,?_⟩
  · intro n
    simpa only [a',WeightedCoeff.reflection_apply,neg_mul,sub_neg_eq_add] using hg n
  · exact hfn.trans (add_le_add (mul_le_mul_of_nonneg_left he₁n (by norm_num))
      (mul_le_mul_of_nonneg_left ((norm_snd_le ab).trans hab) hC₁))
  · apply hgn.trans
    have ha' : ‖a'‖ ≤ R := by simpa only [a',LinearIsometryEquiv.norm_map] using (norm_fst_le ab).trans hab
    exact add_le_add (mul_le_mul_of_nonneg_left he₂n (by norm_num))
      (mul_le_mul_of_nonneg_left ha' hC₁)

end NLS.ZakharovShabat
