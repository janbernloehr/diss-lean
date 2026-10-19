import NLS.SequenceSpaces.SobolevDecayingLeadingTail
import NLS.ZakharovShabat.SobolevWKBInitialDecay
import NLS.ZakharovShabat.WKBLeadingFrequencyCutoff
import NLS.ZakharovShabat.SobolevWKBBothLeadingFourierTails

/-! # The leading terms in the trace identity

Both leading oscillatory terms multiplied by their small initial coordinates have uniformly bounded H^(s+1) tails.
-/

noncomputable section
open Set Complex NLS.Fourier
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- Both leading oscillatory terms, multiplied by their small initial
coordinates in the trace identity, have H^(s+1) tails on original Hs
balls with a common bound at every larger cutoff. -/
theorem exists_uniform_nlsWKB_trace_leading_fourier_tail_bound
    (s : ℕ) (R D M : ℝ) (hR : 0 ≤ R) (hD : 0 ≤ D) (hM : 0 ≤ M) :
    ∃ K : ℕ, 0 < K ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ K' : ℕ, K ≤ K' → ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ δ : NLS.Coeff ⊤, ‖δ‖ ≤ D →
      (∀ n : ℤ, (1+|(n:ℝ)|)*‖δ n‖ ≤ M) →
      ∃ f g : ScalarSobolev (s+1),
        (∀ n, f.val n = if K' ≤ n.natAbs then
          let z := (Real.pi:ℂ)*n+δ n
          nlsWKBInitialUpper a b s z*
            nlsWKBLeadingTerm a b s z 1 else 0) ∧
        (∀ n, g.val n = if K' ≤ n.natAbs then
          let z := (Real.pi:ℂ)*n+δ n
          nlsWKBInitialLower a b s z*
            nlsWKBLeadingTerm (-b) (-a) s (-z) 1 else 0) ∧
        ‖f‖ ≤ C ∧ ‖g‖ ≤ C := by
  obtain ⟨K₀,hK₀,C₀,hC₀,hlead⟩ := exists_uniform_nlsWKB_both_leading_fourier_tail_error_bound s R D M hR hD hM
  obtain ⟨K₁,_,hcut⟩ := exists_wkb_leading_frequency_cutoff D M hD
  obtain ⟨B,hB,hinit⟩ := exists_uniform_nlsWKB_initial_coordinate_decay s s le_rfl R hR
  refine ⟨max K₀ K₁,hK₀.trans_le (le_max_left _ _),B*C₀+B*R,by positivity,?_⟩
  intro K' hK' ab hab a b ha hb hpa hpb hca hcb δ hδD hδM
  have hK₀ : K₀ ≤ K' := (le_max_left _ _).trans hK'
  have hK₁ : K₁ ≤ K' := (le_max_right _ _).trans hK'
  obtain ⟨e₁,e₂,he₁,he₂,he₁n,he₂n⟩ := hlead ab hab a b ha hb hpa hpb hca hcb δ hδD hδM
  let ν (n : ℤ) := (Real.pi:ℂ)*n+δ n
  let p (n : ℤ) := nlsWKBInitialLower a b s (ν n)
  let q (n : ℤ) := nlsWKBInitialUpper a b s (ν n)
  have hfactors (n : ℤ) (hn : K' ≤ n.natAbs) :
      ‖p n‖ ≤ B ∧ ‖q n‖ ≤ B ∧ (1+|(n:ℝ)|)*‖p n‖ ≤ B ∧ (1+|(n:ℝ)|)*‖q n‖ ≤ B := by
    have hδ (j : ℤ) : ‖δ j‖ ≤ D := (lp.norm_apply_le_norm (by simp) δ j).trans hδD
    have hgeom := (hcut δ hδ hδM n (hK₁.trans hn)).2
    change 1+|(n:ℝ)| ≤ ‖ν n‖ at hgeom
    have hz : 1 ≤ ‖ν n‖ := by linarith [abs_nonneg (n:ℝ)]
    have hw : (1+|(n:ℝ)|)*‖(2*I*ν n)⁻¹‖ ≤ 1 := by
      simp only [norm_inv,norm_mul,norm_ofNat,norm_I,mul_one]
      rw [← div_eq_mul_inv]
      apply (div_le_one (by linarith : 0 < 2*‖ν n‖)).mpr
      linarith
    have hw1 : ‖(2*I*ν n)⁻¹‖ ≤ 1 := by
      nlinarith [norm_nonneg ((2*I*ν n)⁻¹),abs_nonneg (n:ℝ)]
    have hi := hinit ab hab a b ha hb hpa hpb hca hcb (ν n) hz
    have hp : ‖p n‖ ≤ B := hi.1.trans (mul_le_of_le_one_right hB hw1)
    have hq : ‖q n‖ ≤ B := hi.2.trans (mul_le_of_le_one_right hB hw1)
    have hdec (v : ℂ) (hv : ‖v‖ ≤ B*‖(2*I*ν n)⁻¹‖) : (1+|(n:ℝ)|)*‖v‖ ≤ B := by
      calc
        _ ≤ (1+|(n:ℝ)|)*(B*‖(2*I*ν n)⁻¹‖) := mul_le_mul_of_nonneg_left hv (by positivity)
        _ = B*((1+|(n:ℝ)|)*‖(2*I*ν n)⁻¹‖) := by ring
        _ ≤ B*1 := mul_le_mul_of_nonneg_left hw hB
        _ = B := mul_one B
    exact ⟨hp,hq,hdec (p n) hi.1,hdec (q n) hi.2⟩
  have hphase₁ (n : ℤ) : ‖I*exp (I*((Real.pi:ℂ)*n))‖ ≤ 1 := by
    simp [norm_exp,Complex.mul_re,Complex.mul_im]
  have hphase₂ (n : ℤ) : ‖-I*exp (-I*((Real.pi:ℂ)*n))‖ ≤ 1 := by
    simp [norm_exp,Complex.mul_re,Complex.mul_im]
  obtain ⟨f,hf,hfn⟩ := WeightedCoeff.exists_sobolev_decaying_leading_tail s K₀ K' hK₀ ab.2 e₁
    (fun n => nlsWKBLeadingTerm a b s (ν n) 1) (fun n => I*exp (I*((Real.pi:ℂ)*n)))
    q B B hB hB he₁ hphase₁
    (fun n hn => (hfactors n hn).2.1) (fun n hn => (hfactors n hn).2.2.2)
  let a' := WeightedCoeff.reflection (s:ℝ) ab.1
  have he₂' (n : ℤ) : e₂.val n = if K₀ ≤ n.natAbs then
      nlsWKBLeadingTerm (-b) (-a) s (-(ν n)) 1-(-I*exp (-I*((Real.pi:ℂ)*n)))*a'.val n else 0 := by
    simpa only [a',WeightedCoeff.reflection_apply,neg_mul,sub_neg_eq_add] using he₂ n
  obtain ⟨g,hg,hgn⟩ := WeightedCoeff.exists_sobolev_decaying_leading_tail s K₀ K' hK₀ a' e₂
    (fun n => nlsWKBLeadingTerm (-b) (-a) s (-(ν n)) 1) (fun n => -I*exp (-I*((Real.pi:ℂ)*n)))
    p B B hB hB he₂' hphase₂
    (fun n hn => (hfactors n hn).1) (fun n hn => (hfactors n hn).2.2.1)
  refine ⟨f,g,hf,hg,?_,?_⟩
  · exact hfn.trans (add_le_add (mul_le_mul_of_nonneg_left he₁n hB)
      (mul_le_mul_of_nonneg_left ((norm_snd_le ab).trans hab) hB))
  · apply hgn.trans
    have ha' : ‖a'‖ ≤ R := by simpa only [a',LinearIsometryEquiv.norm_map] using (norm_fst_le ab).trans hab
    exact add_le_add (mul_le_mul_of_nonneg_left he₂n hB)
      (mul_le_mul_of_nonneg_left ha' hB)

end NLS.ZakharovShabat
