import NLS.Articles.KdVKdV2Frequencies.IntermediateFrequencyOrigin
import NLS.Articles.KdVKdV2Frequencies.Theorem12CompactDerivative
import NLS.SequenceSpaces.CompactScalarConeLocalInverse

/-! Generic real local inverses of the ACTUAL intermediate frequency.
The scalar family is fixed before the choice of action regularity. -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV NLS.ZakharovShabat
open NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

theorem exists_intermediate_real_frequency_inverse
    (D : GlobalRoughAbelianForwardData) (E : PhysicalHstarExtension)
    (α : ℝ) (hα0 : -1<α) (hα1 : α<0)
    (V : Set (Coeff 1)) (G : ℕ+ → Coeff 1 → ℂ)
    (hV : IsOpen V) (hCV : Coeff.nonnegativeLocus 1⊆V) (hG : ∀ n, AnalyticOnNhd ℂ (G n) V)
    (hrec : ∀ (P : PhysicalFrequencyPairChart D) (z : Coeff 2 × Coeff 2),
      z∈P.domain → z∈Coeff.realPairLocus 2 → ∀ n,
        G n (quadraticActionsExponent (q := 1) z)=P.correction n z) :
    ∃ U : Set (Coeff 1), ∃ F : Coeff 1 → Coeff 1,
      IsOpen U ∧ Coeff.nonnegativeLocus 1⊆U ∧ AnalyticOnNhd ℂ F U ∧
      (∀ b∈Coeff.nonnegativeLocus 1, F b∈Coeff.realLocus 1) ∧
      (∀ b∈Coeff.nonnegativeLocus 1, ∀ n : ℕ+,
        F b (actionIndexEquiv.symm n)=(Weight.sobolev α (n : ℤ) : ℂ)*
          G n (normalizedSobolevWeakActionInclusion α (by linarith) b)) ∧
      ∃ O : Set (Coeff.nonnegativeLocus 1), IsOpen O ∧ Dense O ∧
        (⟨0,Coeff.zero_mem_nonnegativeLocus 1⟩ : Coeff.nonnegativeLocus 1)∈O ∧
        ∀ x∈O, ComplexAnalysis.HasAnalyticInverse (𝕜 := ℝ)
          (Coeff.realRestriction F) (Coeff.reCLM 1 x.val) := by
  obtain ⟨U,F₀,hU,hCU,hF₀,_hzero,hpair⟩ := exists_global_negativeWeighted_physical_action_packet
    D (-α) ((α+1)/2) (by linarith) (by linarith) (by linarith) (by ring)
  let F := fun b => weakActionEnumeration (F₀ b)
  have hF : AnalyticOnNhd ℂ F U := analyticOnNhd_postcompose_clm weakActionEnumeration F₀ U hF₀
  have hcal (b : Coeff 1) (hb : b∈Coeff.nonnegativeLocus 1) (n : ℕ+) :
      F b (actionIndexEquiv.symm n)=(Weight.sobolev α (n : ℤ) : ℂ)*
        G n (normalizedSobolevWeakActionInclusion α (by linarith) b) := by
    have he := negativeWeighted_packet_agrees_actual_weak_frequency D (-α) ((α+1)/2)
      (by linarith) (by linarith) (by linarith) (by ring) U F₀ hU hCU hF₀ hpair V G hV hCV hG hrec b hb n
    simpa only [F,weakActionEnumeration_apply,Equiv.apply_symm_apply,neg_neg] using he
  have hreal (b : Coeff 1) (hb : b∈Coeff.nonnegativeLocus 1) : F b∈Coeff.realLocus 1 := by
    intro k
    have h := hcal b hb (actionIndexEquiv k)
    rw [Equiv.symm_apply_apply] at h
    rw [h]
    have hr := actual_weak_family_real_on_cone D G hrec _
      (normalizedSobolevWeakActionInclusion_nonnegative α (by linarith) b hb) (actionIndexEquiv k)
    simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,hr,mul_zero,zero_mul,add_zero]
  obtain ⟨Ω,I,hΩ,hΩr,hI,hIrec,_hpos,_hzeroI,_hI0,_hinv⟩ := exists_global_analytic_weighted_Arnold_action_map
  have hc (b : Coeff 1) (hb : b∈Coeff.nonnegativeLocus 1) :
      IsCompactOperator (fderiv ℂ F b-(-6 : ℂ) • ContinuousLinearMap.id ℂ (Coeff 1)) := by
    have h := global_negativeWeighted_corrected_derivative_compact D (-α) ((α+1)/2)
      (by linarith) (by linarith) (by linarith) (by ring) Ω hΩr I hI hΩ hIrec U F₀ hU hCU hF₀ hpair b hb
    simpa only [neg_smul,sub_neg_eq_add] using h
  have h0 := intermediate_frequency_origin_normalization D E α hα0 hα1 U F₀ hU hCU hF₀ hpair
    V G hV hCV hG hrec
  obtain ⟨O,hO,hdO,hz,hi⟩ := Coeff.exists_open_dense_real_inverse_of_compact_scalar_derivative
    U F hU hCU hF hreal (-6) (by norm_num) hc h0.2
  exact ⟨U,F,hU,hCU,hF,hreal,hcal,O,hO,hdO,hz,fun x hx => (hi x hx).2.2⟩

end NLS.Articles.KdVKdV2Frequencies
