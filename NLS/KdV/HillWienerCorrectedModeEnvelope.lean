import NLS.KdV.HillWienerTailDomination

/-! One ell-one envelope precedes all high modes, both resonant signs
and every parameter on their full reduced strips, for the actual modes. -/
noncomputable section
open scoped ENNReal
open NLS.WeightedCoeff
namespace NLS.KdV

theorem exists_hillWienerCorrectedMode_envelope (w : SpectralWeight)
    (q : WeightedCoeff (w.negativeSobolev 0) 1) (N : ℕ) (hN : 1 ≤ N)
    (hcut : 8*‖q‖ ≤ (N:ℝ)) :
    ∃ H : Coeff 1, ‖H‖ ≤ 2*‖q‖ ∧
      ∀ (n : ℕ) (hn : 1 ≤ n), N ≤ n → ∀ (z : ℂ) (hz : z ∈ reducedHillStrip n),
        ∀ hs : endpointHillConstant 0*(n:ℝ)^((0:ℝ)-1/2)*
          ‖exponentInclusion _ (show 1 ≤ (⊤:ℝ≥0∞) from le_top) q‖ ≤ 1/2,
        ∀ (j : ℤ), j=(n:ℤ) ∨ j=-(n:ℤ) → ∀ k : ℤ,
          w (k-j)*‖(endpointHillCorrectedMode w 0 (by norm_num) (by norm_num) n hn z hz
            (exponentInclusion _ (show 1 ≤ (⊤:ℝ≥0∞) from le_top) q) hs j).val k‖ ≤ ‖H (k-j)‖ := by
  let a := hillWienerMagnitude w q
  let Q := exponentInclusion (w.negativeSobolev 0) (show 1 ≤ (⊤:ℝ≥0∞) from le_top) q
  let δ := 4/(N:ℝ)
  have hNp : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hsmall : δ*‖a‖ ≤ 1/2 := by
    rw [norm_hillWienerMagnitude]
    change (4/(N:ℝ))*‖q‖ ≤ 1/2
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hNp).mpr
    linarith
  obtain ⟨H,hH,hmajor⟩ := Coeff.exists_convolution_neumann_envelope a
    (Coeff.isNonnegative_magnitude _) δ hδ hsmall
  have hHnorm : ‖H‖ ≤ 2*‖q‖ := by
    change ‖H‖ ≤ 2*‖hillWienerMagnitude w q‖ at hH
    rwa [norm_hillWienerMagnitude] at hH
  refine ⟨H,hHnorm,?_⟩
  intro n hn hNn z hz hs j hj k
  let T := hillWienerNormalizedTail w n hn z hz Q j
  let b := hillWienerNormalize w j (w.negativeModulation 0 (by norm_num) j Q)
  let g := hillWienerNormalize w j (endpointHillCorrectedMode w 0 (by norm_num) (by norm_num)
    n hn z hz Q hs j)
  have hT : ‖T‖ ≤ 1/2 := (norm_hillWienerNormalizedTail_le w n hn z hz Q j hj).trans hs
  have hb (m : ℤ) : ‖b m‖ ≤ ‖a m‖ := by
    change ‖hillWienerNormalize w j (w.negativeModulation 0 (by norm_num) j Q) m‖ ≤
      ‖hillWienerMagnitude w q m‖
    rw [norm_hillWienerMagnitude_apply, hillWienerNormalize_modulation,
      norm_mul, Complex.norm_real, Real.norm_of_nonneg (w.positive m).le, exponentInclusion_apply]
  have hsymbol (m : ℤ) : ‖reducedHillSymbol n hn z hz m‖ ≤ δ := by
    calc
      _ ≤ ‖reducedHillHilbertSymbol n hn z hz‖ :=
        lp.norm_apply_le_norm (by norm_num : (2:ℝ≥0∞) ≠ 0) (reducedHillHilbertSymbol n hn z hz) m
      _ ≤ 4/(n:ℝ) := norm_reducedHillHilbertSymbol_le n hn z hz
      _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) hNp (by exact_mod_cast hNn)
  have hd (f : Coeff ⊤) (v : Coeff 1) (hv : Coeff.IsNonnegative v)
      (hfv : ∀ m, ‖f m‖ ≤ ‖v m‖) (m : ℤ) : ‖T f m‖ ≤ ‖Coeff.positiveConvolutionOperator a δ v m‖ :=
    hillWienerNormalizedTail_positive_domination w q n hn z hz j δ hδ hsymbol f v hv hfv m
  have hg : g-T g=b := by
    exact NLS.FunctionalAnalysis.conjugate_vector_sub_equation (hillWienerNormalize w j)
      (unshiftedEndpointHillPerturbation w 0 (by norm_num) (by norm_num) n hn z hz Q)
      (endpointHillCorrectedMode w 0 (by norm_num) (by norm_num) n hn z hz Q hs j)
      (w.negativeModulation 0 (by norm_num) j Q)
      (endpointHillTailInverse_right w 0 (by norm_num) (by norm_num) n hn z hz Q hs
        (w.negativeModulation 0 (by norm_num) j Q))
  have hh := hmajor T b g hT hb hd hg (k-j)
  change ‖hillWienerNormalize w j (endpointHillCorrectedMode w 0 (by norm_num) (by norm_num)
    n hn z hz Q hs j) (k-j)‖ ≤ _ at hh
  rw [hillWienerNormalize_apply, sub_add_cancel, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (w.positive (k-j)).le] at hh
  exact hh

end NLS.KdV
