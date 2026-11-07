import NLS.ZakharovShabat.SourceWeightedSignedTerminal
import NLS.ZakharovShabat.SourceHillWeightedTerminalModel
import NLS.SequenceSpaces.WeightedMultiplier
import NLS.ZakharovShabat.SourceSection14WeightedMembership

/-! # The physical Hill terminal at every nonnegative Dirac Sobolev order

The exact square-root frequency normalization shifts the output order by
minus one half. The actual bounded normalized midpoint symbol is retained.
-/
noncomputable section
open Set Metric Complex NLS.WeightedCoeff
namespace NLS.ZakharovShabat

theorem fractionalHillTerminal_symbol_bound (t : ℝ) (ht : 0 ≤ t) (k : ℤ) :
    Weight.signedSobolev (t-1/2) k*
        ‖sourceHillTerminalScale/(Weight.signedSobolev (-1/2) k:ℂ)‖ ≤
      ‖sourceHillTerminalScale‖*sourceFrequencyWeight (sourceSobolevSpectralWeight t ht) k := by
  have hw : Weight.signedSobolev (t-1/2) k =
      Weight.signedSobolev t k*Weight.signedSobolev (-1/2) k := by
    change (max 1 |(k:ℝ)|)^(t-1/2) = (max 1 |(k:ℝ)|)^t*(max 1 |(k:ℝ)|)^(-1/2:ℝ)
    rw [← Real.rpow_add (by positivity : (0:ℝ)<max 1 |(k:ℝ)|)]
    congr 1
    ring
  have hcomp : Weight.signedSobolev t k ≤ sourceFrequencyWeight (sourceSobolevSpectralWeight t ht) k := by
    rw [sourceFrequencyWeight_sobolev]
    change (max 1 |(k:ℝ)|)^t ≤ (1+|(k:ℝ)|)^t
    exact Real.rpow_le_rpow (by positivity)
      (max_le (by linarith [abs_nonneg (k:ℝ)]) (by linarith)) ht
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ((Weight.signedSobolev (-1/2)).positive k),hw]
  have hcancel (a b d : ℝ) (hd : d ≠ 0) : (a*d)*(b/d) = b*a := by
    field_simp
  have he : (Weight.signedSobolev t k*Weight.signedSobolev (-1/2) k)*
      (‖sourceHillTerminalScale‖/Weight.signedSobolev (-1/2) k) =
      ‖sourceHillTerminalScale‖*Weight.signedSobolev t k :=
    hcancel _ _ _ (ne_of_gt ((Weight.signedSobolev (-1/2)).positive k))
  rw [he]
  exact mul_le_mul_of_nonneg_left hcomp (norm_nonneg _)

def fractionalHillTerminalCLM (t : ℝ) (ht : 0 ≤ t) :
    WeightedCoeff (sourceFrequencyWeight (sourceSobolevSpectralWeight t ht)) 2 →L[ℂ]
      WeightedCoeff (Weight.signedSobolev (t-1/2)) 2 :=
  weightedMultiplierCLM _ _ (fun k => sourceHillTerminalScale/(Weight.signedSobolev (-1/2) k:ℂ))
    ‖sourceHillTerminalScale‖ (norm_nonneg _) (fractionalHillTerminal_symbol_bound t ht)

theorem fractionalHillTerminalCLM_apply (t : ℝ) (ht : 0 ≤ t)
    (a : WeightedCoeff (sourceFrequencyWeight (sourceSobolevSpectralWeight t ht)) 2) (k : ℤ) :
    (fractionalHillTerminalCLM t ht a).val k =
      sourceHillTerminalScale/(Weight.signedSobolev (-1/2) k:ℂ)*a.val k := rfl

def sourceFractionalHillTerminal (t : ℝ) (ht : 0 ≤ t) (ψ : CoeffPair 2) :
    WeightedCoeff (Weight.signedSobolev (t-1/2)) 2 :=
  boundedSymbolBilinear _
    (sourceNormalizedMidpointSymbol (by norm_num) (by norm_num)
      (normalizedWeightedSource (sourceSobolevSpectralWeight t ht) ψ))
    (fractionalHillTerminalCLM t ht
      (normalizedWeightedSignedTerminal (sourceSobolevSpectralWeight t ht) ψ))

theorem sourceFractionalHillTerminal_apply_of_terminal
    (t : ℝ) (ht : 0 ≤ t) (ψ : CoeffPair 2)
    (hT : ∀ k, (normalizedWeightedSignedTerminal (sourceSobolevSpectralWeight t ht) ψ).val k =
      sourceSignedTerminalSequence (normalizedWeightedSource (sourceSobolevSpectralWeight t ht) ψ) k)
    (k : ℤ) :
    (sourceFractionalHillTerminal t ht ψ).val k =
      (sourceHillTerminalModel (normalizedWeightedSource (sourceSobolevSpectralWeight t ht) ψ)).val k := by
  have he := sourceHillTerminalModel_weighted_apply
    (normalizedWeightedSource (sourceSobolevSpectralWeight t ht) ψ) k
  change (Weight.signedSobolev (-1/2) k:ℂ)*
    (sourceHillTerminalModel (normalizedWeightedSource (sourceSobolevSpectralWeight t ht) ψ)).val k = _ at he
  have hne := (Weight.signedSobolev (-1/2)).complex_ne_zero k
  apply (mul_left_cancel₀ hne)
  change (Weight.signedSobolev (-1/2) k:ℂ)*
    (sourceNormalizedMidpointSymbol (by norm_num) (by norm_num)
      (normalizedWeightedSource (sourceSobolevSpectralWeight t ht) ψ) k*
      (fractionalHillTerminalCLM t ht
        (normalizedWeightedSignedTerminal (sourceSobolevSpectralWeight t ht) ψ)).val k) = _
  rw [fractionalHillTerminalCLM_apply,hT,he]
  have hcancel (a b c d : ℂ) (hd : d ≠ 0) : d*(a*(b/d*c)) = b*a*c := by
    field_simp
  exact hcancel _ _ _ _ hne

theorem exists_local_sourceFractionalHillTerminal_analytic
    (t : ℝ) (ht : 0 ≤ t) (φ : realTypeSourceLocus 2) :
    ∃ U : Set (CoeffPair 2), IsOpen U ∧ φ.val ∈ U ∧
      AnalyticOnNhd ℂ (sourceFractionalHillTerminal t ht) U ∧
      ∀ ψ ∈ U, ∀ k, (sourceFractionalHillTerminal t ht ψ).val k =
        (sourceHillTerminalModel (normalizedWeightedSource (sourceSobolevSpectralWeight t ht) ψ)).val k := by
  let w := sourceSobolevSpectralWeight t ht
  obtain ⟨Ut,hUt,hφt,hTa,hTc⟩ := exists_local_normalizedWeightedSignedTerminal_analytic w φ
  obtain ⟨_,_,_,_,V,hV,_,hrealV,_,H⟩ := sourceLemma12_12 (p := 2) (by norm_num) (by norm_num)
  have hφV : normalizedWeightedSource w φ.val ∈ V :=
    hrealV (normalizedWeightedSource_realType w φ.val φ.property)
  let U := Ut ∩ normalizedWeightedSource w ⁻¹' V
  refine ⟨U,hUt.inter (hV.preimage (continuous_normalizedWeightedSource w)),⟨hφt,hφV⟩,?_,?_⟩
  · intro ψ hψ
    have hm := (H.normalized_midpoint_symbol_data.2 _ hψ.2).comp
      ((normalizedWeightedSourceCLM w).analyticAt ψ)
    have hterm := ((fractionalHillTerminalCLM t ht).analyticAt _).comp (hTa ψ hψ.1)
    exact ((boundedSymbolBilinear (Weight.signedSobolev (t-1/2))).analyticAt_bilinear _).comp
      (f := fun a => (sourceNormalizedMidpointSymbol (by norm_num) (by norm_num)
        (normalizedWeightedSource w a),fractionalHillTerminalCLM t ht (normalizedWeightedSignedTerminal w a)))
      (hm.prod hterm)
  · intro ψ hψ k
    exact sourceFractionalHillTerminal_apply_of_terminal t ht ψ (hTc ψ hψ.1) k

end NLS.ZakharovShabat
