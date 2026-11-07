import NLS.ZakharovShabat.SourceWeightedTerminalComplexBound
import NLS.ZakharovShabat.SourceSignedTerminalSequence
import NLS.ZakharovShabat.SourceSection14
import NLS.ZakharovShabat.SourceWeightedRealSpaces
import NLS.SequenceSpaces.WeightedSignedPositiveSplice
import NLS.SequenceSpaces.WeightedAnalyticRealization

/-! # The actual signed Hill terminal in every source spectral weight

Both positive-label terminal signs are retained. The weighted realization
is holomorphic on a common complex neighborhood of each weighted real input.
-/
noncomputable section
open Set Metric Complex NLS.WeightedCoeff
namespace NLS.ZakharovShabat

def normalizedWeightedSignedTerminal (w : SpectralWeight) (ψ : CoeffPair 2) :
    WeightedCoeff (sourceFrequencyWeight w) 2 :=
  ofFunctionOrZero (sourceFrequencyWeight w) 2
    (fun k => sourceSignedTerminalSequence (normalizedWeightedSource w ψ) k)

theorem exists_local_weighted_signedTerminal_bound
    (w : SpectralWeight) (φ : realTypeSourceLocus 2) :
    ∃ U : Set (CoeffPair 2), ∃ M : ℝ, IsOpen U ∧ φ.val ∈ U ∧
      AnalyticOnNhd ℂ (fun ψ => sourceSignedTerminalSequence (normalizedWeightedSource w ψ)) U ∧
      ∀ ψ ∈ U, ∃ b : WeightedCoeff (sourceFrequencyWeight w) 2,
        (∀ k, b.val k = sourceSignedTerminalSequence (normalizedWeightedSource w ψ) k) ∧ ‖b‖ ≤ M := by
  obtain ⟨_,_,_,_,D⟩ := sourceSection14 (p := 2) (by norm_num) (by norm_num)
  obtain ⟨Ve,hVe,hφe,_,A,hA,he⟩ := D.complex.exists_local_normalizedWeightedTerminal_bound w φ
  obtain ⟨Vt,hVt,hreal,hTa,hTd⟩ := exists_sourceSignedTerminalSequence_compact_derivative_domain
  have hφt : normalizedWeightedSource w φ.val ∈ Vt :=
    hreal (normalizedWeightedSource_realType w φ.val φ.property)
  let U := Ve ∩ normalizedWeightedSource w ⁻¹' Vt
  have hU : IsOpen U := hVe.inter (hVt.preimage (continuous_normalizedWeightedSource w))
  let S := WeightedCoeff.signedPositiveSplice (sourceFrequencyWeight w) 2
  refine ⟨U,‖S‖*A,hU,⟨hφe,hφt⟩,?_,?_⟩
  · intro ψ hψ
    exact (hTa _ hψ.2).comp ((normalizedWeightedSourceCLM w).analyticAt ψ)
  · intro ψ hψ
    let a := Coeff.ofFunctionOrZero 2 (fun n => (w (2*n):ℂ)*
      sourceGapWeightedEtaTerminalCoordinate (by norm_num) (by norm_num) n 1
        (normalizedWeightedSource w ψ))
    let b := Coeff.ofFunctionOrZero 2 (fun n => (w (2*n):ℂ)*
      sourceGapWeightedEtaTerminalCoordinate (by norm_num) (by norm_num) n (-1)
        (normalizedWeightedSource w ψ))
    have ha := he ψ hψ.1 1 (Or.inl rfl)
    have hb := he ψ hψ.1 (-1) (Or.inr rfl)
    let A₁ := (weightIsometry (sourceFrequencyWeight w) 2).symm a
    let A₂ := (weightIsometry (sourceFrequencyWeight w) 2).symm b
    have hA₁ : ‖A₁‖ ≤ A := by rw [LinearIsometryEquiv.norm_map]; exact ha.2
    have hA₂ : ‖A₂‖ ≤ A := by rw [LinearIsometryEquiv.norm_map]; exact hb.2
    have hcoord₁ (k : ℤ) : A₁.val k = sourceGapWeightedEtaTerminalCoordinate
        (by norm_num) (by norm_num) k 1 (normalizedWeightedSource w ψ) := by
      change a k/(w (2*k):ℂ) = _
      rw [Coeff.ofFunctionOrZero_apply_of_mem 2 _ ha.1]
      exact mul_div_cancel_left₀ _ (w.toWeight.complex_ne_zero _)
    have hcoord₂ (k : ℤ) : A₂.val k = sourceGapWeightedEtaTerminalCoordinate
        (by norm_num) (by norm_num) k (-1) (normalizedWeightedSource w ψ) := by
      change b k/(w (2*k):ℂ) = _
      rw [Coeff.ofFunctionOrZero_apply_of_mem 2 _ hb.1]
      exact mul_div_cancel_left₀ _ (w.toWeight.complex_ne_zero _)
    refine ⟨S (A₁,A₂),?_,?_⟩
    · intro k
      rcases lt_trichotomy 0 k with hk | hk | hk
      · rw [WeightedCoeff.signedPositiveSplice_positive _ _ _ _ k hk,hcoord₁]
        exact ((hTd _ hψ.2).1 k hk).symm
      · subst k
        rw [WeightedCoeff.signedPositiveSplice_zero,sourceSignedTerminalSequence_zero]
      · rw [WeightedCoeff.signedPositiveSplice_negative,hcoord₂]
        · exact ((hTd _ hψ.2).2.1 k hk).symm
        · intro j
          change w (2*(-j)) = w (2*j)
          rw [mul_neg,SpectralWeight.apply_neg]
        · exact hk
    · exact (S.le_opNorm _).trans (mul_le_mul_of_nonneg_left
        (norm_prod_le_iff.mpr ⟨hA₁,hA₂⟩) (norm_nonneg S))

theorem exists_local_normalizedWeightedSignedTerminal_analytic
    (w : SpectralWeight) (φ : realTypeSourceLocus 2) :
    ∃ U : Set (CoeffPair 2), IsOpen U ∧ φ.val ∈ U ∧
      AnalyticOnNhd ℂ (normalizedWeightedSignedTerminal w) U ∧
      ∀ ψ ∈ U, ∀ k,
        (normalizedWeightedSignedTerminal w ψ).val k =
          sourceSignedTerminalSequence (normalizedWeightedSource w ψ) k := by
  obtain ⟨U,M,hU,hφ,hf,hb⟩ := exists_local_weighted_signedTerminal_bound w φ
  have hc (k : ℤ) : AnalyticOnNhd ℂ
      (fun ψ => sourceSignedTerminalSequence (normalizedWeightedSource w ψ) k) U := by
    intro ψ hψ
    exact ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 k).analyticAt _).comp (hf ψ hψ)
  obtain ⟨ha,hd⟩ := analytic_realization_of_bound (sourceFrequencyWeight w)
    (fun ψ k => sourceSignedTerminalSequence (normalizedWeightedSource w ψ) k) hU hc M hb
  exact ⟨U,hU,hφ,ha,fun ψ hψ => (hd ψ hψ).2⟩

end NLS.ZakharovShabat
