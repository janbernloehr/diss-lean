import NLS.MKdV.MiuraActionDescent
import NLS.ZakharovShabat.SourceDiagonalPrimitiveSquare
import NLS.ZakharovShabat.SourceAbelianSquareIsospectral
import NLS.MKdV.MiuraZeroEnergy

/-! # The mean squared is an analytic NLS action function

The central filled primitive square at zero energy equals the literal
Fourier mean squared. Its ambient source analyticity survives zero mean,
and real isospectral invariance gives an analytic action factor there.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV
local instance : (2 : ℝ≥0∞).HolderTriple 2 1 := (ENNReal.holderTriple_iff _ _ _).mpr (by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_add])

/-- The continued central square has no sign ambiguity, including at
the collapsed central gap. The mean is the original zero Fourier mode. -/
theorem miuraPrimitiveSquare_eq_mean_sq (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    sourceAbelianSquare (by simp) (by norm_num) (realDiagonalH1Source a ha).val
      (realDiagonalH1Source a ha).property 0 0 = (a.val 0)^2 := by
  let φ := realDiagonalH1Source a ha
  have hz := sourcePeriodicSegment_re_mem_Icc (by simp) (by norm_num) φ.val 0 0
    (zero_mem_central_segment_of_diagonal (by simp) (by norm_num) φ rfl)
  have hs := sourceAbelianSquare_eq_arcosh_sq (by simp) (by norm_num) φ.val φ.property 0 0 hz
  have hmean : ((a.val 0).re : ℂ) = a.val 0 := by
    apply Complex.ext <;> simp only [ofReal_re,ofReal_im,miura_mean_real a ha]
  have hprofile : sourceRealGapArcoshProfile (by simp) φ.val 0 0 = |(a.val 0).re| := by
    change Real.arcosh ((canonicalDiscriminant (by simp)
      (periodOnePotential (sobolevSourceInclusion (a,a))) 0).re/2) = _
    rw [canonicalDiscriminant_miura_zero,← hmean,← ofReal_cosh]
    simp only [mul_re,show (2 : ℂ).re = 2 from rfl,ofReal_re,
      show (2 : ℂ).im = 0 from rfl,ofReal_im,mul_zero,sub_zero]
    rw [mul_div_cancel_left₀ _ (by norm_num : (2:ℝ) ≠ 0),← Real.cosh_abs,
      Real.arcosh_cosh (abs_nonneg _)]
  calc
    _ = (sourceRealGapArcoshProfile (by simp) φ.val 0 0 : ℂ)^2 := by
      simpa only [ofReal_zero] using! hs
    _ = (a.val 0)^2 := by rw [hprofile,← ofReal_pow,sq_abs,ofReal_pow,hmean]

/-- Corrected converse mean assertion: a holomorphic ℓ¹ action factor
recovers `[u]^2` on every original real H1 input, also at `[u]=0`.
No signed-mean recovery is asserted. -/
theorem exists_miuraMeanSquare_action_extension :
    ∃ I : CoeffPair 2 → Coeff 1, ∃ U : Set (CoeffPair 2),
      IsOpen U ∧ realTypeSourceLocus 2 ⊆ U ∧ AnalyticOnNhd ℂ I U ∧
      (∀ ψ ∈ U, ∀ m : ℤ, I ψ m = sourceComplexAction (by simp) (by norm_num) m ψ) ∧
      (∀ (a : ScalarDomain 2) (_ha : ∀ j, a.val j = conj (a.val (-j))),
        ∀ m : ℤ, I (sobolevSourceInclusion (a,a)) m = miuraNLSAction a m) ∧
      ∃ V : Set (Coeff 1), ∃ G : Coeff 1 → ℂ,
        IsOpen V ∧ (∀ ψ ∈ realDiagonalSourceLocus 2, I ψ ∈ V) ∧
          AnalyticOnNhd ℂ G V ∧ AnalyticOnNhd ℝ G V ∧
          ∀ (a : ScalarDomain 2) (_ha : ∀ j, a.val j = conj (a.val (-j))),
            G (I (sobolevSourceInclusion (a,a))) = (a.val 0)^2 := by
  obtain ⟨W₀,B,X,t,D⟩ := exists_sourceBirkhoffMap_complex_analytic
    (p := 2) (by simp) (by norm_num)
  let I := sourceActionSequence (q := 1) (by simp) (by norm_num) t
  obtain ⟨O,F,hO,hdiag,hF,hreal⟩ := exists_sourceDiagonalPrimitiveSquare
    (p := 2) (by simp) (by norm_num)
  have hinv (a b : realTypeSourceSubmodule 2) (_ha : a.val ∈ O) (_hb : b.val ∈ O)
      (hab : b ∈ sourceRealActionLevelSet (by simp) (by norm_num) a) : F b.val = F a.val := by
    rw [hreal b,hreal a]
    apply sourceAbelianSquare_eq_of_isospectral (by simp) (by norm_num) a b _ 0 0
    rwa [sourceIsospectralSet_eq_actionLevelSet_all_exponents (by simp) (by norm_num) a]
  obtain ⟨V,G,hV,hcenters,_,_,hG,hrec,_⟩ := D.exists_scalar_action_extension_on (q := 1) F hO hF hinv
  refine ⟨I,X,D.source_open,D.real_subset,D.actionSequence_analytic,D.actionSequence_apply,?_,
    V,G,hV,?_,hG,hG.restrictScalars,?_⟩
  · intro a ha m
    let ψ := realDiagonalH1Source a ha
    change I ψ.val m = _
    rw [D.actionSequence_apply ψ.val (D.real_subset ψ.property),
      sourceComplexAction_eq_sourceRealAction _ _ m ψ.val ψ.property]
    exact (sourceIndexedAction_eq_sourceRealAction _ _ m ψ.val ψ.property).symm
  · intro ψ hψ
    exact hcenters ⟨ψ,hψ.1⟩ (hdiag hψ)
  · intro a ha
    exact (hrec (realDiagonalH1Source a ha) (hdiag ⟨(realDiagonalH1Source a ha).property,rfl⟩)).trans
      ((hreal (realDiagonalH1Source a ha)).trans (miuraPrimitiveSquare_eq_mean_sq a ha))

end NLS.MKdV
