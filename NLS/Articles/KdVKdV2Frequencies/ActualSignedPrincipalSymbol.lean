import NLS.Articles.KdVKdV2Frequencies.ActualSignedAbelianFourier
import NLS.SequenceSpaces.PeriodOneFreeFourierEquiv
import NLS.SequenceSpaces.SignedMultiplierPrincipal

/-! # Exact actual signed principal symbol and its reciprocal -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV

/-- The literal full positive symbol, including physical signs, actual
eta normalization and the exact complex factor 2*i. -/
def actualPositivePrincipalSymbol (D : RoughAbelianFourierData) (e : ℤ → Bool)
    (q : PeriodOneHminusOne) : Coeff ⊤ :=
  Coeff.signedProductSymbol e (2*I) (D.symbol q)
    (sourceEtaNormalizationSymbol (by norm_num) (by norm_num) D.chart.family.roots 1 (D.chart.dirichletSource q))

/-- The original positive principal is EXACTLY this literal multiplier
followed by the SAME native free Fourier/Miura equivalence. -/
theorem actualPositiveFourierPrincipal_eq_multiplier
    (D : RoughAbelianFourierData) (e : ℤ → Bool) (t : ℝ) (ht : 0≤t)
    (q : WeightedCoeff (Weight.sobolev (t-1)) 2) :
    actualPositiveFourierPrincipal D e t ht q=
      (Coeff.holderProduct (q := 2) (actualPositivePrincipalSymbol D e (periodOneSobolevImageInclusion t ht q))).comp
        (periodOneNativeFreeFourierEquiv t ht).toContinuousLinearMap := by
  ext h n
  change (Coeff.signChange e
    ((Coeff.holderProduct (q := 2) (D.symbol (periodOneSobolevImageInclusion t ht q)))
      ((Coeff.holderProduct (q := 2)
        (sourceEtaNormalizationSymbol (by norm_num) (by norm_num) D.chart.family.roots 1
          (D.chart.dirichletSource (periodOneSobolevImageInclusion t ht q))))
        ((2*I) • (periodOneNativeFreeFourierEquiv t ht h))))) n=_
  rw [Coeff.signChange_apply]
  change (if e n then -(D.symbol (periodOneSobolevImageInclusion t ht q) n*
    (sourceEtaNormalizationSymbol (by norm_num) (by norm_num) D.chart.family.roots 1
      (D.chart.dirichletSource (periodOneSobolevImageInclusion t ht q)) n*(2*I*periodOneNativeFreeFourierEquiv t ht h n))) else
    D.symbol (periodOneSobolevImageInclusion t ht q) n*
    (sourceEtaNormalizationSymbol (by norm_num) (by norm_num) D.chart.family.roots 1
      (D.chart.dirichletSource (periodOneSobolevImageInclusion t ht q)) n*(2*I*periodOneNativeFreeFourierEquiv t ht h n)))=
    actualPositivePrincipalSymbol D e (periodOneSobolevImageInclusion t ht q) n*periodOneNativeFreeFourierEquiv t ht h n
  rw [actualPositivePrincipalSymbol,Coeff.signedProductSymbol_apply]
  cases e n <;> simp only [Bool.false_eq_true,↓reduceIte] <;> ring

/-- At EVERY eligible real rough base the actual positive principal has
an ACTUAL bounded positive reciprocal. The original root and phase are
retained; the product identity precedes every positive signed index. -/
theorem exists_actualPositivePrincipalSymbol_reciprocal
    (D : RoughAbelianFourierData) (e : ℤ → Bool) (q : PeriodOneHminusOne)
    (hq : q∈ball (0 : PeriodOneHminusOne) D.radius) (hqr : IsRealPeriodOneHminusOne q) :
    ∃ b : Coeff ⊤,
      (∀ n : ℤ, n≤0 → actualPositivePrincipalSymbol D e q n=0) ∧
      (∀ n : ℤ, n≤0 → b n=0) ∧
      ∀ n : ℤ, 0<n → actualPositivePrincipalSymbol D e q n*b n=1 := by
  have hreal := D.real_lift q (D.source_domain hq).1.1 hqr
  let φ : realTypeSourceSubmodule 2 := ⟨D.chart.dirichletSource q,
    isRealType_sourcePhase _ (isRealType_hillMiuraDiagonal
      ⟨D.chart.miura.lift q,(periodOneL2Conjugation_fixed_iff _).mp hreal⟩)⟩
  obtain ⟨_B,DC,_hact⟩ := D.roots.exists_original_birkhoff_map
  obtain ⟨U,_hU,hφU,_hUW,_C,_hC,hmu⟩ := DC.exists_local_sourceEtaNormalization_symbols φ
  have hm := (hmu 1 (Or.inl rfl)).2.2 φ.val hφU
  let b := Coeff.signedProductSymbol e (2*I)⁻¹ (D.reciprocal q)
    (sourceEtaNormalizationInverseSymbol (by norm_num) (by norm_num) D.chart.family.roots 1 (D.chart.dirichletSource q))
  refine ⟨b,?_,?_,?_⟩
  · intro n hn
    rw [actualPositivePrincipalSymbol,Coeff.signedProductSymbol_apply,((D.symbol_data q hq).2.2.1 n hn).1]
    simp only [zero_mul,mul_zero,neg_zero,ite_self]
  · intro n hn
    dsimp only [b]
    rw [Coeff.signedProductSymbol_apply,((D.symbol_data q hq).2.2.1 n hn).2]
    simp only [zero_mul,mul_zero,neg_zero,ite_self]
  · intro n hn
    let k := Coeff.positivePoleIndex n hn
    have hk : (k : ℤ)=n := by exact_mod_cast Coeff.positivePoleIndex_real n hn
    have hs : D.symbol q n*D.reciprocal q n=1 := by
      simpa only [hk] using ((D.symbol_data q hq).2.2.2 k).2.2.2
    exact Coeff.signedProductSymbol_reciprocal e (2*I) (by simp) _ _ _ _ n hs (hm.2.2 n).2.2.2

/-- At physically real bases, both actual conjugate source terms use
ONE full signed multiplier followed by the SAME actual free equivalence. -/
theorem actualSignedFourierPrincipal_eq_multiplier
    (D : RoughAbelianFourierData) (e : ℤ → Bool) (t : ℝ) (ht : 0≤t)
    (q : WeightedCoeff (Weight.sobolev (t-1)) 2)
    (hqr : IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion t ht q)) :
    actualSignedFourierPrincipal D e t ht q=
      (WeightedCoeff.weightIsometry (Weight.sobolev (t-1/2)) 2).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((Coeff.holderProduct (q := 2) (Coeff.completedPositiveSymbol
          (actualPositivePrincipalSymbol D e (periodOneSobolevImageInclusion t ht q)))).comp
            (periodOneNativeFreeFourierEquiv t ht).toContinuousLinearMap) := by
  have hJq := sobolev_conjugateReflection_fixed_of_real_inclusion t ht q hqr
  rw [actualSignedFourierPrincipal,hJq,actualPositiveFourierPrincipal_eq_multiplier]
  exact WeightedCoeff.nativeSignedPrincipal_multiplier _ _ _ _
    (periodOneNativeFreeFourierEquiv_conjugation t ht) _

end NLS.Articles.KdVKdV2Frequencies
