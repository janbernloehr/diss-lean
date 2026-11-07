import NLS.KdV.HillMiuraFourierLebesgueNormalizedSource
import NLS.ZakharovShabat.SourceWeightedEtaExponentCompactDerivative

/-! # Native weighted Hill eta Fourier principals at every finite exponent

The actual normalized p-family and its reciprocal symbol are retained.
The exact free principal is 2*i times the ORIGINAL native weight isometry.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV
variable {p : ℝ≥0∞} [Fact (1≤p)]

/-- The exact positive free eta derivative on the actual Hill source. -/
theorem etaRectangular_fourier_hillMiuraFourierLebesgue (t : ℝ) :
    (etaRectangularExponentCLM 1).comp ((sourceBirkhoffFourier (p := p)).comp
      (hillMiuraNormalizedFourierLebesgueDirichletSource t))=
    (2*I) • (WeightedCoeff.weightIsometry (Weight.sobolev t) p).toContinuousLinearEquiv.toContinuousLinearMap := by
  ext a n
  change etaRectangularExponentCLM 1 (sourceBirkhoffFourier (hillMiuraNormalizedFourierLebesgueDirichletSource t a)) n=_
  rw [etaRectangularExponentCLM_one_fourier,hillMiuraNormalizedFourierLebesgueDirichletSource_snd]
  change -2*(-I*((Weight.sobolev t n : ℂ)*a.val n))=(2*I)*((Weight.sobolev t n : ℂ)*a.val n)
  ring

def hillMiuraFourierLebesgueEtaSequence (hp : p≠⊤) (hp1 : 1<p)
    (sp : (n : ℤ) → CoeffPair p → DeletedCoeff p n) (t : ℝ) (ht : 0≤t) (sign : ℂ)
    (a : WeightedCoeff (Weight.sobolev t) p) : Coeff p :=
  normalizedWeightedEtaSequence hp hp1 sp (sourceSobolevSpectralWeight t ht) sign
    (hillMiuraNormalizedFourierLebesgueDirichletSource t a)

theorem isCompactOperator_fderiv_hillMiuraFourierLebesgueEta_sub_principal
    {hp : p≠⊤} {hp1 : 1<p} {W₀ B W : Set (CoeffPair p)}
    {sp : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W sp)
    (t : ℝ) (ht : 0≤t) (a : WeightedCoeff (Weight.sobolev t) p)
    (hr : ∀ n : ℤ, a.val (-n)=(starRingEnd ℂ) (a.val n)) :
    IsCompactOperator (fderiv ℂ (hillMiuraFourierLebesgueEtaSequence hp hp1 sp t ht 1) a-
      (Coeff.holderProduct (q := p)
        (normalizedWeightedEtaExponentSymbol hp hp1 sp (sourceSobolevSpectralWeight t ht) 1
          (hillMiuraNormalizedFourierLebesgueDirichletSource t a))).comp
            ((2*I) • (WeightedCoeff.weightIsometry (Weight.sobolev t) p).toContinuousLinearEquiv.toContinuousLinearMap)) := by
  let J := hillMiuraNormalizedFourierLebesgueDirichletSource (p := p) t
  let w := sourceSobolevSpectralWeight t ht
  let φ : realTypeSourceLocus p := ⟨J a,isRealType_hillMiuraNormalizedFourierLebesgueDirichletSource t a hr⟩
  obtain ⟨U,_hU,hφU,_hBa,_C,_hC,hf⟩ := D.exists_local_normalizedWeightedEta_exponent_factorization w φ
  have hη := ((hf 1 (Or.inl rfl)).1 φ.val hφU).differentiableAt
  have hd := (hη.hasFDerivAt.comp a J.hasFDerivAt).fderiv
  have hc := (D.isCompactOperator_fderiv_normalizedWeightedEta_exponent_sub_principal w φ 1 (Or.inl rfl)).comp_clm J
  have he : (fderiv ℂ (normalizedWeightedEtaSequence hp hp1 sp w 1) φ.val-
      (Coeff.holderProduct (q := p) (normalizedWeightedEtaExponentSymbol hp hp1 sp w 1 φ.val)).comp
        ((etaRectangularExponentCLM (p := p) 1).comp (sourceBirkhoffFourier (p := p)))).comp J=
    fderiv ℂ (hillMiuraFourierLebesgueEtaSequence hp hp1 sp t ht 1) a-
      (Coeff.holderProduct (q := p) (normalizedWeightedEtaExponentSymbol hp hp1 sp w 1 φ.val)).comp
        (((etaRectangularExponentCLM (p := p) 1).comp (sourceBirkhoffFourier (p := p))).comp J) := by
    rw [show fderiv ℂ (hillMiuraFourierLebesgueEtaSequence hp hp1 sp t ht 1) a=
      (fderiv ℂ (normalizedWeightedEtaSequence hp hp1 sp w 1) φ.val).comp J from hd]
    rfl
  change IsCompactOperator ((fderiv ℂ (normalizedWeightedEtaSequence hp hp1 sp w 1) φ.val-
      (Coeff.holderProduct (q := p) (normalizedWeightedEtaExponentSymbol hp hp1 sp w 1 φ.val)).comp
        ((etaRectangularExponentCLM (p := p) 1).comp (sourceBirkhoffFourier (p := p)))).comp J) at hc
  rw [he] at hc
  have hfree : ((etaRectangularExponentCLM (p := p) 1).comp (sourceBirkhoffFourier (p := p))).comp J=
      (2*I) • (WeightedCoeff.weightIsometry (Weight.sobolev t) p).toContinuousLinearEquiv.toContinuousLinearMap :=
    etaRectangular_fourier_hillMiuraFourierLebesgue t
  rw [hfree] at hc
  exact hc

end NLS.KdV
