import NLS.KdV.HillMiuraSobolevEtaSequence
import NLS.ZakharovShabat.SourceWeightedEtaCompactDerivative

/-! # The actual native Hill eta derivative and its Fourier principal

The actual ordinary Dirichlet source is retained, including its phase
and the spectral weight at twice the physical index. The exact free
principal is twice i times the native Sobolev weight isometry.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV

/-- The exact positive free eta derivative on the actual Hill source. -/
theorem etaRectangular_fourier_hillMiuraSobolev (t : ℝ) :
    (etaRectangularCLM 1).comp ((sourceBirkhoffFourier (p := 2)).comp
      (hillMiuraNormalizedSobolevDirichletSource t))=
    (2*I) • (WeightedCoeff.weightIsometry (Weight.sobolev t) 2).toContinuousLinearEquiv.toContinuousLinearMap := by
  ext a n
  change etaRectangularCLM 1 (sourceBirkhoffFourier (hillMiuraNormalizedSobolevDirichletSource t a)) n=_
  rw [etaRectangularCLM_one_fourier,hillMiuraNormalizedSobolevDirichletSource_snd]
  change -2*(-I*((Weight.sobolev t n : ℂ)*a.val n))=(2*I)*((Weight.sobolev t n : ℂ)*a.val n)
  ring

/-- The actual positive eta derivative is its literal invertible
normalization times the exact weighted Fourier principal, plus compact,
at EVERY physically real native base and EVERY nonnegative real order. -/
theorem isCompactOperator_fderiv_hillMiuraSobolevEta_sub_principal
    {W0 W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) W0 W s)
    (t : ℝ) (ht : 0≤t) (a : WeightedCoeff (Weight.sobolev t) 2)
    (hr : periodOneL2Conjugation (WeightedCoeff.sobolevToL2 ht a)=WeightedCoeff.sobolevToL2 ht a) :
    IsCompactOperator (fderiv ℂ (hillMiuraSobolevEtaSequence s t ht 1) a-
      (Coeff.holderProduct (q := 2)
        (sourceEtaNormalizationSymbol (by norm_num) (by norm_num) s 1
          (sourcePhase (hillMiuraDiagonal (WeightedCoeff.sobolevToL2 ht a))))).comp
      ((2*I) • (WeightedCoeff.weightIsometry (Weight.sobolev t) 2).toContinuousLinearEquiv.toContinuousLinearMap)) := by
  obtain ⟨B,D,_hactions⟩ := H.exists_original_birkhoff_map
  let J := hillMiuraNormalizedSobolevDirichletSource t
  let w := sourceSobolevSpectralWeight t ht
  let φ : realTypeSourceLocus 2 := ⟨J a,isRealType_hillMiuraNormalizedSobolevDirichletSource t ht a hr⟩
  obtain ⟨U,_hU,hφU,_hBa,_C,_hC,hf⟩ := D.exists_local_normalizedWeightedEta_factorization w φ
  have hη := ((hf 1 (Or.inl rfl)).1 φ.val hφU).differentiableAt
  have hd := (hη.hasFDerivAt.comp a J.hasFDerivAt).fderiv
  have hc := (D.isCompactOperator_fderiv_normalizedWeightedEta_sub_principal w φ 1 (Or.inl rfl)).comp_clm J
  have he : (fderiv ℂ (normalizedWeightedEtaSequence (by norm_num) (by norm_num) s w 1) φ.val-
      (Coeff.holderProduct (q := 2) (normalizedWeightedEtaSymbol s w 1 φ.val)).comp
        ((etaRectangularCLM 1).comp (sourceBirkhoffFourier (p := 2)))).comp J=
    fderiv ℂ (hillMiuraSobolevEtaSequence s t ht 1) a-
      (Coeff.holderProduct (q := 2) (normalizedWeightedEtaSymbol s w 1 φ.val)).comp
        (((etaRectangularCLM 1).comp (sourceBirkhoffFourier (p := 2))).comp J) := by
    rw [show fderiv ℂ (hillMiuraSobolevEtaSequence s t ht 1) a=
      (fderiv ℂ (normalizedWeightedEtaSequence (by norm_num) (by norm_num) s w 1) φ.val).comp J from hd]
    rfl
  change IsCompactOperator ((fderiv ℂ (normalizedWeightedEtaSequence (by norm_num) (by norm_num) s w 1) φ.val-
      (Coeff.holderProduct (q := 2) (normalizedWeightedEtaSymbol s w 1 φ.val)).comp
        ((etaRectangularCLM 1).comp (sourceBirkhoffFourier (p := 2)))).comp J) at hc
  rw [he] at hc
  have hfree : ((etaRectangularCLM 1).comp (sourceBirkhoffFourier (p := 2))).comp J=
      (2*I) • (WeightedCoeff.weightIsometry (Weight.sobolev t) 2).toContinuousLinearEquiv.toContinuousLinearMap :=
    etaRectangular_fourier_hillMiuraSobolev t
  rw [hfree] at hc
  simpa only [normalizedWeightedEtaSymbol,φ,w,J,normalizedWeightedSource_hillMiuraSobolev] using hc

end NLS.KdV
