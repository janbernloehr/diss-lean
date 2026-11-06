import NLS.ZakharovShabat.SourceWeightedEtaExponentFactorization
import NLS.SequenceSpaces.BoundedAnalyticSymbolExponent

/-! # The ACTUAL weighted eta derivative has its normalized Fourier principal

The original normalization/phase is retained as a bounded invertible
multiplier. The verified actual weighted Birkhoff derivative has compact
Fourier remainder; symbol differentiation contributes another compact
term. Every real normalized source and every spectral weight is covered.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1≤p)]

private theorem compact_fderiv_postcomp_sub
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (L : F →L[ℂ] G) (f : E → F) (q : E) (hf : DifferentiableAt ℂ f q)
    (Q : E →L[ℂ] F) (hc : IsCompactOperator (fderiv ℂ f q-Q)) :
    IsCompactOperator (fderiv ℂ (fun x => L (f x)) q-L.comp Q) := by
  have hd : fderiv ℂ (fun x => L (f x)) q=L.comp (fderiv ℂ f q) :=
    (L.hasFDerivAt.comp q hf.hasFDerivAt).fderiv
  rw [hd]
  have he : L.comp (fderiv ℂ f q)-L.comp Q=L.comp (fderiv ℂ f q-Q) := by
    apply ContinuousLinearMap.ext
    intro h
    exact (L.map_sub _ _).symm
  rw [he]
  exact hc.clm_comp L

namespace SourceBirkhoffMapComplexData
variable {hp : p≠⊤} {hp1 : 1<p}
variable {W₀ B W : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- At EVERY normalized real source and EVERY spectral weight, the
ACTUAL native eta derivative is its full normalization multiplier times
the exact signed Fourier coordinate, plus a COMPACT operator. -/
theorem isCompactOperator_fderiv_normalizedWeightedEta_exponent_sub_principal
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (w : SpectralWeight) (φ : realTypeSourceLocus p) (sign : ℂ) (hsign : sign=1 ∨ sign=-1) :
    IsCompactOperator (fderiv ℂ (normalizedWeightedEtaSequence hp hp1 s w sign) φ.val-
      (Coeff.holderProduct (q := p) (normalizedWeightedEtaExponentSymbol hp hp1 s w sign φ.val)).comp
        ((etaRectangularExponentCLM (p := p) sign).comp (sourceBirkhoffFourier (p := p)))) := by
  obtain ⟨U,hU,hφU,hBa,_C,_hC,hfactors⟩ := D.exists_local_normalizedWeightedEta_exponent_factorization w φ
  obtain ⟨_hηa,hσa,_hνa,hdata⟩ := hfactors sign hsign
  let F := fun ψ => etaRectangularExponentCLM (p := p) sign (normalizedWeightedBirkhoffMap hp hp1 s w ψ)
  have hF : DifferentiableAt ℂ F φ.val :=
    (etaRectangularExponentCLM (p := p) sign).differentiableAt.comp φ.val (hBa φ.val hφU).differentiableAt
  have hFc : IsCompactOperator (fderiv ℂ F φ.val-(etaRectangularExponentCLM (p := p) sign).comp (sourceBirkhoffFourier (p := p))) :=
    compact_fderiv_postcomp_sub (etaRectangularExponentCLM (p := p) sign) _ φ.val (hBa φ.val hφU).differentiableAt
      (sourceBirkhoffFourier (p := p)) (D.isCompactOperator_fderiv_normalizedWeightedBirkhoffMap_sub_fourier w φ)
  have he : normalizedWeightedEtaSequence hp hp1 s w sign =ᶠ[𝓝 φ.val]
      (fun ψ => Coeff.holderProduct (q := p) (normalizedWeightedEtaExponentSymbol hp hp1 s w sign ψ) (F ψ)) := by
    filter_upwards [hU.mem_nhds hφU] with ψ hψ
    exact (hdata ψ hψ).1
  rw [he.fderiv_eq]
  exact Coeff.isCompactOperator_fderiv_symbol_packet_sub_principal_exponent hp _ F φ.val
    (hσa φ.val hφU).differentiableAt hF _ hFc

/-- The multiplier in the ACTUAL eta principal is a bounded equivalence,
with its ACTUAL reciprocal symbol. No phase-tail replacement is needed. -/
theorem exists_normalizedWeightedEta_exponent_principal_equiv
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (w : SpectralWeight) (φ : realTypeSourceLocus p) (sign : ℂ) (hsign : sign=1 ∨ sign=-1) :
    ∃ S : Coeff p ≃L[ℂ] Coeff p,
      S.toContinuousLinearMap=Coeff.holderProduct (q := p) (normalizedWeightedEtaExponentSymbol hp hp1 s w sign φ.val) ∧
      IsCompactOperator (fderiv ℂ (normalizedWeightedEtaSequence hp hp1 s w sign) φ.val-
        S.toContinuousLinearMap.comp ((etaRectangularExponentCLM (p := p) sign).comp (sourceBirkhoffFourier (p := p)))) := by
  obtain ⟨U,_hU,hφU,_hBa,_C,_hC,hfactors⟩ := D.exists_local_normalizedWeightedEta_exponent_factorization w φ
  have hu := (hfactors sign hsign).2.2.2 φ.val hφU
  let S := Coeff.multiplierEquivOfInverse (p := p)
    (normalizedWeightedEtaExponentSymbol hp hp1 s w sign φ.val) (normalizedWeightedEtaExponentInverseSymbol hp hp1 s w sign φ.val)
    (fun n => hu.2.2.2 n)
  have he : S.toContinuousLinearMap=Coeff.holderProduct (q := p) (normalizedWeightedEtaExponentSymbol hp hp1 s w sign φ.val) := by
    ext a n
    rfl
  refine ⟨S,he,?_⟩
  rw [he]
  exact D.isCompactOperator_fderiv_normalizedWeightedEta_exponent_sub_principal w φ sign hsign

end SourceBirkhoffMapComplexData

/-- The positive complex Fourier coordinate is EXACTLY minus twice the
second source component, including the reflected rectangular convention. -/
theorem etaRectangularExponentCLM_one_fourier (h : CoeffPair p) (n : ℤ) :
    etaRectangularExponentCLM (p := p) 1 (sourceBirkhoffFourier h) n= -2*h.snd n := by
  have hs8 : (Real.sqrt 8 : ℂ)=2*(Real.sqrt 2 : ℂ) := by
    have H : Real.sqrt (8 : ℝ)=2*Real.sqrt 2 := by
      rw [show (8 : ℝ)=4*2 by norm_num,Real.sqrt_mul (by norm_num),show Real.sqrt (4 : ℝ)=2 by rw [show (4 : ℝ)=(2 : ℝ)^2 by norm_num,Real.sqrt_sq (by norm_num)]]
    exact_mod_cast H
  have hs2 : (Real.sqrt 2 : ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne'
  rw [etaRectangularExponentCLM_apply,sourceBirkhoffFourier_fst,sourceBirkhoffFourier_snd,hs8]
  field_simp [hs2,Complex.I_ne_zero]
  ring

end NLS.ZakharovShabat
