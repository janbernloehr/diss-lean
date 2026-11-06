import NLS.ZakharovShabat.SourceEtaNormalizationSymbol
import NLS.ZakharovShabat.NormalizedWeightedBirkhoffDifferential

/-! # Exact native factorization of ACTUAL weighted eta at every finite exponent

Both actual eta signs factor through the SAME normalized weighted
Birkhoff map and literal inverse-root/phase symbol. Every coefficient
is exact on ONE open complex neighborhood of each normalized real base.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1≤p)]

/-- The original signed complex coordinate, with its exact rectangular normalization. -/
def etaRectangularExponentCLM (sign : ℂ) : (Coeff p × Coeff p) →L[ℂ] Coeff p :=
  ((Real.sqrt 8 : ℂ)/2) • (ContinuousLinearMap.fst ℂ (Coeff p) (Coeff p)+
    (sign*I) • ContinuousLinearMap.snd ℂ (Coeff p) (Coeff p))

@[simp] theorem etaRectangularExponentCLM_apply (sign : ℂ) (a : Coeff p × Coeff p) (n : ℤ) :
    etaRectangularExponentCLM sign a n=((Real.sqrt 8 : ℂ)/2)*(a.1 n+sign*I*a.2 n) := by
  change (((Real.sqrt 8 : ℂ)/2) • (a.1+(sign*I) • a.2)) n=_
  simp only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,lp.coeFn_add,Pi.add_apply]

/-- The actual normalization symbol in normalized spectral-weight coordinates. -/
def normalizedWeightedEtaExponentSymbol (hp : p≠⊤) (hp1 : 1<p)
    (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n) (w : SpectralWeight) (sign : ℂ)
    (ψ : CoeffPair p) : Coeff ⊤ :=
  sourceEtaNormalizationSymbol hp hp1 s sign (normalizedWeightedSource w ψ)

def normalizedWeightedEtaExponentInverseSymbol (hp : p≠⊤) (hp1 : 1<p)
    (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n) (w : SpectralWeight) (sign : ℂ)
    (ψ : CoeffPair p) : Coeff ⊤ :=
  sourceEtaNormalizationInverseSymbol hp hp1 s sign (normalizedWeightedSource w ψ)

namespace SourceBirkhoffMapComplexData
variable {hp : p≠⊤} {hp1 : 1<p}
variable {W₀ B W : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- At EVERY normalized real base and EVERY spectral weight, the SAME
actual eta has its exact native analytic inverse-normalization factorization.
ONE domain and bound precede BOTH signs and EVERY signed index. -/
theorem exists_local_normalizedWeightedEta_exponent_factorization
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (w : SpectralWeight) (φ : realTypeSourceLocus p) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ.val∈U ∧
      AnalyticOnNhd ℂ (normalizedWeightedBirkhoffMap hp hp1 s w) U ∧
      ∃ C : ℝ, 0<C ∧ ∀ sign : ℂ, sign=1 ∨ sign=-1 →
        AnalyticOnNhd ℂ (normalizedWeightedEtaSequence hp hp1 s w sign) U ∧
        AnalyticOnNhd ℂ (normalizedWeightedEtaExponentSymbol hp hp1 s w sign) U ∧
        AnalyticOnNhd ℂ (normalizedWeightedEtaExponentInverseSymbol hp hp1 s w sign) U ∧ ∀ ψ∈U,
          normalizedWeightedEtaSequence hp hp1 s w sign ψ=
            Coeff.holderProduct (q := p) (normalizedWeightedEtaExponentSymbol hp hp1 s w sign ψ)
              (etaRectangularExponentCLM sign (normalizedWeightedBirkhoffMap hp hp1 s w ψ)) ∧
          ‖normalizedWeightedEtaExponentSymbol hp hp1 s w sign ψ‖≤C ∧
          ‖normalizedWeightedEtaExponentInverseSymbol hp hp1 s w sign ψ‖≤C ∧ ∀ n,
            normalizedWeightedEtaExponentSymbol hp hp1 s w sign ψ n*normalizedWeightedEtaExponentInverseSymbol hp hp1 s w sign ψ n=1 := by
  let φu : realTypeSourceSubmodule p :=
    ⟨normalizedWeightedSource w φ.val,normalizedWeightedSource_realType w φ.val φ.property⟩
  obtain ⟨Ur,hUr,hφr,_hUrW,C,hC,hsymbol⟩ := D.exists_local_sourceEtaNormalization_symbols φu
  obtain ⟨Ue,hUe,hφe,_M,_hM,hEta⟩ := D.exists_local_normalizedWeightedEta_analytic w φ
  obtain ⟨Ub,hUb,hrealUb,hUbW,hBa,hBcoords⟩ := D.exists_normalizedWeightedBirkhoffMap_analytic w
  let L := normalizedWeightedSourceCLM (p := p) w
  let U := (Ue∩Ub)∩L ⁻¹' Ur
  have hU : IsOpen U := (hUe.inter hUb).inter (hUr.preimage L.continuous)
  have hφU : φ.val∈U := ⟨⟨hφe,hrealUb φ.property⟩,hφr⟩
  refine ⟨U,hU,hφU,hBa.mono (fun _ h => h.1.2),C,hC,?_⟩
  intro sign hsign
  obtain ⟨hσa,hνa,hσd⟩ := hsymbol sign hsign
  have hσcomp : AnalyticOnNhd ℂ (normalizedWeightedEtaExponentSymbol hp hp1 s w sign) U := by
    intro ψ hψ
    exact (hσa (L ψ) hψ.2).comp (L.analyticAt ψ)
  have hνcomp : AnalyticOnNhd ℂ (normalizedWeightedEtaExponentInverseSymbol hp hp1 s w sign) U := by
    intro ψ hψ
    exact (hνa (L ψ) hψ.2).comp (L.analyticAt ψ)
  refine ⟨((hEta sign hsign).1).mono (fun _ h => h.1.1),hσcomp,hνcomp,?_⟩
  intro ψ hψ
  have hd := hσd (L ψ) hψ.2
  refine ⟨?_,hd.1,hd.2.1,fun n => (hd.2.2 n).2.2.2⟩
  ext n
  have hξ := (hd.2.2 n).1
  have hμ := (hd.2.2 n).2.1
  have hxy := D.coordinates (normalizedWeightedSource w ψ) (hUbW ψ hψ.1.2) n
  rw [((hEta sign hsign).2 ψ hψ.1.1).2 n]
  change (w (2*n) : ℂ)*sourceGapWeightedEtaCoordinate hp hp1 n s sign (L ψ)=
    normalizedWeightedEtaExponentSymbol hp hp1 s w sign ψ n*
      etaRectangularExponentCLM sign (normalizedWeightedBirkhoffMap hp hp1 s w ψ) n
  rw [sourceGapWeightedEtaCoordinate_eq_inverse_normalization hp hp1 n s sign (L ψ) hξ]
  rw [show normalizedWeightedEtaExponentSymbol hp hp1 s w sign ψ n=sourceEtaNormalizationSymbol hp hp1 s sign (L ψ) n from rfl,hμ,
    etaRectangularExponentCLM_apply,(hBcoords ψ hψ.1.2 n).1,(hBcoords ψ hψ.1.2 n).2,hxy.1,hxy.2,
    sourceBirkhoffWeightedCoordinate_eq_rectangular hp hp1 n s sign (L ψ) hsign]
  rw [show sourceBirkhoffX hp hp1 n s (L ψ)=
      sourceBirkhoffX hp hp1 n s (normalizedWeightedSource w ψ) from rfl,
    show sourceBirkhoffY hp hp1 n s (L ψ)=
      sourceBirkhoffY hp hp1 n s (normalizedWeightedSource w ψ) from rfl]
  ring

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
