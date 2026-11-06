import NLS.ZakharovShabat.SourceEtaNormalizationSymbol
import NLS.ZakharovShabat.NormalizedWeightedBirkhoffDifferential

/-! # Exact native factorization of ACTUAL weighted eta

Both actual eta signs factor through the SAME normalized weighted
Birkhoff map and literal inverse-root/phase symbol. Every coefficient
is exact on ONE open complex neighborhood of each normalized real base.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The original signed complex coordinate, with its exact rectangular normalization. -/
def etaRectangularCLM (sign : ℂ) : (Coeff 2 × Coeff 2) →L[ℂ] Coeff 2 :=
  ((Real.sqrt 8 : ℂ)/2) • (ContinuousLinearMap.fst ℂ (Coeff 2) (Coeff 2)+
    (sign*I) • ContinuousLinearMap.snd ℂ (Coeff 2) (Coeff 2))

@[simp] theorem etaRectangularCLM_apply (sign : ℂ) (a : Coeff 2 × Coeff 2) (n : ℤ) :
    etaRectangularCLM sign a n=((Real.sqrt 8 : ℂ)/2)*(a.1 n+sign*I*a.2 n) := by
  change (((Real.sqrt 8 : ℂ)/2) • (a.1+(sign*I) • a.2)) n=_
  simp only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,lp.coeFn_add,Pi.add_apply]

/-- The actual normalization symbol in normalized spectral-weight coordinates. -/
def normalizedWeightedEtaSymbol
    (s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n) (w : SpectralWeight) (sign : ℂ)
    (ψ : CoeffPair 2) : Coeff ⊤ :=
  sourceEtaNormalizationSymbol (by norm_num) (by norm_num) s sign (normalizedWeightedSource w ψ)

def normalizedWeightedEtaInverseSymbol
    (s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n) (w : SpectralWeight) (sign : ℂ)
    (ψ : CoeffPair 2) : Coeff ⊤ :=
  sourceEtaNormalizationInverseSymbol (by norm_num) (by norm_num) s sign (normalizedWeightedSource w ψ)

namespace SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- At EVERY normalized real base and EVERY spectral weight, the SAME
actual eta has its exact native analytic inverse-normalization factorization.
ONE domain and bound precede BOTH signs and EVERY signed index. -/
theorem exists_local_normalizedWeightedEta_factorization
    (D : SourceBirkhoffMapComplexData (by norm_num) (by norm_num) W₀ B W s)
    (w : SpectralWeight) (φ : realTypeSourceLocus 2) :
    ∃ U : Set (CoeffPair 2), IsOpen U ∧ φ.val∈U ∧
      AnalyticOnNhd ℂ (normalizedWeightedBirkhoffMap (by norm_num) (by norm_num) s w) U ∧
      ∃ C : ℝ, 0<C ∧ ∀ sign : ℂ, sign=1 ∨ sign=-1 →
        AnalyticOnNhd ℂ (normalizedWeightedEtaSequence (by norm_num) (by norm_num) s w sign) U ∧
        AnalyticOnNhd ℂ (normalizedWeightedEtaSymbol s w sign) U ∧
        AnalyticOnNhd ℂ (normalizedWeightedEtaInverseSymbol s w sign) U ∧ ∀ ψ∈U,
          normalizedWeightedEtaSequence (by norm_num) (by norm_num) s w sign ψ=
            Coeff.holderProduct (q := 2) (normalizedWeightedEtaSymbol s w sign ψ)
              (etaRectangularCLM sign (normalizedWeightedBirkhoffMap (by norm_num) (by norm_num) s w ψ)) ∧
          ‖normalizedWeightedEtaSymbol s w sign ψ‖≤C ∧
          ‖normalizedWeightedEtaInverseSymbol s w sign ψ‖≤C ∧ ∀ n,
            normalizedWeightedEtaSymbol s w sign ψ n*normalizedWeightedEtaInverseSymbol s w sign ψ n=1 := by
  let φu : realTypeSourceSubmodule 2 :=
    ⟨normalizedWeightedSource w φ.val,normalizedWeightedSource_realType w φ.val φ.property⟩
  obtain ⟨Ur,hUr,hφr,_hUrW,C,hC,hsymbol⟩ := D.exists_local_sourceEtaNormalization_symbols φu
  obtain ⟨Ue,hUe,hφe,_M,_hM,hEta⟩ := D.exists_local_normalizedWeightedEta_analytic w φ
  obtain ⟨Ub,hUb,hrealUb,hUbW,hBa,hBcoords⟩ := D.exists_normalizedWeightedBirkhoffMap_analytic w
  let L := normalizedWeightedSourceCLM (p := 2) w
  let U := (Ue∩Ub)∩L ⁻¹' Ur
  have hU : IsOpen U := (hUe.inter hUb).inter (hUr.preimage L.continuous)
  have hφU : φ.val∈U := ⟨⟨hφe,hrealUb φ.property⟩,hφr⟩
  refine ⟨U,hU,hφU,hBa.mono (fun _ h => h.1.2),C,hC,?_⟩
  intro sign hsign
  obtain ⟨hσa,hνa,hσd⟩ := hsymbol sign hsign
  have hσcomp : AnalyticOnNhd ℂ (normalizedWeightedEtaSymbol s w sign) U := by
    intro ψ hψ
    exact (hσa (L ψ) hψ.2).comp (L.analyticAt ψ)
  have hνcomp : AnalyticOnNhd ℂ (normalizedWeightedEtaInverseSymbol s w sign) U := by
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
  change (w (2*n) : ℂ)*sourceGapWeightedEtaCoordinate (by norm_num) (by norm_num) n s sign (L ψ)=
    normalizedWeightedEtaSymbol s w sign ψ n*
      etaRectangularCLM sign (normalizedWeightedBirkhoffMap (by norm_num) (by norm_num) s w ψ) n
  rw [sourceGapWeightedEtaCoordinate_eq_inverse_normalization (by norm_num) (by norm_num) n s sign (L ψ) hξ]
  rw [show normalizedWeightedEtaSymbol s w sign ψ n=sourceEtaNormalizationSymbol (by norm_num) (by norm_num) s sign (L ψ) n from rfl,hμ,
    etaRectangularCLM_apply,(hBcoords ψ hψ.1.2 n).1,(hBcoords ψ hψ.1.2 n).2,hxy.1,hxy.2,
    sourceBirkhoffWeightedCoordinate_eq_rectangular (by norm_num) (by norm_num) n s sign (L ψ) hsign]
  rw [show sourceBirkhoffX (by norm_num) (by norm_num) n s (L ψ)=
      sourceBirkhoffX (by norm_num) (by norm_num) n s (normalizedWeightedSource w ψ) from rfl,
    show sourceBirkhoffY (by norm_num) (by norm_num) n s (L ψ)=
      sourceBirkhoffY (by norm_num) (by norm_num) n s (normalizedWeightedSource w ψ) from rfl]
  ring

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
