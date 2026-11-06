import NLS.KdV.HillMiuraSobolevNormalizedSource
import NLS.ZakharovShabat.SourceWeightedEtaComplexAnalytic
import NLS.ZakharovShabat.SourceBirkhoffOriginalMap

/-! # Actual weighted eta sequences on native Sobolev Miura lifts

The SAME supplied root family is retained. The canonical weighted complex
eta theorem is composed with the exact normalized ordinary Dirichlet
source. One native complex neighborhood and bound precede BOTH signs
and EVERY signed index, at every physically real native base.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV

/-- The actual eta coefficients with their exact H^t weights. -/
def hillMiuraSobolevEtaSequence
    (s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n)
    (t : ℝ) (ht : 0≤t) (sign : ℂ)
    (a : WeightedCoeff (Weight.sobolev t) 2) : Coeff 2 :=
  normalizedWeightedEtaSequence (by norm_num) (by norm_num) s
    (sourceSobolevSpectralWeight t ht) sign (hillMiuraNormalizedSobolevDirichletSource t a)

/-- The actual original root family has weighted complex analytic eta
sequences near EVERY real native Sobolev base, with exact coefficients.
The common neighborhood and bound precede both signs and all indices. -/
theorem exists_hillMiuraSobolevEtaSequence_analytic
    {W0 W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) W0 W s)
    (t : ℝ) (ht : 0≤t) (a0 : WeightedCoeff (Weight.sobolev t) 2)
    (hr : periodOneL2Conjugation (WeightedCoeff.sobolevToL2 ht a0)=WeightedCoeff.sobolevToL2 ht a0) :
    ∃ V : Set (WeightedCoeff (Weight.sobolev t) 2), IsOpen V ∧ a0∈V ∧
      ∃ M : ℝ, 0≤M ∧ ∀ sign : ℂ, sign=1 ∨ sign=-1 →
        AnalyticOnNhd ℂ (hillMiuraSobolevEtaSequence s t ht sign) V ∧
        ∀ a∈V, ‖hillMiuraSobolevEtaSequence s t ht sign a‖≤M ∧
          ∀ n : ℤ, hillMiuraSobolevEtaSequence s t ht sign a n=
            (Weight.sobolev t n : ℂ)*sourceGapWeightedEtaCoordinate
              (by norm_num) (by norm_num) n s sign
                (sourcePhase (hillMiuraDiagonal (WeightedCoeff.sobolevToL2 ht a))) := by
  obtain ⟨B,D,_hactions⟩ := H.exists_original_birkhoff_map
  let J := hillMiuraNormalizedSobolevDirichletSource t
  let φ : realTypeSourceLocus 2 :=
    ⟨J a0,isRealType_hillMiuraNormalizedSobolevDirichletSource t ht a0 hr⟩
  obtain ⟨U,hU,hφU,M,hM,hEta⟩ :=
    D.exists_local_normalizedWeightedEta_analytic (sourceSobolevSpectralWeight t ht) φ
  let V : Set (WeightedCoeff (Weight.sobolev t) 2) := J ⁻¹' U
  refine ⟨V,hU.preimage J.continuous,hφU,M,hM,?_⟩
  intro sign hsign
  refine ⟨?_,?_⟩
  · intro a ha
    exact ((hEta sign hsign).1 (J a) ha).comp (J.analyticAt a)
  · intro a ha
    refine ⟨((hEta sign hsign).2 (J a) ha).1,?_⟩
    intro n
    have he := ((hEta sign hsign).2 (J a) ha).2 n
    simpa only [hillMiuraSobolevEtaSequence,J,sourceSobolevSpectralWeight_even,
      normalizedWeightedSource_hillMiuraSobolev] using he

end NLS.KdV
