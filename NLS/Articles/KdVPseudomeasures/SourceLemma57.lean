import NLS.Articles.KdVPseudomeasures.Lemma57CommonNeighborhood
import NLS.Articles.KdVPseudomeasures.OriginalHillWienerFrequencySequence

/-! Lemma 5.7 on every original physical integer-order Wiener source.
The complex source is its natural zero-mean coefficient Banach model.
A single complex neighborhood precedes every mode and every exponent p>1. -/
noncomputable section
open Set Complex NLS.KdV NLS.WeightedCoeff NLS.LpSequence
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures

abbrev OriginalWienerComplexFrequencySource (N : ℕ) :=
  zeroModeSubmodule (Weight.signedSobolev (signedStepOrder 0 N)) 1

private def wienerFrequencyRealInclusion (N : ℕ) :
    fourierRealZeroSubmodule (Weight.signedSobolev (signedStepOrder 0 N)) 1 →L[ℝ]
      HillComplexL2FrequencySource :=
  (fourierRealZeroSubmodule (Weight.signedSobolev 0) 2).subtypeL.comp
    ((signedIteratedInclusion 0 N).comp (hillWienerSourceHilbertInclusion N))

def originalWienerComplexFrequencyInclusion (N : ℕ) :
    OriginalWienerComplexFrequencySource N →L[ℂ] HillComplexL2FrequencySource :=
  (fourierRealContractiveComplexification (p := 1)
    (Weight.signedSobolev (signedStepOrder 0 N)) (Weight.signedSobolev_neg _)).complexifyLinear
      (wienerFrequencyRealInclusion N)

private theorem complexify_fourier_real {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (w : Weight) (hw : ∀ k, w (-k)=w k)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (f : fourierRealZeroSubmodule w p →L[ℝ] F) (a : fourierRealZeroSubmodule w p) :
    (fourierRealContractiveComplexification w hw).complexifyLinear f a.val = f a :=
  (fourierRealContractiveComplexification w hw).complexifyLinear_real f a

theorem originalWienerComplexFrequencyInclusion_real (N : ℕ) (q : OriginalWienerPotential N) :
    originalWienerComplexFrequencyInclusion N (originalWienerSourceCoefficients N q).val =
      (originalWienerL2Inclusion N q).val :=
  complexify_fourier_real _ _ (wienerFrequencyRealInclusion N) (originalWienerSourceCoefficients N q)

private theorem pullback_lp_data
    {E B : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup B] [NormedSpace ℂ B]
    (L : E →L[ℂ] B) (V : Set B) (F : B → Coeff ⊤)
    (hF : AnalyticOnNhd ℂ F V)
    (hp : ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → ∃ H : B → Coeff p,
      AnalyticOnNhd ℂ H V ∧ ∀ z ∈ V, ∀ k, H z k=F z k) :
    AnalyticOnNhd ℂ (fun z => F (L z)) (L ⁻¹' V) ∧
      ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → ∃ H : E → Coeff p,
        AnalyticOnNhd ℂ H (L ⁻¹' V) ∧ ∀ z ∈ L ⁻¹' V, ∀ k, H z k=F (L z) k := by
  refine ⟨fun z hz => (hF _ hz).comp (L.analyticAt z),?_⟩
  intro p inst hgt
  obtain ⟨H,hH,hc⟩ := hp p hgt
  exact ⟨(fun z => H (L z)),fun z hz => (hH _ hz).comp (L.analyticAt z),
    fun z hz k => hc _ hz k⟩

private theorem wiener_real_frequency_coordinates (N : ℕ)
    (F : HillComplexL2FrequencySource → Coeff ⊤)
    (hFr : ∀ q : HillRealL2BanachSource, ∀ k : ℤ, F q.val k = positiveScalarExtension
      (fun n => (hillRoughKdVFrequency n (hillL2SourceInclusion q):ℂ)-(2*(Real.pi:ℂ)*(n:ℤ))^3) k)
    (q : OriginalWienerPotential N) (n : ℕ+) :
    F (originalWienerComplexFrequencyInclusion N (originalWienerSourceCoefficients N q).val) (n:ℤ) =
      (hillRoughKdVFrequency n (originalHillRealMeanZeroSource (originalWienerOriginalPotential N q)):ℂ)-
        (2*(Real.pi:ℂ)*(n:ℤ))^3 := by
  have he := hFr (originalWienerL2Inclusion N q) (n:ℤ)
  have hnat := congrArg (fun a : HillRealMeanZeroSource =>
    (hillRoughKdVFrequency n a:ℂ)-(2*(Real.pi:ℂ)*(n:ℤ))^3)
    (originalWienerL2Inclusion_native N q)
  exact (congrArg (fun z : HillComplexL2FrequencySource => F z (n:ℤ))
    (originalWienerComplexFrequencyInclusion_real N q)).trans
      (he.trans ((positiveScalarExtension_apply _ n).trans hnat))

theorem sourceLemma5_7 (N : ℕ) :
    ∃ U : Set (OriginalWienerComplexFrequencySource N), IsOpen U ∧
      (∀ q : OriginalWienerPotential N, (originalWienerSourceCoefficients N q).val ∈ U) ∧
      ∃ F : OriginalWienerComplexFrequencySource N → Coeff ⊤,
        AnalyticOnNhd ℂ F U ∧
        (∀ q : OriginalWienerPotential N, ∀ n : ℕ+,
          F (originalWienerSourceCoefficients N q).val (n:ℤ) =
            (hillRoughKdVFrequency n (originalHillRealMeanZeroSource (originalWienerOriginalPotential N q)):ℂ)-
              (2*(Real.pi:ℂ)*(n:ℤ))^3) ∧
        ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p →
          ∃ H : OriginalWienerComplexFrequencySource N → Coeff p,
            AnalyticOnNhd ℂ H U ∧ ∀ z ∈ U, ∀ k, H z k=F z k := by
  obtain ⟨V,hV,hreal,F,hF,hFr,hp⟩ := sourceLemma5_7_L2
  let L := originalWienerComplexFrequencyInclusion N
  let U := L ⁻¹' V
  have hU : IsOpen U := hV.preimage L.continuous
  have hpoint (q : OriginalWienerPotential N) :
      L (originalWienerSourceCoefficients N q).val=(originalWienerL2Inclusion N q).val :=
    originalWienerComplexFrequencyInclusion_real N q
  have hcenter (q : OriginalWienerPotential N) : (originalWienerSourceCoefficients N q).val ∈ U :=
    NLS.FunctionalAnalysis.mem_preimage_of_apply_mem L V _
      ((hpoint q).symm ▸ hreal (originalWienerL2Inclusion N q))
  have hdata := pullback_lp_data L V F hF hp
  exact ⟨U,hU,hcenter,(fun z => F (L z)),hdata.1,
    wiener_real_frequency_coordinates N F hFr,hdata.2⟩

end NLS.Articles.KdVPseudomeasures
