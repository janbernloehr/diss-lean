import NLS.Articles.KdVKdV2Frequencies.ActualL2CoordinatePhaseData
import NLS.KdV.HillHminusMidpointNormalization
import NLS.SequenceSpaces.AnalyticTwoFactorPullback

/-! Removing BOTH actual coordinate phase and normalized midpoint leaves
pi times the SAME amplitude and eta, with an analytic one-derivative
remainder. The amplitude and spectral Fourier errors remain essential. -/
noncomputable section
open Set Metric Complex NLS.KdV
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies.RoughAbelianFourierDataAt
variable {q0 : PeriodOneHminusOne}

theorem exists_l2_amplitude_eta_remainder
    (D : RoughAbelianFourierDataAt q0)
    (q : WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2)
    (hqr : IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion 1 (by norm_num) q))
    (hq : periodOneSobolevImageInclusion 1 (by norm_num) q∈ball q0 D.radius) :
    ∃ U : Set (WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2), IsOpen U ∧ q∈U ∧
      ∃ CA CR : ℝ, ∃ A : WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2 → WeightedCoeff (Weight.sobolev 1) 2,
      ∃ R : WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2 → WeightedCoeff (Weight.sobolev 2) 2,
        0≤CA ∧ 0≤CR ∧ AnalyticOnNhd ℂ A U ∧ AnalyticOnNhd ℂ R U ∧ ∀ p∈U,
          periodOneSobolevImageInclusion 1 (by norm_num) p∈ball q0 D.radius ∧ ‖A p‖≤CA ∧ ‖R p‖≤CR ∧
          (∀ j : ℤ, (R p).val j=D.packet (periodOneSobolevImageInclusion 1 (by norm_num) p) j-(A p).val j) ∧
          (∀ j : ℤ, j≤0 → (A p).val j=0) ∧
          ∀ n : ℕ+, (A p).val (n:ℤ)=(Real.pi:ℂ)*D.amplitude (periodOneSobolevImageInclusion 1 (by norm_num) p) (n:ℤ)*
            D.chart.sourceEtaSequence (periodOneSobolevImageInclusion 1 (by norm_num) p) (n:ℤ) := by
  obtain ⟨V,hV,hqV,B,C₁,K₁,F,N₁,M₁,hB,hC₁,hK₁,hFa,hN₁a,hM₁a,hdata⟩ :=
    D.exists_l2_coordinate_phase_data q hqr hq
  let L := periodOneSobolevImageInclusion 1 (by norm_num : (0:ℝ)≤1)
  obtain ⟨Z,hZ,hqZ,_hZP,C₂,K₂,N₂,M₂,hC₂,hK₂,hN₂a,hM₂a,hmid⟩ :=
    D.chart.exists_local_midpoint_normalization_data D.roots (L q) (D.source_domain hq)
      (D.real_lift _ (D.source_domain hq).1.1 hqr)
  have hd₁ (p) (hp : p∈V) : (L p)∈ball q0 D.radius ∧ ‖F p‖≤B ∧ ‖N₁ p‖≤C₁ ∧ ‖M₁ p‖≤K₁ ∧
      (∀ j : ℤ, F p j=(Weight.sobolev 1 j:ℂ)*D.packet (L p) j) ∧
      ∀ j : ℤ, M₁ p j*N₁ p j*D.packet (L p) j=
        (Weight.sobolev 1 j:ℂ)*(D.packet (L p) j-N₁ p j*D.packet (L p) j) := by
    obtain ⟨hpD,hFb,hNb,hMb,hFc,hc,_hinv⟩ := hdata p hp
    exact ⟨hpD,hFb,hNb,hMb,hFc,hc⟩
  obtain ⟨U,hU,hqU,hUV,A,R,hAa,hRa,hd⟩ := Coeff.exists_two_factor_remainder_from_rough_data
    L V Z q hV hZ hqV hqZ D.packet F N₁ M₁ N₂ M₂
    (fun n a => D.chart.sourceNormalizedMidpoint n a/(Real.pi:ℂ)) (fun a => a∈ball q0 D.radius)
    B C₁ K₁ C₂ K₂ hC₁ hK₁ hC₂ hK₂ hFa hN₁a hM₁a hN₂a hM₂a hd₁
    (fun p hp j hj => (D.packet_data (L p) (hdata p hp).1).2.2 j hj)
    (fun a ha => (hmid a ha).1) (fun a ha => (hmid a ha).2.1)
    (fun a ha n => ((hmid a ha).2.2 n).1) (fun a ha n => ((hmid a ha).2.2 n).2.1)
  refine ⟨U,hU,hqU,C₂*(C₁*B),K₁*(C₁*B)+K₂*(C₂*(C₁*B)),A,R,
    by positivity,by positivity,hAa,hRa,?_⟩
  intro p hp
  obtain ⟨hpZ,hpD,hAb,hRb,hAc,hRc⟩ := hd p hp
  refine ⟨hpD,hAb,hRb,hRc,?_,?_⟩
  · intro j hj
    rw [hAc j,(D.packet_data (L p) hpD).2.2 j hj,mul_zero,mul_zero]
  intro n
  change (A p).val (n:ℤ)=(Real.pi:ℂ)*D.amplitude (L p) (n:ℤ)*D.chart.sourceEtaSequence (L p) (n:ℤ)
  have hN₁ : N₁ p (n:ℤ)=exp (-I*D.chart.sourceNoncentralBeta n (L p)) :=
    (hdata p (hUV hp)).2.2.2.2.2.2 n
  have hmidN : D.chart.sourceNormalizedMidpoint n (L p)*N₂ (L p) (n:ℤ)=(Real.pi:ℂ) :=
    ((hmid (L p) hpZ).2.2 n).2.2.1
  rw [hAc n,hN₁,D.packet_coordinates _ hpD n]
  unfold HillHminusPsiChart.sourceAbelianCoordinateFormula
  have he : exp (I*D.chart.sourceNoncentralBeta n (L p))*exp (-I*D.chart.sourceNoncentralBeta n (L p))=1 := by
    rw [←exp_add,show I*D.chart.sourceNoncentralBeta n (L p)+-I*D.chart.sourceNoncentralBeta n (L p)=0 by ring,exp_zero]
  calc
    _ = (D.chart.sourceNormalizedMidpoint n (L p)*N₂ (L p) (n:ℤ))*
        (D.amplitude (L p) (n:ℤ)*D.chart.sourceEtaSequence (L p) (n:ℤ))*
        (exp (I*D.chart.sourceNoncentralBeta n (L p))*exp (-I*D.chart.sourceNoncentralBeta n (L p))) := by ring
    _ = _ := by rw [hmidN,he,mul_one];ring

end NLS.Articles.KdVKdV2Frequencies.RoughAbelianFourierDataAt
