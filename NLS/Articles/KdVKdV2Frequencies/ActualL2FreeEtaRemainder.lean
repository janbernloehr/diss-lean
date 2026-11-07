import NLS.Articles.KdVKdV2Frequencies.ActualL2AmplitudeError
import NLS.Articles.KdVKdV2Frequencies.ActualL2AmplitudeEtaRemainder
import NLS.SequenceSpaces.AnalyticAmplitudePacketRemainder

/-! Remove the ACTUAL coordinate phase, midpoint AND stored physical
amplitude from the SAME packet. Its core is the exact FREE amplitude
times the SAME eta, with a total analytic one-derivative remainder. -/
noncomputable section
open Set Metric Complex NLS.KdV
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies.RoughAbelianFourierDataAt
variable {q0 : PeriodOneHminusOne}

theorem exists_l2_free_eta_remainder (D : RoughAbelianFourierDataAt q0)
    (q : WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2)
    (hr : IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion 1 (by norm_num) q))
    (hq : periodOneSobolevImageInclusion 1 (by norm_num) q∈ball q0 D.radius) :
    ∃ U : Set (WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2), IsOpen U ∧ q∈U ∧
      ∃ CA CR : ℝ,∃ A : WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2 → WeightedCoeff (Weight.sobolev 1) 2,
      ∃ R : WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2 → WeightedCoeff (Weight.sobolev 2) 2,
        0≤CA ∧ 0≤CR ∧ AnalyticOnNhd ℂ A U ∧ AnalyticOnNhd ℂ R U ∧ ∀ p∈U,
          periodOneSobolevImageInclusion 1 (by norm_num) p∈ball q0 D.radius ∧ ‖A p‖≤CA ∧ ‖R p‖≤CR ∧
          (∀ j : ℤ,(R p).val j=D.packet (periodOneSobolevImageInclusion 1 (by norm_num) p) j-(A p).val j) ∧
          (∀ j : ℤ,j≤0 → (A p).val j=0) ∧ ∀ n : ℕ+,(A p).val (n:ℤ)=
            (Real.pi:ℂ)*(hillL2FreeAmplitude n:ℂ)*D.chart.sourceEtaSequence
              (periodOneSobolevImageInclusion 1 (by norm_num) p) (n:ℤ) := by
  let L := periodOneSobolevImageInclusion 1 (by norm_num : (0:ℝ)≤1)
  obtain ⟨V,hV,hqV,_CA0,CR0,A0,R0,_hCA0,hCR0,_hA0a,hR0a,h0⟩ :=
    D.exists_l2_amplitude_eta_remainder q hr hq
  obtain ⟨W,hW,hqW,_hWD,CM,M,hCM,hMa,hM⟩ := D.exists_l2_amplitude_error q hr hq
  obtain ⟨Z,hZ,hqZ,CF,F,hCF,hFa,hF⟩ := D.chart.exists_native_sobolev_eta_germ D.roots 1 (by norm_num) q
    (D.source_domain hq) (D.real_lift _ (D.source_domain hq).1.1 hr)
    (D.native_lifts 1 (by norm_num) q (D.source_domain hq).1.1)
  obtain ⟨U,hU,hqU,hUV,A,R,hAa,hRa,hd⟩ := Coeff.exists_analytic_amplitude_packet_remainder
    V W Z hV hW hZ q hqV hqW hqZ (fun p => D.packet (L p)) (fun p => D.chart.sourceEtaSequence (L p))
    (fun p j => D.amplitude (L p) j) hillL2FreeAmplitude (Real.pi:ℂ)
    (fun n => (hillL2FreeAmplitude_pos n).le) hillL2FreeAmplitude_le_one A0 R0 F M CR0 CF CM hCM
    hR0a hFa hMa (fun p hp => (h0 p hp).2.2.1) (fun p hp => (hF p hp).2.1)
    (fun p hp => (hM p hp).1) (fun p hp => (h0 p hp).2.2.2.1)
    (fun p hp => (h0 p hp).2.2.2.2.1) (fun p hp => (h0 p hp).2.2.2.2.2)
    (fun p hp => (hF p hp).2.2) (fun p hp => (hM p hp).2.1) (fun p hp => (hM p hp).2.2)
  refine ⟨U,hU,hqU,‖(Real.pi:ℂ)‖*CF,CR0+‖(Real.pi:ℂ)‖*(CM*CF),A,R,
    by positivity,by positivity,hAa,hRa,?_⟩
  intro p hp
  exact ⟨(h0 p (hUV hp)).1,(hd p hp).1,(hd p hp).2.1,(hd p hp).2.2.1,(hd p hp).2.2.2.1,(hd p hp).2.2.2.2⟩

end NLS.Articles.KdVKdV2Frequencies.RoughAbelianFourierDataAt
