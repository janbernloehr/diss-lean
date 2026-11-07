import NLS.Articles.KdVKdV2Frequencies.ActualL2EtaTerminalRemainder
import NLS.KdV.HillHminusL2SpectralFourierRemainders
import NLS.ZakharovShabat.SourceExactEtaTerminalFourier
import NLS.SequenceSpaces.AnalyticSpectralPacketRefinement

/-! The SAME actual packet differs by an analytic h2 remainder from
the EXACT free amplitude times the Fourier coefficients of its retained
native Miura lift. All spectral errors and original roots are retained. -/
noncomputable section
open Set Metric Complex NLS.KdV NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies.RoughAbelianFourierDataAt
variable {q0 : PeriodOneHminusOne}

theorem exists_l2_miura_fourier_remainder (D : RoughAbelianFourierDataAt q0)
    (q : WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2)
    (hr : IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion 1 (by norm_num) q))
    (hq : periodOneSobolevImageInclusion 1 (by norm_num) q∈ball q0 D.radius) :
    ∃ U : Set (WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2),IsOpen U ∧ q∈U ∧
      ∃ CA CR : ℝ,∃ A : WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2 → WeightedCoeff (Weight.sobolev 1) 2,
      ∃ R : WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2 → WeightedCoeff (Weight.sobolev 2) 2,
        0≤CA ∧ 0≤CR ∧ AnalyticOnNhd ℂ A U ∧ AnalyticOnNhd ℂ R U ∧ ∀ p∈U,
          periodOneSobolevImageInclusion 1 (by norm_num) p∈ball q0 D.radius ∧ ‖A p‖≤CA ∧ ‖R p‖≤CR ∧
          (∀ j : ℤ,(R p).val j=D.packet (periodOneSobolevImageInclusion 1 (by norm_num) p) j-(A p).val j) ∧
          (∀ j : ℤ,j≤0 → (A p).val j=0) ∧ ∀ n : ℕ+,(A p).val (n:ℤ)=
            (2*(Real.pi:ℂ)*I)*(hillL2FreeAmplitude n:ℂ)*
              D.chart.miura.lift (periodOneSobolevImageInclusion 1 (by norm_num) p) (n:ℤ) := by
  let L := periodOneSobolevImageInclusion 1 (by norm_num : (0:ℝ)≤1)
  obtain ⟨V,hV,hqV,CA0,CR0,A0,R0,hCA0,hCR0,hA0a,hR0a,h0⟩ := D.exists_l2_eta_terminal_remainder q hr hq
  obtain ⟨W,hW,hqW,C,M,S,hC,hMa,hSa,hWdata⟩ := D.chart.exists_native_l2_spectral_fourier_remainders
    D.native_lifts q (D.source_domain hq) (D.real_lift _ (D.source_domain hq).1.1 hr)
  let B := fun p j => -2*(D.chart.dirichletSource (L p)).snd j
  have hc (p) (hp : p∈V∩W) (n : ℕ+) : (A0 p).val (n:ℤ)=
      (Real.pi:ℂ)*(hillL2FreeAmplitude n:ℂ)*(B p (n:ℤ)+(-2:ℂ)*((M p).val (n:ℤ)+I*(S p).val (n:ℤ))) := by
    rw [(h0 p hp.1).2.2.2.2.2 n,((hWdata p hp.2).2.2.2 n).1,((hWdata p hp.2).2.2.2 n).2]
    have he := sourceExactEtaTerminal_fourier_decomposition (by norm_num : (2:ℝ≥0∞)≠⊤) (by norm_num)
      (D.chart.dirichletSource (L p)) (n:ℤ)
    have ht : D.chart.sourceEtaTerminal (n:ℤ) (L p)=B p (n:ℤ)+(-2:ℂ)*
        (sourceExactEtaMidpointFourierError (by norm_num) (by norm_num) (D.chart.dirichletSource (L p)) (n:ℤ)+
          I*sourceExactEtaSineFourierError (by norm_num) (by norm_num) (D.chart.dirichletSource (L p)) (n:ℤ)) := by
      change -2*(_+I*_)=(-2)*_+(-2)*(_+I*_)
      linear_combination (norm := ring) he
    exact congrArg (fun z : ℂ => (Real.pi:ℂ)*(hillL2FreeAmplitude n:ℂ)*z) ht
  obtain ⟨U,hU,hqU,hUV,A,R,hAa,hRa,hd⟩ := Coeff.exists_analytic_spectral_packet_refinement V W hV hW q hqV hqW
    (fun p => D.packet (L p)) B hillL2FreeAmplitude (Real.pi:ℂ)
    (fun n => (hillL2FreeAmplitude_pos n).le) hillL2FreeAmplitude_le_one A0 R0 M S CA0 CR0 C C
    hA0a hR0a hMa hSa (fun p hp => (h0 p hp).2.1) (fun p hp => (h0 p hp).2.2.1)
    (fun p hp => (hWdata p hp).2.1) (fun p hp => (hWdata p hp).2.2.1)
    (fun p hp => (h0 p hp).2.2.2.1) (fun p hp => (h0 p hp).2.2.2.2.1) hc
  refine ⟨U,hU,hqU,CA0+‖(Real.pi:ℂ)‖*(2*(C+C)),CR0+‖(Real.pi:ℂ)‖*(2*(C+C)),A,R,
    by positivity,by positivity,hAa,hRa,?_⟩
  intro p hp
  refine ⟨(h0 p (hUV hp)).1,(hd p hp).1,(hd p hp).2.1,(hd p hp).2.2.1,(hd p hp).2.2.2.1,?_⟩
  intro n
  rw [(hd p hp).2.2.2.2 n]
  simp only [B,HillHminusPsiChart.dirichletSource,sourcePhase_snd,hillMiuraDiagonal_snd,
    lp.coeFn_smul,Pi.smul_apply,smul_eq_mul]
  ring

end NLS.Articles.KdVKdV2Frequencies.RoughAbelianFourierDataAt
