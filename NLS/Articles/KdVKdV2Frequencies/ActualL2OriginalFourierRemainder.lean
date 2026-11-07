import NLS.Articles.KdVKdV2Frequencies.ActualL2MiuraFourierRemainder
import NLS.KdV.HillHminusL2MiuraNonlinear
import NLS.KdV.HillHminusMiuraNonzeroEquation
import NLS.SequenceSpaces.AnalyticBracketPacketRefinement

/-! The SAME actual packet differs from the ORIGINAL potential Fourier
core by a TOTAL analytic h2 remainder. The actual shifted Miura equation
removes the retained lift with its exact finite-index 1+n normalization. -/
noncomputable section
open Set Metric Complex NLS.KdV
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies.RoughAbelianFourierDataAt
variable {q0 : PeriodOneHminusOne}

theorem exists_l2_original_fourier_remainder (D : RoughAbelianFourierDataAt q0)
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
            (hillL2FreeAmplitude n:ℂ)/(1+(n:ℂ))*p.val (n:ℤ) := by
  let L := periodOneSobolevImageInclusion 1 (by norm_num : (0:ℝ)≤1)
  obtain ⟨V,hV,hqV,CA0,CR0,A0,R0,hCA0,hCR0,hA0a,hR0a,h0⟩ := D.exists_l2_miura_fourier_remainder q hr hq
  obtain ⟨W,hW,hqW,C,T,hC,hTa,hWd⟩ := D.chart.exists_native_l2_miura_nonlinear
    D.native_lifts q (D.source_domain hq).1.1
  let B := fun (n : ℕ+) (p : WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2) => (hillL2FreeAmplitude n:ℂ)/(1+(n:ℂ))*p.val (n:ℤ)
  have hc (p) (hp : p∈V∩W) (n : ℕ+) : (A0 p).val (n:ℤ)=
      B n p+(hillL2FreeAmplitude n:ℂ)/(1+(n:ℂ))*(T p).val (n:ℤ) := by
    rw [(h0 p hp.1).2.2.2.2.2 n,(hWd p hp.2).2.2 n]
    have hn : (n:ℤ)≠0 := ne_of_gt (by exact_mod_cast n.pos : (0:ℤ)<n)
    have he := D.chart.retained_miura_nonzero_equation (L p) (hWd p hp.2).1 (n:ℤ) hn
    rw [periodOneSobolevImageInclusion_apply] at he
    simp only [L,Int.cast_natCast] at he
    have hne : 1+(n:ℂ)≠0 := by exact_mod_cast (show 1+(n:ℝ)≠0 by positivity)
    dsimp only [B]
    field_simp
    linear_combination (norm := ring) (hillL2FreeAmplitude n:ℂ)*he
  obtain ⟨U,hU,hqU,hUV,A,R,hAa,hRa,hd⟩ := Coeff.exists_analytic_bracket_packet_refinement
    V W hV hW q hqV hqW (fun p => D.packet (L p)) B hillL2FreeAmplitude
    (fun n => (hillL2FreeAmplitude_pos n).le) hillL2FreeAmplitude_le_one A0 R0 T CA0 CR0 C
    hA0a hR0a hTa (fun p hp => (h0 p hp).2.1) (fun p hp => (h0 p hp).2.2.1)
    (fun p hp => (hWd p hp).2.1) (fun p hp => (h0 p hp).2.2.2.1)
    (fun p hp => (h0 p hp).2.2.2.2.1) hc
  refine ⟨U,hU,hqU,CA0+C,CR0+C,A,R,add_nonneg hCA0 hC,add_nonneg hCR0 hC,hAa,hRa,?_⟩
  intro p hp
  exact ⟨(h0 p (hUV hp)).1,(hd p hp).1,(hd p hp).2⟩

end NLS.Articles.KdVKdV2Frequencies.RoughAbelianFourierDataAt
