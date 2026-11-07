import NLS.Articles.KdVKdV2Frequencies.ActualL2OriginalFourierIdentification
import NLS.KdV.HillRawFreeFourierNormalization
import NLS.SequenceSpaces.SignedHalfOriginalFourierCore
import NLS.SequenceSpaces.SignedHalfOrderDecomposition

/-! The SAME signed physical forward map on ORIGINAL L2 differs from
its exactly normalized ORIGINAL Fourier core by a locally bounded analytic
raw h^(3/2) remainder. All original source conjugations/signs are retained. -/
noncomputable section
open Set Metric Complex NLS.KdV
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

theorem exists_actual_l2_raw_original_fourier_remainder (D : GlobalRoughAbelianForwardData)
    (q : WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2)
    (hqr : IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion 1 (by norm_num) q)) :
    let q0 : PeriodOneRealHminusOne := ⟨periodOneSobolevImageInclusion 1 (by norm_num) q,hqr⟩
    let E := D.chart q0
    ∃ V : Set (WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2), IsOpen V ∧ q∈V ∧
      ∃ CA CR : ℝ,
      ∃ A : WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2 → WeightedCoeff (Weight.sobolev (1-1/2)) 2,
      ∃ R : WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2 → WeightedCoeff (Weight.sobolev (2-1/2)) 2,
        0≤CA ∧ 0≤CR ∧ AnalyticOnNhd ℂ A V ∧ AnalyticOnNhd ℂ R V ∧ ∀ p∈V,
          periodOneSobolevImageInclusion 1 (by norm_num) p∈D.domain ∧ ‖A p‖≤CA ∧ ‖R p‖≤CR ∧
          D.signed (periodOneSobolevImageInclusion 1 (by norm_num) p)=
            WeightedCoeff.sobolevInclusion (by norm_num : (-1/2:ℝ)≤1-1/2) (A p)+
            WeightedCoeff.sobolevInclusion (by norm_num : (-1/2:ℝ)≤2-1/2) (R p) ∧
          (A p).val 0=0 ∧ ∀ n : ℕ+,
            (A p).val (n:ℤ)=(if E.signs (n:ℤ) then -((Real.sqrt (2*Real.pi*(n:ℝ)):ℂ)⁻¹*p.val (n:ℤ))
              else (Real.sqrt (2*Real.pi*(n:ℝ)):ℂ)⁻¹*p.val (n:ℤ)) ∧
            (A p).val (-(n:ℤ))=(if E.signs (n:ℤ) then -((Real.sqrt (2*Real.pi*(n:ℝ)):ℂ)⁻¹*p.val (-(n:ℤ)))
              else (Real.sqrt (2*Real.pi*(n:ℝ)):ℂ)⁻¹*p.val (-(n:ℤ))) := by
  let v := Weight.sobolev ((1:ℝ)-1)
  let L := periodOneSobolevImageInclusion 1 (by norm_num)
  let q0 : PeriodOneRealHminusOne := ⟨L q,hqr⟩
  let E := D.chart q0
  obtain ⟨U,hU,hqU,CA,CR,A,R,hCA,hCR,hAa,hRa,hd⟩ := D.exists_actual_l2_original_fourier_decomposition q hqr
  have hJq := sobolev_conjugateReflection_fixed_of_real_inclusion 1 (by norm_num) q hqr
  obtain ⟨V,hV,hqV,hVU,hJV,hAva,hRva,hs⟩ := WeightedCoeff.exists_signed_half_packet_decomposition
    v (Weight.sobolev_neg _) U hU q hqU hJq E.signs (fun p => D.positive (L p)) A R CA CR hAa hRa
    (fun p hp => (hd p hp).2.1) (fun p hp => (hd p hp).2.2.1) (fun p hp => (hd p hp).2.2.2.1)
  refine ⟨V,hV,hqV,2*CA,2*CR,WeightedCoeff.signedHalfTarget v 1 E.signs A,
    WeightedCoeff.signedHalfTarget v 2 E.signs R,mul_nonneg (by norm_num) hCA,
    mul_nonneg (by norm_num) hCR,hAva,hRva,?_⟩
  intro p hp
  refine ⟨(hd p (hVU hp)).1,(hs p hp).1,(hs p hp).2.1,?_,?_⟩
  · have he : D.signed (L p)=WeightedCoeff.signedTargetLift v (Weight.sobolev (-1/2))
        (fun z => D.positive (L z)) p := by
      apply Subtype.ext
      funext j
      rw [signed,WeightedCoeff.signedTargetLift_apply,WeightedCoeff.signedTargetLift_apply,
        WeightedCoeff.normalizedSignedCompletion_apply _ (Weight.sobolev_neg (-1)),
        WeightedCoeff.normalizedSignedCompletion_apply v (Weight.sobolev_neg _)]
      rw [periodOneSobolevImageInclusion_conjugateReflection 1 (by norm_num)]
      rfl
    exact he.trans (hs p hp).2.2
  have hc := WeightedCoeff.signedHalfTarget_exact_fourier_core v (Weight.sobolev_neg _) U E.signs A
    (fun n => hillL2FreeAmplitude n/(1+(n:ℝ))) (fun n => (Real.sqrt (2*Real.pi*(n:ℝ)))⁻¹)
    (fun n => by rw [←mul_div_assoc];exact raw_free_amplitude_fourier_normalization n)
    (fun z hz => (hd z hz).2.2.2.2.1)
    (fun z hz n => by
      simpa only [Complex.ofReal_div,Complex.ofReal_add,Complex.ofReal_one,Complex.ofReal_natCast]
        using (hd z hz).2.2.2.2.2 n) p (hVU hp) (hJV p hp)
  simpa only [Complex.ofReal_inv] using hc

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
