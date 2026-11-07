import NLS.Articles.KdVKdV2Frequencies.ActualL2RawFixedFourierRemainder
import NLS.ComplexAnalysis.AnalyticOpenGluing

/-! ONE analytic fixed-Fourier decomposition around the ENTIRE real
ORIGINAL L2 space, retaining the SAME global physical map and all local
uniform native bounds. The stronger remainders agree on full overlaps. -/
noncomputable section
open Set Complex NLS.KdV NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

theorem exists_global_l2_fixed_fourier_remainder (D : GlobalRoughAbelianForwardData) :
    ∃ U : Set (WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2),IsOpen U ∧
      (∀ q,IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion 1 (by norm_num) q) → q∈U) ∧
      ∃ A : WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2 → WeightedCoeff (Weight.sobolev (1-1/2)) 2,
      ∃ R : WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2 → WeightedCoeff (Weight.sobolev (2-1/2)) 2,
        AnalyticOnNhd ℂ A U ∧ AnalyticOnNhd ℂ R U ∧
        (∀ p∈U,periodOneSobolevImageInclusion 1 (by norm_num) p∈D.domain ∧
          D.signed (periodOneSobolevImageInclusion 1 (by norm_num) p)=
            WeightedCoeff.sobolevInclusion (by norm_num : (-1/2:ℝ)≤1-1/2) (A p)+
            WeightedCoeff.sobolevInclusion (by norm_num : (-1/2:ℝ)≤2-1/2) (R p) ∧
          (A p).val 0=0 ∧ ∀ n : ℕ+,
            (A p).val (n:ℤ)=(if D.fixedFourierSigns (n:ℤ) then -((Real.sqrt (2*Real.pi*(n:ℝ)):ℂ)⁻¹*p.val (n:ℤ))
              else (Real.sqrt (2*Real.pi*(n:ℝ)):ℂ)⁻¹*p.val (n:ℤ)) ∧
            (A p).val (-(n:ℤ))=(if D.fixedFourierSigns (n:ℤ) then -((Real.sqrt (2*Real.pi*(n:ℝ)):ℂ)⁻¹*p.val (-(n:ℤ)))
              else (Real.sqrt (2*Real.pi*(n:ℝ)):ℂ)⁻¹*p.val (-(n:ℤ)))) ∧
        ∀ q,IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion 1 (by norm_num) q) →
          ∃ V : Set (WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2),IsOpen V ∧ q∈V ∧ V⊆U ∧
            ∃ CA CR : ℝ,0≤CA ∧ 0≤CR ∧ ∀ p∈V,‖A p‖≤CA ∧ ‖R p‖≤CR := by
  classical
  let L := periodOneSobolevImageInclusion 1 (by norm_num : (0:ℝ)≤1)
  let I := {q : WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2 // IsRealPeriodOneHminusOne (L q)}
  choose V hV hqV CA CR A R hCA hCR hAa hRa hd using
    (fun q : I => D.exists_actual_l2_raw_fixed_fourier_remainder q.val q.property)
  let F := fun i : I => fun p => (A i p,R i p)
  have hF (i : I) : AnalyticOnNhd ℂ (F i) (V i) := (hAa i).prod (hRa i)
  have he (i j : I) : EqOn (F i) (F j) (V i∩V j) := by
    intro p hp
    have hA : A i p=A j p := by
      apply Subtype.ext
      funext k
      by_cases hk0 : k=0
      · subst k
        rw [(hd i p hp.1).2.2.2.2.1,(hd j p hp.2).2.2.2.2.1]
      by_cases hk : 0<k
      · let n := Coeff.positivePoleIndex k hk
        have hn : (n:ℤ)=k := by exact_mod_cast Coeff.positivePoleIndex_real k hk
        rw [←hn,((hd i p hp.1).2.2.2.2.2 n).1,((hd j p hp.2).2.2.2.2.2 n).1]
      · have hkp : 0< -k := by omega
        let n := Coeff.positivePoleIndex (-k) hkp
        have hn : (n:ℤ)= -k := by exact_mod_cast Coeff.positivePoleIndex_real (-k) hkp
        have hnk : -(n:ℤ)=k := by omega
        rw [←hnk,((hd i p hp.1).2.2.2.2.2 n).2,((hd j p hp.2).2.2.2.2.2 n).2]
    have hR : R i p=R j p := by
      have h := ((hd i p hp.1).2.2.2.1).symm.trans ((hd j p hp.2).2.2.2.1)
      rw [hA] at h
      have hc := add_left_cancel h
      apply Subtype.ext
      funext k
      have hk := congrArg (fun z : WeightedCoeff (Weight.sobolev (-1/2)) 2 => z.val k) hc
      simpa only [WeightedCoeff.sobolevInclusion_apply] using hk
    exact Prod.ext hA hR
  obtain ⟨T,hTa,hT⟩ := exists_analytic_open_gluing V hV F hF he
  refine ⟨⋃ i,V i,isOpen_iUnion hV,(fun q hq => mem_iUnion.mpr ⟨(⟨q,hq⟩ : I),hqV ⟨q,hq⟩⟩),
    (fun p => (T p).1),(fun p => (T p).2),(fun p hp => analyticAt_fst.comp (hTa p hp)),
    (fun p hp => analyticAt_snd.comp (hTa p hp)),?_,?_⟩
  · intro p hp
    obtain ⟨i,hi⟩ := mem_iUnion.mp hp
    have hAi := congrArg Prod.fst (hT i hi)
    have hRi := congrArg Prod.snd (hT i hi)
    dsimp only [F] at hAi hRi ⊢
    rw [hAi,hRi]
    exact ⟨(hd i p hi).1,(hd i p hi).2.2.2.1,(hd i p hi).2.2.2.2⟩
  intro q hq
  let i : I := ⟨q,hq⟩
  refine ⟨V i,hV i,hqV i,(fun p hp => mem_iUnion.mpr ⟨i,hp⟩),CA i,CR i,hCA i,hCR i,?_⟩
  intro p hp
  dsimp only
  rw [congrArg Prod.fst (hT i hp),congrArg Prod.snd (hT i hp)]
  exact ⟨(hd i p hp).2.1,(hd i p hp).2.2.1⟩

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
