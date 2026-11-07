import NLS.KdV.HillMiuraSobolevNormalizedSource
import NLS.ZakharovShabat.SourceWeightedOwnEtaDecay
import NLS.ZakharovShabat.SourceBirkhoffOriginalMap

/-! The SAME original own-index eta remainder is analytic and has
inverse-index decay near every real actual native H1 Miura source. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV

theorem exists_hillMiuraH1_own_eta_decay
    {W0 W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) W0 W s)
    (a0 : WeightedCoeff (Weight.sobolev 1) 2)
    (hr : periodOneL2Conjugation (WeightedCoeff.sobolevToL2 (by norm_num : (0:ℝ)≤1) a0)=
      WeightedCoeff.sobolevToL2 (by norm_num : (0:ℝ)≤1) a0) :
    ∃ V : Set (WeightedCoeff (Weight.sobolev 1) 2),IsOpen V ∧ a0∈V ∧
      (∀ n : ℤ,AnalyticOnNhd ℂ (fun a => sourceAngularEtaRemainder (by norm_num) (by norm_num) n s
        (sourcePhase (hillMiuraDiagonal (WeightedCoeff.sobolevToL2 (by norm_num : (0:ℝ)≤1) a)))) V) ∧
      ∃ K : ℝ,0≤K ∧ ∀ a∈V,∀ n : ℤ,(1+|(n:ℝ)|)*‖sourceAngularEtaRemainder (by norm_num) (by norm_num) n s
        (sourcePhase (hillMiuraDiagonal (WeightedCoeff.sobolevToL2 (by norm_num : (0:ℝ)≤1) a)))‖≤K := by
  obtain ⟨_B,D,_hactions⟩ := H.exists_original_birkhoff_map
  let J := hillMiuraNormalizedSobolevDirichletSource 1
  let φ : realTypeSourceLocus 2 := ⟨J a0,isRealType_hillMiuraNormalizedSobolevDirichletSource 1 (by norm_num) a0 hr⟩
  have hw (n : ℤ) : 1+|(n:ℝ)|≤sourceSobolevSpectralWeight 1 (by norm_num) (2*n) := by
    rw [sourceSobolevSpectralWeight_even]
    simp only [Weight.sobolev_apply,Real.rpow_one,le_refl]
  obtain ⟨U,hU,hφU,_hUW,ha,K,hK,hb⟩ := D.exists_local_normalizedWeighted_own_eta_decay
    (sourceSobolevSpectralWeight 1 (by norm_num)) hw φ
  refine ⟨J ⁻¹' U,hU.preimage J.continuous,hφU,?_,K,hK,?_⟩
  · intro n a haU
    have h := (ha n (J a) haU).comp (J.analyticAt a)
    simpa only [Function.comp_def,J,normalizedWeightedSource_hillMiuraSobolev] using h
  · intro a haU n
    simpa only [Function.comp_def,J,normalizedWeightedSource_hillMiuraSobolev] using hb (J a) haU n

end NLS.KdV
