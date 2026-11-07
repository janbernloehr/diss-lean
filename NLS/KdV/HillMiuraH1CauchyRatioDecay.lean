import NLS.ZakharovShabat.SourceCauchyEnergyRatioDecay
import NLS.ZakharovShabat.SourceSobolevNormalizedCoordinates
import NLS.KdV.HillMiuraSobolevNormalizedSource

/-! Exact quantitative Cauchy action-ratio decay for the SAME actual
Miura lift in native H1. The source normalization uses 1+2|n| and
is decoded exactly; the physical free factor is 2*pi*n. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV

theorem sobolevSourceInclusion_pair_eq_hillMiura (a : WeightedCoeff (Weight.sobolev 1) 2) :
    sobolevSourceInclusion (a,a)=hillMiuraDiagonal (WeightedCoeff.sobolevToL2 (by norm_num : (0:ℝ)≤1) a) := by
  apply (CoeffPair.toMax 2).injective
  apply Prod.ext
  · ext n
    change (sobolevSourceInclusion (a,a)).fst n=(hillMiuraDiagonal _).fst n
    rw [sobolevSourceInclusion_fst,hillMiuraDiagonal_fst,WeightedCoeff.sobolevToL2_apply]
  · ext n
    change (sobolevSourceInclusion (a,a)).snd n=(hillMiuraDiagonal _).snd n
    rw [sobolevSourceInclusion_snd,hillMiuraDiagonal_snd,WeightedCoeff.sobolevToL2_apply]

theorem exists_hillMiuraH1_cauchy_energyRatio_decay {W : Set (CoeffPair 2)}
    (C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W)
    (a0 : WeightedCoeff (Weight.sobolev 1) 2)
    (hr : periodOneL2Conjugation (WeightedCoeff.sobolevToL2 (by norm_num : (0:ℝ)≤1) a0)=
      WeightedCoeff.sobolevToL2 (by norm_num : (0:ℝ)≤1) a0)
    (hC : hillMiuraDiagonal (WeightedCoeff.sobolevToL2 (by norm_num : (0:ℝ)≤1) a0)∈
      Metric.ball C.discs.source.val C.discs.sourceRadius) :
    ∃ V : Set (WeightedCoeff (Weight.sobolev 1) 2), IsOpen V ∧ a0∈V ∧
      ∃ N : ℕ, ∃ K : ℝ, 0≤K ∧ ∀ a∈V,
        hillMiuraDiagonal (WeightedCoeff.sobolevToL2 (by norm_num : (0:ℝ)≤1) a)∈
          Metric.ball C.discs.source.val C.discs.sourceRadius ∧
        ∀ n : ℕ+, N≤(n:ℕ) →
          (1+(n:ℝ))*‖(2*((Real.pi:ℂ)*(n:ℕ)))*C.normalizedEnergyActionRatio (n:ℕ)
            (hillMiuraDiagonal (WeightedCoeff.sobolevToL2 (by norm_num : (0:ℝ)≤1) a))-1‖≤K := by
  let X := WeightedCoeff (Weight.sobolev 1) 2
  let J : X →L[ℂ] CoeffPair 2 := sobolevNormalizedCoordinates.toContinuousLinearMap.comp
    ((ContinuousLinearMap.id ℂ X).prod (ContinuousLinearMap.id ℂ X))
  have hdecode (a : X) : normalizedWeightedSource (SpectralWeight.sobolev 1 (by norm_num)) (J a)=
      hillMiuraDiagonal (WeightedCoeff.sobolevToL2 (by norm_num : (0:ℝ)≤1) a) :=
    (normalizedWeightedSource_sobolevNormalizedCoordinates (a,a)).trans (sobolevSourceInclusion_pair_eq_hillMiura a)
  have hreal : IsRealType (CoeffPair.toMax 2 (J a0)) := by
    apply (sobolevNormalizedCoordinates_realType_iff (a0,a0)).mpr
    rw [sobolevSourceInclusion_pair_eq_hillMiura]
    exact isRealType_hillMiuraDiagonal ⟨_,(periodOneL2Conjugation_fixed_iff _).mp hr⟩
  obtain ⟨U,hU,hJU,hUC,N,K,hK,hb⟩ := C.exists_local_normalizedSobolev_energyActionRatio_decay
    ⟨J a0,hreal⟩ (by rw [hdecode];exact hC)
  refine ⟨J ⁻¹' U,hU.preimage J.continuous,hJU,N,K,hK,?_⟩
  intro a ha
  refine ⟨by simpa only [hdecode] using hUC (J a) ha,?_⟩
  intro n hn
  simpa only [hdecode] using hb (J a) ha n hn

end NLS.KdV
