import NLS.KdV.HillMiuraSobolevNormalizedSource
import NLS.ZakharovShabat.SourceExactEtaMidpointFourierAnalytic
import NLS.ZakharovShabat.SourceExactEtaSineFourierAnalytic

/-! Actual literal midpoint and sine Fourier errors of the SAME native
H1 Dirichlet Miura source are analytic in h2 on one common neighborhood. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV

def hillMiuraH1DirichletPair : WeightedCoeff (Weight.sobolev 1) 2 →L[ℂ] SobolevSource 1 :=
  ((I:ℂ) • (WeightedCoeff.sobolevInclusion (p := 2) (by norm_num : ((1:ℕ):ℝ)≤1))).prod
    ((-I:ℂ) • (WeightedCoeff.sobolevInclusion (p := 2) (by norm_num : ((1:ℕ):ℝ)≤1)))

theorem hillMiuraH1DirichletPair_decode (a : WeightedCoeff (Weight.sobolev 1) 2) :
    higherSobolevSourceInclusion 1 (hillMiuraH1DirichletPair a)=
      sourcePhase (hillMiuraDiagonal (WeightedCoeff.sobolevToL2 (by norm_num : (0:ℝ)≤1) a)) := by
  apply (CoeffPair.toMax 2).injective
  apply Prod.ext
  · ext n
    change (higherSobolevSourceInclusion 1 (hillMiuraH1DirichletPair a)).fst n=(sourcePhase _).fst n
    rw [higherSobolevSourceInclusion_fst,sourcePhase_fst,hillMiuraDiagonal_fst]
    simp only [hillMiuraH1DirichletPair,ContinuousLinearMap.prod_apply,smul_apply,
      WeightedCoeff.smul_val,WeightedCoeff.sobolevInclusion_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,
      WeightedCoeff.sobolevToL2_apply]
  · ext n
    change (higherSobolevSourceInclusion 1 (hillMiuraH1DirichletPair a)).snd n=(sourcePhase _).snd n
    rw [higherSobolevSourceInclusion_snd,sourcePhase_snd,hillMiuraDiagonal_snd]
    simp only [hillMiuraH1DirichletPair,ContinuousLinearMap.prod_apply,smul_apply,
      WeightedCoeff.smul_val,WeightedCoeff.sobolevInclusion_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,
      WeightedCoeff.sobolevToL2_apply]

theorem exists_hillMiuraH1_spectral_fourier_remainders
    (a0 : WeightedCoeff (Weight.sobolev 1) 2)
    (hr : periodOneL2Conjugation (WeightedCoeff.sobolevToL2 (by norm_num : (0:ℝ)≤1) a0)=
      WeightedCoeff.sobolevToL2 (by norm_num : (0:ℝ)≤1) a0) :
    ∃ U : Set (WeightedCoeff (Weight.sobolev 1) 2),IsOpen U ∧ a0∈U ∧
      ∃ CM CS : ℝ,∃ M S : WeightedCoeff (Weight.sobolev 1) 2 → WeightedCoeff (Weight.sobolev 2) 2,
        0≤CM ∧ 0≤CS ∧ AnalyticOnNhd ℂ M U ∧ AnalyticOnNhd ℂ S U ∧ ∀ a∈U,
          ‖M a‖≤CM ∧ ‖S a‖≤CS ∧ ∀ n : ℤ,
            (M a).val n=sourceExactEtaMidpointFourierError (by norm_num) (by norm_num)
              (sourcePhase (hillMiuraDiagonal (WeightedCoeff.sobolevToL2 (by norm_num : (0:ℝ)≤1) a))) n ∧
            (S a).val n=sourceExactEtaSineFourierError (by norm_num) (by norm_num)
              (sourcePhase (hillMiuraDiagonal (WeightedCoeff.sobolevToL2 (by norm_num : (0:ℝ)≤1) a))) n := by
  let J := hillMiuraH1DirichletPair
  have hreal : IsRealType (CoeffPair.toMax 2 (higherSobolevSourceInclusion 1 (J a0))) := by
    rw [hillMiuraH1DirichletPair_decode]
    exact isRealType_sourcePhase _ (isRealType_hillMiuraDiagonal ⟨_,(periodOneL2Conjugation_fixed_iff _).mp hr⟩)
  let φ : realTypeHigherSobolevSourceLocus 1 := ⟨J a0,hreal⟩
  obtain ⟨V,hV,hφV,CM,hCM,hMa,hM⟩ := exists_local_sourceExactEtaMidpointFourierRemainder_analytic 1 le_rfl φ
  obtain ⟨W,hW,hφW,CS,hCS,hSa,hS⟩ := exists_local_sourceExactEtaSineFourierRemainder_analytic 1 le_rfl φ
  let Q : WeightedCoeff (Weight.sobolev (((1:ℕ):ℝ)+1)) 2 →L[ℂ] WeightedCoeff (Weight.sobolev 2) 2 := WeightedCoeff.sobolevInclusion (by norm_num : (2:ℝ)≤((1:ℕ):ℝ)+1)
  let M := fun a => Q (sourceExactEtaMidpointFourierRemainder 1 (J a))
  let S := fun a => Q (sourceExactEtaSineFourierRemainder 1 (J a))
  let U := J ⁻¹' (V∩W)
  refine ⟨U,(hV.inter hW).preimage J.continuous,⟨hφV,hφW⟩,CM,CS,M,S,hCM,hCS,?_,?_,?_⟩
  · intro a ha
    exact (Q.analyticAt _).comp ((hMa (J a) ha.1).comp (J.analyticAt a))
  · intro a ha
    exact (Q.analyticAt _).comp ((hSa (J a) ha.2).comp (J.analyticAt a))
  · intro a ha
    refine ⟨(WeightedCoeff.norm_sobolevInclusion_le _ _).trans (hM (J a) ha.1).1,
      (WeightedCoeff.norm_sobolevInclusion_le _ _).trans (hS (J a) ha.2).1,?_⟩
    intro n
    change (Q (sourceExactEtaMidpointFourierRemainder 1 (J a))).val n=_ ∧
      (Q (sourceExactEtaSineFourierRemainder 1 (J a))).val n=_
    rw [WeightedCoeff.sobolevInclusion_apply,WeightedCoeff.sobolevInclusion_apply,
      (hM (J a) ha.1).2 n,(hS (J a) ha.2).2 n,hillMiuraH1DirichletPair_decode]
    exact ⟨rfl,rfl⟩

end NLS.KdV
