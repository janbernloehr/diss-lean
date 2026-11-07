import NLS.KdV.HillHminusL2MiuraRatioDecay
import NLS.ZakharovShabat.SourceCauchyEnergyRatioAnalytic

/-! Common complex analyticity and quantitative decay of the SAME
actual Miura action ratios in the ORIGINAL L2 topology. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV.HillHminusPsiChart

theorem exists_native_l2_analytic_miura_actionRatio_decay (P : HillHminusPsiChart)
    (hstrong : HasAllNativeMiuraGerms P) {W : Set (CoeffPair 2)}
    (C : SourceFullAbelianUniformCauchyFamily (by norm_num) (by norm_num) W)
    (q : WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2)
    (hq : periodOneSobolevImageInclusion 1 (by norm_num) q∈P.sourceBetaDomain)
    (hr : periodOneL2Conjugation (P.miura.lift (periodOneSobolevImageInclusion 1 (by norm_num) q))=
      P.miura.lift (periodOneSobolevImageInclusion 1 (by norm_num) q))
    (hC : hillMiuraDiagonal (P.miura.lift (periodOneSobolevImageInclusion 1 (by norm_num) q))∈
      Metric.ball C.discs.source.val C.discs.sourceRadius) :
    ∃ U : Set (WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2), IsOpen U ∧ q∈U ∧
      (∀ p∈U, periodOneSobolevImageInclusion 1 (by norm_num) p∈P.sourceBetaDomain) ∧
      ∃ N : ℕ, ∃ K : ℝ, 0≤K ∧ ∀ n : ℕ+, N≤(n:ℕ) →
        AnalyticOnNhd ℂ (fun p => P.miuraActionRatio C n (periodOneSobolevImageInclusion 1 (by norm_num) p)) U ∧
        ∀ p∈U, (1+(n:ℝ))*‖(2*((Real.pi:ℂ)*(n:ℕ)))*P.miuraActionRatio C n
          (periodOneSobolevImageInclusion 1 (by norm_num) p)-1‖≤K := by
  obtain ⟨V,hV,hqV,hVP,Nd,K,hK,hb⟩ := P.exists_native_l2_miura_actionRatio_decay hstrong C q hq hr hC
  let L := periodOneSobolevImageInclusion 1 (by norm_num : (0:ℝ)≤1)
  let F := fun p => hillMiuraDiagonal (P.miura.lift (L p))
  have hFa : AnalyticOnNhd ℂ F V := fun p hp =>
    (hillMiuraDiagonal.analyticAt _).comp ((P.miura.lift_analytic _ (hVP p hp).1.1).comp (L.analyticAt p))
  let φ : realTypeSourceSubmodule 2 := ⟨F q,isRealType_hillMiuraDiagonal ⟨_,(periodOneL2Conjugation_fixed_iff _).mp hr⟩⟩
  obtain ⟨Na,B,hB,hqB,_hBC,ha⟩ := C.exists_local_normalizedEnergyActionRatio_common_analytic φ hC
  let U := V∩F ⁻¹' B
  refine ⟨U,hFa.continuousOn.isOpen_inter_preimage hV hB,⟨hqV,hqB⟩,
    (fun p hp => hVP p hp.1),max Nd Na,K,hK,?_⟩
  intro n hn
  refine ⟨(fun p hp => (ha n ((le_max_right Nd Na).trans hn) (F p) hp.2).comp (hFa p hp.1)),?_⟩
  intro p hp
  exact (hb p hp.1).2 n ((le_max_left Nd Na).trans hn)

end NLS.KdV.HillHminusPsiChart
