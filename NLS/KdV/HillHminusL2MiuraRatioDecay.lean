import NLS.KdV.HillMiuraH1CauchyRatioDecay
import NLS.KdV.HillHminusMiuraActionRatios
import NLS.KdV.HillHminusRetainedMiuraEtaChart
import NLS.ComplexAnalysis.AnalyticUniformPullback

/-! The ACTUAL retained Miura Cauchy action ratio has inverse-index
error from its free normalization on ONE ORIGINAL complex L2
neighborhood, before ALL sufficiently high positive labels. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV.HillHminusPsiChart

theorem exists_native_l2_miura_actionRatio_decay (P : HillHminusPsiChart)
    (hstrong : HasAllNativeMiuraGerms P) {W : Set (CoeffPair 2)}
    (C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W)
    (q : WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2)
    (hq : periodOneSobolevImageInclusion 1 (by norm_num) q∈P.sourceBetaDomain)
    (hr : periodOneL2Conjugation (P.miura.lift (periodOneSobolevImageInclusion 1 (by norm_num) q))=
      P.miura.lift (periodOneSobolevImageInclusion 1 (by norm_num) q))
    (hC : hillMiuraDiagonal (P.miura.lift (periodOneSobolevImageInclusion 1 (by norm_num) q))∈
      Metric.ball C.discs.source.val C.discs.sourceRadius) :
    ∃ U : Set (WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2), IsOpen U ∧ q∈U ∧
      (∀ p∈U, periodOneSobolevImageInclusion 1 (by norm_num) p∈P.sourceBetaDomain) ∧
      ∃ N : ℕ, ∃ K : ℝ, 0≤K ∧ ∀ p∈U,
        hillMiuraDiagonal (P.miura.lift (periodOneSobolevImageInclusion 1 (by norm_num) p))∈
          Metric.ball C.discs.source.val C.discs.sourceRadius ∧
        ∀ n : ℕ+, N≤(n:ℕ) →
          (1+(n:ℝ))*‖(2*((Real.pi:ℂ)*(n:ℕ)))*P.miuraActionRatio C n
            (periodOneSobolevImageInclusion 1 (by norm_num) p)-1‖≤K := by
  obtain ⟨V,hV,hqV,g,hga,hg⟩ := hstrong 1 (by norm_num) q hq.1.1
  have hrg : periodOneL2Conjugation (WeightedCoeff.sobolevToL2 (by norm_num : (0:ℝ)≤1) (g q))=
      WeightedCoeff.sobolevToL2 (by norm_num : (0:ℝ)≤1) (g q) := by
    rw [(hg q hqV).2]
    exact hr
  have hCg : hillMiuraDiagonal (WeightedCoeff.sobolevToL2 (by norm_num : (0:ℝ)≤1) (g q))∈
      Metric.ball C.discs.source.val C.discs.sourceRadius := by
    rw [(hg q hqV).2]
    exact hC
  obtain ⟨B,hB,hgqB,N,K,hK,hb⟩ := exists_hillMiuraH1_cauchy_energyRatio_decay C (g q) hrg hCg
  let L := periodOneSobolevImageInclusion 1 (by norm_num : (0:ℝ)≤1)
  let S := fun a : WeightedCoeff (Weight.sobolev 1) 2 =>
    hillMiuraDiagonal (WeightedCoeff.sobolevToL2 (by norm_num : (0:ℝ)≤1) a)
  let F := fun a : PeriodOneHminusOne => hillMiuraDiagonal (P.miura.lift a)
  let Bound := fun χ : CoeffPair 2 => χ∈Metric.ball C.discs.source.val C.discs.sourceRadius ∧
    ∀ n : ℕ+, N≤(n:ℕ) → (1+(n:ℝ))*‖(2*((Real.pi:ℂ)*(n:ℕ)))*
      C.normalizedEnergyActionRatio (n:ℕ) χ-1‖≤K
  have hcomm (p) (hp : p∈V) : S (g p)=F (L p) := by
    dsimp only [S,F]
    rw [(hg p hp).2]
  obtain ⟨U,hU,hqU,_hUV,hd⟩ := NLS.ComplexAnalysis.exists_uniform_analytic_pullback
    L P.sourceBetaDomain P.sourceBetaDomain_open q hq V hV hqV g hga B hB hgqB F S hcomm Bound hb
  exact ⟨U,hU,hqU,(fun p hp => (hd p hp).1),N,K,hK,fun p hp => (hd p hp).2⟩

end NLS.KdV.HillHminusPsiChart
