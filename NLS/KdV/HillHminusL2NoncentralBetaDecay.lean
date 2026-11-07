import NLS.KdV.HillMiuraH1AbsoluteBetaDecay
import NLS.ComplexAnalysis.AnalyticUniformPullback
import NLS.KdV.HillHminusRetainedMiuraEtaChart
import NLS.KdV.HillHminusNativeSourceFactors

/-! Inverse-index decay of the ACTUAL noncentral coordinate beta factor
on one ORIGINAL complex L2 neighborhood. The original roots, actual
Miura lift and literal central-term subtraction are retained. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV.HillHminusPsiChart

theorem sourceNoncentralBeta_bound_of_absolute (P : HillHminusPsiChart)
    (a : PeriodOneHminusOne) (n : ℕ+) (K : ℝ)
    (hs : Summable (fun m : ℤ => ‖sourceAngularBetaSeriesTerm (by norm_num) (by norm_num)
      ((n:ℕ):ℤ) P.family.roots (P.dirichletSource a) m‖))
    (hb : (1+(n:ℝ))*(∑' m : ℤ, ‖sourceAngularBetaSeriesTerm (by norm_num) (by norm_num)
      ((n:ℕ):ℤ) P.family.roots (P.dirichletSource a) m‖)≤K) :
    (1+(n:ℝ))*‖P.sourceNoncentralBeta n a‖≤2*K := by
  have hfull : ‖P.sourceBetaCorrection (n:ℕ) a‖≤
      ∑' m : ℤ, ‖sourceAngularBetaSeriesTerm (by norm_num) (by norm_num)
        ((n:ℕ):ℤ) P.family.roots (P.dirichletSource a) m‖ := norm_tsum_le_tsum_norm hs
  have hzero := hs.le_tsum 0 (fun _ _ => norm_nonneg _)
  have hn : (0:ℤ)≠((n:ℕ):ℤ) := by have := n.pos; omega
  have hz : sourceAngularBetaSeriesTerm (by norm_num) (by norm_num) ((n:ℕ):ℤ)
      P.family.roots (P.dirichletSource a) 0=
      sourceAngularBeta (by norm_num) (by norm_num) ((n:ℕ):ℤ) 0
        P.family.roots (P.dirichletSource a) := by
    rw [sourceAngularBetaSeriesTerm,if_neg hn]
  rw [hz] at hzero
  have hsub := norm_sub_le (P.sourceBetaCorrection (n:ℕ) a)
    (sourceAngularBeta (by norm_num) (by norm_num) ((n:ℕ):ℤ) 0 P.family.roots (P.dirichletSource a))
  have hmul := mul_le_mul_of_nonneg_left (hsub.trans (add_le_add hfull hzero))
    (by positivity : (0:ℝ)≤1+(n:ℝ))
  dsimp only [sourceNoncentralBeta]
  calc
    _ ≤ _ := hmul
    _ = 2*((1+(n:ℝ))*(∑' m : ℤ, ‖sourceAngularBetaSeriesTerm (by norm_num) (by norm_num)
        ((n:ℕ):ℤ) P.family.roots (P.dirichletSource a) m‖)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ)≤2)


theorem exists_native_l2_noncentralBeta_decay (P : HillHminusPsiChart)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num)
      P.family.originalDomain P.family.domain P.family.roots)
    (hstrong : HasAllNativeMiuraGerms P)
    (q : WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2)
    (hq : periodOneSobolevImageInclusion 1 (by norm_num) q∈P.sourceBetaDomain)
    (hr : periodOneL2Conjugation (P.miura.lift (periodOneSobolevImageInclusion 1 (by norm_num) q))=
      P.miura.lift (periodOneSobolevImageInclusion 1 (by norm_num) q)) :
    ∃ U : Set (WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2), IsOpen U ∧ q∈U ∧
      (∀ p∈U, periodOneSobolevImageInclusion 1 (by norm_num) p∈P.sourceBetaDomain) ∧
      ∃ K : ℝ, 0≤K ∧ ∀ p∈U, ∀ n : ℕ+,
        (1+(n:ℝ))*‖P.sourceNoncentralBeta n (periodOneSobolevImageInclusion 1 (by norm_num) p)‖≤K := by
  obtain ⟨V,hV,hqV,g,hga,hg⟩ := hstrong 1 (by norm_num) q hq.1.1
  have hrg : periodOneL2Conjugation (WeightedCoeff.sobolevToL2 (by norm_num : (0:ℝ)≤1) (g q))=
      WeightedCoeff.sobolevToL2 (by norm_num : (0:ℝ)≤1) (g q) := by
    rw [(hg q hqV).2]
    exact hr
  obtain ⟨B,hB,hgqB,K,hK,habs⟩ := exists_hillMiuraH1_absolute_beta_decay H (g q) hrg
  let L := periodOneSobolevImageInclusion 1 (by norm_num : (0:ℝ)≤1)
  let S := fun a : WeightedCoeff (Weight.sobolev 1) 2 => sourcePhase (hillMiuraDiagonal
    (WeightedCoeff.sobolevToL2 (by norm_num : (0:ℝ)≤1) a))
  let Bound := fun χ : CoeffPair 2 => ∀ n : ℤ,
    Summable (fun m : ℤ => ‖sourceAngularBetaSeriesTerm (by norm_num) (by norm_num) n P.family.roots χ m‖) ∧
    (1+|(n:ℝ)|)*(∑' m : ℤ, ‖sourceAngularBetaSeriesTerm (by norm_num) (by norm_num) n P.family.roots χ m‖)≤K
  have hcomm (p : WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2) (hp : p∈V) :
      S (g p)=P.dirichletSource (L p) := by
    dsimp only [S]
    rw [(hg p hp).2]
    rfl
  obtain ⟨U,hU,hqU,_hUV,hdata⟩ := NLS.ComplexAnalysis.exists_uniform_analytic_pullback
    L P.sourceBetaDomain P.sourceBetaDomain_open q hq V hV hqV g hga B hB hgqB
    P.dirichletSource S hcomm Bound habs
  refine ⟨U,hU,hqU,(fun p hp => (hdata p hp).1),2*K,by positivity,?_⟩
  intro p hp n
  obtain ⟨hs,hb⟩ := (hdata p hp).2 ((n:ℕ):ℤ)
  apply P.sourceNoncentralBeta_bound_of_absolute (L p) n K hs
  simpa only [Int.cast_natCast,abs_of_pos (by positivity : (0:ℝ)<n)] using hb

end NLS.KdV.HillHminusPsiChart
