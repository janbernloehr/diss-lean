import NLS.KdV.HillMiuraH1OwnEtaDecay
import NLS.KdV.HillHminusOwnEtaAnalytic
import NLS.KdV.HillHminusRetainedMiuraEtaChart
import NLS.ComplexAnalysis.AnalyticUniformPullback
import NLS.ComplexAnalysis.AnalyticFamilyBoundPullback

/-! The literal own-index eta remainder of the SAME retained Hill chart
is analytic and has inverse-index decay on ONE ORIGINAL complex L2
neighborhood before EVERY signed index. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV.HillHminusPsiChart

theorem exists_native_l2_own_eta_bound (P : HillHminusPsiChart)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) P.family.originalDomain P.family.domain P.family.roots)
    (hstrong : HasAllNativeMiuraGerms P)
    (q : WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2)
    (hq : periodOneSobolevImageInclusion 1 (by norm_num) q∈P.sourceBetaDomain)
    (hr : periodOneL2Conjugation (P.miura.lift (periodOneSobolevImageInclusion 1 (by norm_num) q))=
      P.miura.lift (periodOneSobolevImageInclusion 1 (by norm_num) q)) :
    ∃ U : Set (WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2),IsOpen U ∧ q∈U ∧
      (∀ p∈U,periodOneSobolevImageInclusion 1 (by norm_num) p∈P.sourceBetaDomain) ∧
      ∃ K : ℝ,0≤K ∧ ∀ p∈U,∀ n : ℤ,(1+|(n:ℝ)|)*‖P.sourceOwnEtaRemainder n
        (periodOneSobolevImageInclusion 1 (by norm_num) p)‖≤K := by
  let L := periodOneSobolevImageInclusion 1 (by norm_num : (0:ℝ)≤1)
  obtain ⟨V,hV,hqV,g,hga,hg⟩ := hstrong 1 (by norm_num) q hq.1.1
  have hrg : periodOneL2Conjugation (WeightedCoeff.sobolevToL2 (by norm_num : (0:ℝ)≤1) (g q))=
      WeightedCoeff.sobolevToL2 (by norm_num : (0:ℝ)≤1) (g q) := by
    rw [(hg q hqV).2]
    exact hr
  obtain ⟨B,hB,hgqB,_hBa,K,hK,hb⟩ := exists_hillMiuraH1_own_eta_decay H (g q) hrg
  let S := fun a : WeightedCoeff (Weight.sobolev 1) 2 =>
    sourcePhase (hillMiuraDiagonal (WeightedCoeff.sobolevToL2 (by norm_num : (0:ℝ)≤1) a))
  let Bound := fun χ : CoeffPair 2 => ∀ n : ℤ,(1+|(n:ℝ)|)*
    ‖sourceAngularEtaRemainder (by norm_num) (by norm_num) n P.family.roots χ‖≤K
  have hcomm (p) (hp : p∈V) : S (g p)=P.dirichletSource (L p) := by
    dsimp only [S]
    rw [(hg p hp).2]
    rfl
  obtain ⟨A,hA,hqA,_hAV,hd⟩ := NLS.ComplexAnalysis.exists_uniform_analytic_pullback
    L P.sourceBetaDomain P.sourceBetaDomain_open q hq V hV hqV g hga B hB hgqB
    P.dirichletSource S hcomm Bound hb
  exact ⟨A,hA,hqA,(fun p hp => (hd p hp).1),K,hK,fun p hp n => (hd p hp).2 n⟩

theorem exists_native_l2_own_eta_decay (P : HillHminusPsiChart)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) P.family.originalDomain P.family.domain P.family.roots)
    (hstrong : HasAllNativeMiuraGerms P)
    (q : WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2)
    (hq : periodOneSobolevImageInclusion 1 (by norm_num) q∈P.sourceBetaDomain)
    (hr : periodOneL2Conjugation (P.miura.lift (periodOneSobolevImageInclusion 1 (by norm_num) q))=
      P.miura.lift (periodOneSobolevImageInclusion 1 (by norm_num) q)) :
    ∃ U : Set (WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2),IsOpen U ∧ q∈U ∧
      (∀ p∈U,periodOneSobolevImageInclusion 1 (by norm_num) p∈P.sourceBetaDomain) ∧
      (∀ n : ℤ,AnalyticOnNhd ℂ (fun p => P.sourceOwnEtaRemainder n
        (periodOneSobolevImageInclusion 1 (by norm_num) p)) U) ∧
      ∃ K : ℝ,0≤K ∧ ∀ p∈U,∀ n : ℤ,(1+|(n:ℝ)|)*‖P.sourceOwnEtaRemainder n
        (periodOneSobolevImageInclusion 1 (by norm_num) p)‖≤K := by
  let L := periodOneSobolevImageInclusion 1 (by norm_num : (0:ℝ)≤1)
  obtain ⟨V,hV,hqV,hd,K,hK,hb⟩ := P.exists_native_l2_own_eta_bound H hstrong q hq hr
  obtain ⟨T,hT,hqT,_hTP,hTa⟩ := P.exists_local_sourceOwnEtaRemainder_analytic H (L q) hq hr
  obtain ⟨U,hU,hqU,hUD,hRa,hB⟩ := NLS.ComplexAnalysis.exists_analytic_family_bound_pullback L
    P.sourceBetaDomain V hV T hT q hqV hqT P.sourceOwnEtaRemainder hTa
    (fun a => ∀ n : ℤ,(1+|(n:ℝ)|)*‖P.sourceOwnEtaRemainder n a‖≤K) hd hb
  exact ⟨U,hU,hqU,hUD,hRa,K,hK,hB⟩

end NLS.KdV.HillHminusPsiChart
