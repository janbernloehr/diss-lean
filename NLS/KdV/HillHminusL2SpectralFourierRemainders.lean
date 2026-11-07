import NLS.KdV.HillMiuraH1SpectralFourierRemainders
import NLS.KdV.HillHminusRetainedMiuraEtaChart
import NLS.ComplexAnalysis.BoundedAnalyticPullback

/-! The literal spectral midpoint and sine Fourier errors of the SAME
retained Miura lift have bounded analytic h2 realizations on ONE ORIGINAL
complex L2 neighborhood, including ALL signed labels and closed gaps. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV.HillHminusPsiChart

theorem exists_native_l2_spectral_fourier_remainders (P : HillHminusPsiChart)
    (hstrong : HasAllNativeMiuraGerms P)
    (q : WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2)
    (hq : periodOneSobolevImageInclusion 1 (by norm_num) q∈P.sourceBetaDomain)
    (hr : periodOneL2Conjugation (P.miura.lift (periodOneSobolevImageInclusion 1 (by norm_num) q))=
      P.miura.lift (periodOneSobolevImageInclusion 1 (by norm_num) q)) :
    ∃ U : Set (WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2),IsOpen U ∧ q∈U ∧
      ∃ C : ℝ,∃ M S : WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2 → WeightedCoeff (Weight.sobolev 2) 2,
        0≤C ∧ AnalyticOnNhd ℂ M U ∧ AnalyticOnNhd ℂ S U ∧ ∀ p∈U,
          periodOneSobolevImageInclusion 1 (by norm_num) p∈P.sourceBetaDomain ∧ ‖M p‖≤C ∧ ‖S p‖≤C ∧
          ∀ n : ℤ,(M p).val n=sourceExactEtaMidpointFourierError (by norm_num) (by norm_num) (P.dirichletSource (periodOneSobolevImageInclusion 1 (by norm_num) p)) n ∧
            (S p).val n=sourceExactEtaSineFourierError (by norm_num) (by norm_num) (P.dirichletSource (periodOneSobolevImageInclusion 1 (by norm_num) p)) n := by
  let L := periodOneSobolevImageInclusion 1 (by norm_num : (0:ℝ)≤1)
  obtain ⟨V,hV,hqV,g,hga,hg⟩ := hstrong 1 (by norm_num) q hq.1.1
  have hrg : periodOneL2Conjugation (WeightedCoeff.sobolevToL2 (by norm_num : (0:ℝ)≤1) (g q))=
      WeightedCoeff.sobolevToL2 (by norm_num : (0:ℝ)≤1) (g q) := by
    rw [(hg q hqV).2]
    exact hr
  obtain ⟨B,hB,hgqB,CM,CS,M,S,hCM,hCS,hMa,hSa,hd⟩ := exists_hillMiuraH1_spectral_fourier_remainders (g q) hrg
  let R := fun a => (M a,S a)
  have hRa : AnalyticOnNhd ℂ R B := hMa.prod hSa
  have hRb (a) (ha : a∈B) : ‖R a‖≤max CM CS := by
    rw [Prod.norm_def]
    exact max_le_max (hd a ha).1 (hd a ha).2.1
  let obs := fun x : WeightedCoeff (Weight.sobolev 2) 2 × WeightedCoeff (Weight.sobolev 2) 2 =>
    ((fun n : ℤ => x.1.val n),(fun n : ℤ => x.2.val n))
  let T := fun a : PeriodOneHminusOne =>
    ((fun n : ℤ => sourceExactEtaMidpointFourierError (by norm_num) (by norm_num) (P.dirichletSource a) n),
      (fun n : ℤ => sourceExactEtaSineFourierError (by norm_num) (by norm_num) (P.dirichletSource a) n))
  have he (p) (hp : p∈V) (hgp : g p∈B) : obs (R (g p))=T (L p) := by
    apply Prod.ext
    · funext n
      have h := ((hd (g p) hgp).2.2 n).1
      rw [(hg p hp).2] at h
      exact h
    · funext n
      have h := ((hd (g p) hgp).2.2 n).2
      rw [(hg p hp).2] at h
      exact h
  obtain ⟨U,hU,hqU,_hUV,F,hFa,hF⟩ := NLS.ComplexAnalysis.exists_bounded_analytic_pullback L
    P.sourceBetaDomain P.sourceBetaDomain_open q hq V hV hqV g hga B hB hgqB R hRa (max CM CS) hRb obs T he
  refine ⟨U,hU,hqU,max CM CS,(fun p => (F p).1),(fun p => (F p).2),le_trans hCM (le_max_left _ _),
    (fun p hp => analyticAt_fst.comp (hFa p hp)),(fun p hp => analyticAt_snd.comp (hFa p hp)),?_⟩
  intro p hp
  refine ⟨(hF p hp).1,(norm_fst_le (F p)).trans (hF p hp).2.1,(norm_snd_le (F p)).trans (hF p hp).2.1,?_⟩
  intro n
  exact ⟨congrArg (fun z => z.1 n) (hF p hp).2.2,congrArg (fun z => z.2 n) (hF p hp).2.2⟩

end NLS.KdV.HillHminusPsiChart
