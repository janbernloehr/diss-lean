import NLS.KdV.HillCanonicalAbelianActionVariation
import NLS.KdV.HillCanonicalOffIndexAnalyticCorrection

/-! Full cotangents and Gardner variations of the actual infinite
off-index correction are limits of the literal finite signed cutoffs.
This uses the proved locally uniform Banach analytic approximation;
termwise source differentiation is not assumed. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.LpSequence
open scoped ENNReal
namespace NLS.KdV

theorem analyticOnNhd_hillHminusOffIndexSignedAbelianTerm (n : ℕ+) (j : ℤ) :
    AnalyticOnNhd ℂ (fun q => positiveScalarExtension (hillHminusOffIndexAbelianTerm n q) j)
      hillHminusPhysicalAbelianDomain := by
  by_cases hj : j ∈ range positiveEmbedding
  · obtain ⟨m,rfl⟩ := hj
    change AnalyticOnNhd ℂ (fun q => positiveScalarExtension (hillHminusOffIndexAbelianTerm n q) ((m:ℕ):ℤ))
      hillHminusPhysicalAbelianDomain
    simpa only [positiveScalarExtension_apply] using analyticOnNhd_hillHminusOffIndexAbelianTerm n m
  · have he (a : PeriodOneHminusOne) :
        positiveScalarExtension (hillHminusOffIndexAbelianTerm n a) j = 0 :=
      positiveScalarExtension_zero_of_not_mem_range _ j hj
    simp only [he]
    exact analyticOnNhd_const

theorem fderiv_hillHminusOffIndexAbelianPartialSum_eq_sum
    (n : ℕ+) (N : ℕ) (q : PeriodOneHminusOne) (hq : q ∈ hillHminusPhysicalAbelianDomain) :
    fderiv ℂ (hillHminusOffIndexAbelianPartialSum n N) q =
      ∑ j ∈ Finset.Icc (-(N:ℤ)) N,
        fderiv ℂ (fun a => positiveScalarExtension (hillHminusOffIndexAbelianTerm n a) j) q :=
  fderiv_fun_sum (fun j _ => (analyticOnNhd_hillHminusOffIndexSignedAbelianTerm n j q hq).differentiableAt)

theorem tendsto_hillHminusOffIndexAbelian_cotangent_sums
    (n : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ hillHminusOffIndexAnalyticDomain) :
    Tendsto (fun N : ℕ => ∑ j ∈ Finset.Icc (-(N:ℤ)) N,
      fderiv ℂ (fun a => positiveScalarExtension (hillHminusOffIndexAbelianTerm n a) j) q) atTop
        (𝓝 (fderiv ℂ (hillHminusOffIndexAbelianCorrection n) q)) := by
  obtain ⟨r,hr,_,hconv⟩ := exists_uniform_fderiv_hillHminusOffIndexAbelianCorrection n q hq
  exact (hconv.tendsto_at (mem_ball_self hr)).congr'
    (Eventually.of_forall (fun N => fderiv_hillHminusOffIndexAbelianPartialSum_eq_sum n N q
      (hillHminusOffIndexAnalyticDomain_subset_physical hq)))

theorem tendsto_hillHminusOffIndexAbelian_variation_sums
    (n : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ hillHminusOffIndexAnalyticDomain)
    (h : PeriodOneHminusOne) :
    Tendsto (fun N : ℕ => ∑ j ∈ Finset.Icc (-(N:ℤ)) N,
      (fderiv ℂ (fun a => positiveScalarExtension (hillHminusOffIndexAbelianTerm n a) j) q) h) atTop
        (𝓝 ((fderiv ℂ (hillHminusOffIndexAbelianCorrection n) q) h)) := by
  have hc : Continuous (fun L : PeriodOneHminusOne →L[ℂ] ℂ => L h) := by fun_prop
  simpa only [Function.comp_def,sum_apply] using
    hc.continuousAt.tendsto.comp (tendsto_hillHminusOffIndexAbelian_cotangent_sums n q hq)

theorem tendsto_hillHminusOffIndexAbelian_Gardner_sums
    (n : ℕ+) (G : PeriodOneHminusOne → ℂ) (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusOffIndexAnalyticDomain) :
    Tendsto (fun N : ℕ => ∑ j ∈ Finset.Icc (-(N:ℤ)) N,
      NLS.Poisson.hminusGardnerBracket
        (fun a => positiveScalarExtension (hillHminusOffIndexAbelianTerm n a) j) G q) atTop
        (𝓝 (NLS.Poisson.hminusGardnerBracket (hillHminusOffIndexAbelianCorrection n) G q)) := by
  simpa only [NLS.Poisson.fderiv_apply_gardnerHamiltonianVector] using
    tendsto_hillHminusOffIndexAbelian_variation_sums n q hq (NLS.Poisson.gardnerHamiltonianVector G q)

end NLS.KdV
