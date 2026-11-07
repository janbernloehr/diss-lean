import NLS.KdV.HillCanonicalOffIndexAnalyticDomain

/-! The intrinsic ACTUAL infinite off-index correction is analytic
in the full native Banach source variable on ONE common OPEN CONNECTED
complex neighborhood of the ENTIRE real form, BEFORE ALL n. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV

theorem localUniformAnalyticApproximation_hillHminusOffIndexAbelianCorrection (n : ℕ+) :
    HasLocalUniformAnalyticApproximationOn (hillHminusOffIndexAbelianPartialSum n)
      (hillHminusOffIndexAbelianCorrection n) hillHminusOffIndexAnalyticDomain := by
  apply HasLocalUniformAnalyticApproximationOn.of_open_local_uniform isOpen_hillHminusOffIndexAnalyticDomain
    (fun N => (analyticOnNhd_hillHminusOffIndexAbelianPartialSum n N).mono hillHminusOffIndexAnalyticDomain_subset_physical)
  intro q hq
  obtain ⟨U,hU,hqU,_,hconv⟩ := exists_locally_uniform_hillHminusOffIndexAbelianCorrection q hq
  exact ⟨U,hU,hqU,hconv n⟩

theorem analyticOnNhd_hillHminusOffIndexAbelianCorrection (n : ℕ+) :
    AnalyticOnNhd ℂ (hillHminusOffIndexAbelianCorrection n) hillHminusOffIndexAnalyticDomain :=
  analyticOnNhd_of_complexSmoothOn _ isOpen_hillHminusOffIndexAnalyticDomain
    (localUniformAnalyticApproximation_hillHminusOffIndexAbelianCorrection n).contDiffOn

theorem exists_uniform_fderiv_hillHminusOffIndexAbelianCorrection (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ hillHminusOffIndexAnalyticDomain) :
    ∃ r : ℝ, 0 < r ∧ ball q r ⊆ hillHminusOffIndexAnalyticDomain ∧
      TendstoUniformlyOn (fun N => fderiv ℂ (hillHminusOffIndexAbelianPartialSum n N))
        (fderiv ℂ (hillHminusOffIndexAbelianCorrection n)) atTop (ball q r) :=
  (localUniformAnalyticApproximation_hillHminusOffIndexAbelianCorrection n).uniform_fderiv q hq

end NLS.KdV
