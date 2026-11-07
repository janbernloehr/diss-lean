import NLS.Articles.KdVPseudomeasures.OriginalHillRealAbelianPhases
import NLS.KdV.HillCanonicalOffIndexAbsoluteSum

/-! Absolute convergence of the infinite ACTUAL off-index correction
on a common complex source neighborhood before ALL n. The sharper
source estimate, analytic sum and uniform all-n bounds are separate. -/
noncomputable section
open Set Complex NLS.KdV
open scoped Classical
namespace NLS.Articles.KdVPseudomeasures

theorem original_Hill_offIndex_absolute_sum_common_domain :
    IsOpen hillHminusOffIndexSummabilityDomain ∧ IsConnected hillHminusOffIndexSummabilityDomain ∧
      hillHminusOffIndexSummabilityDomain ⊆ hillHminusPhysicalAbelianDomain ∧
      (∀ q : OriginalHminusOnePotential, originalPeriodOneCoefficients q ∈ hillHminusOffIndexSummabilityDomain) ∧
      ∀ n : ℕ+, ∀ q ∈ hillHminusOffIndexSummabilityDomain,
        Summable (fun m => ‖hillHminusOffIndexAbelianTerm n q m‖) :=
  ⟨isOpen_hillHminusOffIndexSummabilityDomain,isConnected_hillHminusOffIndexSummabilityDomain,
    hillHminusOffIndexSummabilityDomain_subset,
    (fun q => real_mem_hillHminusOffIndexSummabilityDomain _ (originalPeriodOneCoefficients_real q)),
    summable_norm_hillHminusOffIndexAbelianTerm⟩

theorem original_Hill_offIndex_infinite_correction_hasSum (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ hillHminusOffIndexSummabilityDomain) :
    HasSum (hillHminusOffIndexAbelianTerm n q) (hillHminusOffIndexAbelianCorrection n q) :=
  hillHminusOffIndexAbelianCorrection_hasSum n q hq

theorem original_Hill_offIndex_infinite_correction_real (n : ℕ+) (q : OriginalHminusOnePotential) :
    (hillHminusOffIndexAbelianCorrection n (originalPeriodOneCoefficients q)).im = 0 :=
  hillHminusOffIndexAbelianCorrection_im_eq_zero_of_real n _ (originalPeriodOneCoefficients_real q)

end NLS.Articles.KdVPseudomeasures
