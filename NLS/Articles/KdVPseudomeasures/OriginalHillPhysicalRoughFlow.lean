import NLS.Articles.KdVPseudomeasures.OriginalHillRoughCanonicalTrajectories

/-! The actual canonical rough KdV flow on the original physical
H-minus-one distributions, with unchanged Fourier normalization. -/
noncomputable section
open Set NLS.KdV
namespace NLS.Articles.KdVPseudomeasures

theorem continuous_originalHillPotentialOfRealSource : Continuous originalHillPotentialOfRealSource :=
  (periodOneOriginal.continuous.comp hillRealMeanZeroInclusion.continuous).subtype_mk _

def hillOriginalCanonicalKdVFlow (q : OriginalHminusOnePotential) (time : ℝ) : OriginalHminusOnePotential :=
  originalHillPotentialOfRealSource (hillRoughCanonicalKdVFlow (originalHillRealMeanZeroSource q) time)

theorem hillOriginalCanonicalKdVFlow_zero (q : OriginalHminusOnePotential) :
    hillOriginalCanonicalKdVFlow q 0 = q := by
  rw [hillOriginalCanonicalKdVFlow, hillRoughCanonicalKdVFlow_zero,
    originalHillPotentialOfRealSource_ofOriginal]

theorem hillOriginalCanonicalKdVFlow_add (q : OriginalHminusOnePotential) (t s : ℝ) :
    hillOriginalCanonicalKdVFlow (hillOriginalCanonicalKdVFlow q s) t =
      hillOriginalCanonicalKdVFlow q (t + s) := by
  simp only [hillOriginalCanonicalKdVFlow, originalHillRealMeanZeroSource_ofRealSource,
    hillRoughCanonicalKdVFlow_add]

theorem hillOriginalCanonicalKdVFlow_isospectral (q : OriginalHminusOnePotential) (t : ℝ) :
    hillOriginalCanonicalKdVFlow q t ∈ originalIsospectralSet q := by
  have h := hillRoughCanonicalKdVFlow_isospectral (originalHillRealMeanZeroSource q) t
  rw [originalHillPotentialOfRealSource_ofOriginal] at h
  exact h

theorem continuous_hillOriginalCanonicalKdVFlow :
    Continuous (fun p : ℝ × OriginalHminusOnePotential => hillOriginalCanonicalKdVFlow p.2 p.1) := by
  have hi : Continuous (fun p : ℝ × OriginalHminusOnePotential =>
      (p.1, originalHillRealMeanZeroSource p.2)) :=
    continuous_fst.prodMk (continuous_originalHillRealMeanZeroSource.comp continuous_snd)
  have hc := continuous_hillRoughCanonicalKdVFlow.comp hi
  have h := continuous_originalHillPotentialOfRealSource.comp hc
  simpa only [Function.comp_def, hillOriginalCanonicalKdVFlow] using! h

theorem continuous_hillOriginalCanonicalKdVFlow_val_time (q : OriginalHminusOnePotential) :
    Continuous (fun t : ℝ => (hillOriginalCanonicalKdVFlow q t).val) := by
  have hi : Continuous (fun t : ℝ => (t, q)) := continuous_id.prodMk continuous_const
  have h := continuous_subtype_val.comp (continuous_hillOriginalCanonicalKdVFlow.comp hi)
  simpa only [Function.comp_def] using! h

end NLS.Articles.KdVPseudomeasures
