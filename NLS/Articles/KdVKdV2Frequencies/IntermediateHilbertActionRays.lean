import NLS.Articles.KdVKdV2Frequencies.NormalizedSobolevWeakActions
import NLS.Articles.KdVConvexity.HilbertActionUnreindex

/-! Exact ORIGINAL weak-action identification on every positive
coordinate ray, for every intermediate order. No full Hilbert-to-weighted
inclusion is assumed or needed for these finite coordinate directions. -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV
open NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

theorem nonnegative_real_single_ray (p : ℝ≥0∞) [Fact (1≤p)]
    (j : ℤ) (t : ℝ) (ht : 0≤t) : (t : ℂ) • lp.single p j 1∈Coeff.nonnegativeLocus p := by
  intro i
  change ((t : ℂ)*(lp.single (E := fun _ : ℤ => ℂ) p j 1) i).im=0 ∧
    0≤((t : ℂ)*(lp.single (E := fun _ : ℤ => ℂ) p j 1) i).re
  by_cases hij : i=j <;> simp [lp.single_apply,hij,ht]

theorem intermediate_hilbert_single_ray_nonnegative
    (α : ℝ) (j : ℤ) (t : ℝ) (ht : 0≤t) :
    (((t : ℂ)/(Weight.sobolev α (actionIndexEquiv j : ℤ) : ℂ)) • lp.single 2 j 1)∈Coeff.nonnegativeLocus 2 := by
  have h := nonnegative_real_single_ray 2 j (t/Weight.sobolev α (actionIndexEquiv j : ℤ))
    (div_nonneg ht ((Weight.sobolev α).positive _).le)
  simpa only [Complex.ofReal_div] using h

theorem normalized_weak_single_ray_hilbert (α : ℝ) (hα : -1≤α) (j : ℤ) (z : ℂ) :
    normalizedSobolevWeakActionInclusion α hα (z • lp.single 1 j 1)=
      weakActionEnumeration (hilbertWeakActions (actionUnreindex
        ((z/(Weight.sobolev α (actionIndexEquiv j : ℤ) : ℂ)) • lp.single 2 j 1))) := by
  ext k
  rw [normalizedSobolevWeakActionInclusion_apply,weakActionEnumeration_hilbert]
  change (baseActionWeight k : ℂ)*((z • lp.single (E := fun _ : ℤ => ℂ) 1 j 1) k/(Weight.sobolev α (actionIndexEquiv k : ℤ) : ℂ))=
    (baseActionWeight k : ℂ)*(baseActionInclusion (actionUnreindex
      ((z/(Weight.sobolev α (actionIndexEquiv j : ℤ) : ℂ)) • lp.single 2 j 1))).val k
  rw [baseActionInclusion_apply,actionUnreindex_apply,Equiv.symm_apply_apply]
  change (baseActionWeight k : ℂ)*(z*(lp.single (E := fun _ : ℤ => ℂ) 1 j 1) k/
      (Weight.sobolev α (actionIndexEquiv k : ℤ) : ℂ))=
    (baseActionWeight k : ℂ)*((z/(Weight.sobolev α (actionIndexEquiv j : ℤ) : ℂ))*
      (lp.single (E := fun _ : ℤ => ℂ) 2 j 1) k)
  by_cases hkj : k=j <;> simp [lp.single_apply,hkj]

end NLS.Articles.KdVKdV2Frequencies
