import NLS.ZakharovShabat.PeriodicEndpointLabeling

/-! # Two original roots in a refined disc give its full endpoint pair when a collision has multiplicity at least two. -/

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

theorem PeriodicEndpointPair.of_candidates
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {φ : PairSpace p} {n : ℤ} {a b x y : ℂ}
    (h : PeriodicEndpointPair hp φ n a b)
    (hx : x ∈ refinedResonantDisk n) (hy : y ∈ refinedResonantDisk n)
    (hsx : x ∈ periodicSpectrum hp φ) (hsy : y ∈ periodicSpectrum hp φ)
    (hdouble : x = y → 2 ≤ periodicAlgebraicMultiplicity hp φ x) :
    PeriodicEndpointPair hp φ n x y := by
  classical
  have hax := (h.spectrum_iff x (refinedResonantDisk_subset_strip n hx)).mp hsx
  have hay := (h.spectrum_iff y (refinedResonantDisk_subset_strip n hy)).mp hsy
  rcases hax with hax | hax <;> rcases hay with hay | hay
  all_goals subst x; subst y
  · have hm := h.multiplicity_eq_count a (refinedResonantDisk_subset_strip n h.left_mem)
    have htwo := hdouble rfl
    have he : b = a := by
      by_contra hb
      have hc : ({a,b} : Multiset ℂ).count a = 1 := by simp [Ne.symm hb]
      omega
    simpa only [he] using h
  · exact h
  · exact h.swap
  · have hm := h.multiplicity_eq_count b (refinedResonantDisk_subset_strip n h.right_mem)
    have htwo := hdouble rfl
    have he : a = b := by
      by_contra ha
      have hc : ({a,b} : Multiset ℂ).count b = 1 := by simp [Ne.symm ha]
      omega
    simpa only [he] using h

end NLS.ZakharovShabat
