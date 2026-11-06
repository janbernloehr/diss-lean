import NLS.KdV.HillMeanZeroNormingPerturbations
import NLS.KdV.HillEndpointSheetFacts
import NLS.KdV.HillClosedGapAbelianCorrections

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.KdV

/-- Every ORIGINAL L2 neighborhood of a mean-zero real potential contains
a mean-zero real potential with nonzero selected physical log norming.
The perturbation uses its ACTUAL nonzero Dirichlet Darboux derivative. -/
theorem exists_hillMeanZero_logNorming_ne_zero_in_open
    (q : RealPeriodOneHillPotential) (n : ℕ+) (hmean : q.val.val 0 = 0)
    (U : Set RealPeriodOneHillPotential) (hU : IsOpen U) (hqU : q ∈ U) :
    ∃ p ∈ U, p.val.val 0 = 0 ∧ hillDirichletLogMultiplier p.val p.property.1 p.property.2 n n.pos ≠ 0 := by
  classical
  by_contra hnone
  have hz (p : RealPeriodOneHillPotential) (hpU : p ∈ U) (hpmean : p.val.val 0 = 0) :
      hillDirichletLogMultiplier p.val p.property.1 p.property.2 n n.pos = 0 := by
    by_contra hp
    exact hnone ⟨p,hpU,hpmean,hp⟩
  have ht : Tendsto (hillRealDirichletPerturbation q n) (𝓝 0) (𝓝 q) := by
    simpa only [hillRealDirichletPerturbation_zero] using
      ((continuous_hillRealDirichletPerturbation q n).continuousAt (x := (0:ℝ))).tendsto
  have he : (fun t : ℝ => (hillDirichletLogMultiplier (hillRealDirichletPerturbation q n t).val
      (hillRealDirichletPerturbation q n t).property.1 (hillRealDirichletPerturbation q n t).property.2 n n.pos : ℂ))
      =ᶠ[𝓝 0] (fun _ => (0:ℂ)) := by
    filter_upwards [ht.eventually (hU.mem_nhds hqU)] with t htp
    rw [hz _ htp (hillRealDirichletPerturbation_mean_zero q n hmean t),ofReal_zero]
  have hc := (hasDerivAt_const (0:ℝ) (0:ℂ)).congr_of_eventuallyEq he
  have hd := (hasDerivAt_hillLogNorming_realDirichletPerturbation q n).unique hc
  norm_num at hd

/-- The two selected gaps can be made open simultaneously by arbitrarily
small ORIGINAL real mean-zero L2 perturbations. No infinite-gap or spectral
perturbation premise is assumed. -/
theorem exists_hillMeanZero_selectedOpen_in_open
    (q : RealPeriodOneHillPotential) (n m : ℕ+) (hmean : q.val.val 0 = 0)
    (U : Set RealPeriodOneHillPotential) (hU : IsOpen U) (hqU : q ∈ U) :
    ∃ p ∈ U, p.val.val 0 = 0 ∧
      hillRealGapHalfLength p.val p.property.1 p.property.2 n ≠ 0 ∧
      hillRealGapHalfLength p.val p.property.1 p.property.2 m ≠ 0 := by
  obtain ⟨r,hrU,hrmean,hrn⟩ := exists_hillMeanZero_logNorming_ne_zero_in_open q n hmean U hU hqU
  let V := U ∩ {p : RealPeriodOneHillPotential | hillDirichletLogMultiplier p.val p.property.1 p.property.2 n n.pos ≠ 0}
  have hV : IsOpen V := hU.inter (isOpen_ne_fun (continuous_hillDirichletLogMultiplier n n.pos) continuous_const)
  obtain ⟨p,hpV,hpmean,hpm⟩ := exists_hillMeanZero_logNorming_ne_zero_in_open r m hrmean V hV ⟨hrU,hrn⟩
  have hopen (j : ℕ+) (hj : hillDirichletLogMultiplier p.val p.property.1 p.property.2 j j.pos ≠ 0) :
      hillRealGapHalfLength p.val p.property.1 p.property.2 j ≠ 0 := by
    intro hc
    exact hj ((hillDirichletSheetRoot_eq_zero_iff_logMultiplier_eq_zero p j j.pos).mp
      (hillDirichletSheetRoot_eq_zero_of_halfLength_zero p.val p.property.1 p.property.2 j j.pos hc))
  exact ⟨p,hpV.1,hpmean,hopen n hpV.2,hopen m hpm⟩

theorem hillMeanZero_mem_closure_selectedOpen
    (q : RealPeriodOneHillPotential) (n m : ℕ+) (hmean : q.val.val 0 = 0) :
    q ∈ closure {p : RealPeriodOneHillPotential | p.val.val 0 = 0 ∧
      hillRealGapHalfLength p.val p.property.1 p.property.2 n ≠ 0 ∧
      hillRealGapHalfLength p.val p.property.1 p.property.2 m ≠ 0} := by
  rw [_root_.mem_closure_iff]
  intro U hU hqU
  obtain ⟨p,hpU,hpmean,hpn,hpm⟩ := exists_hillMeanZero_selectedOpen_in_open q n m hmean U hU hqU
  exact ⟨p,hpU,hpmean,hpn,hpm⟩

end NLS.KdV
