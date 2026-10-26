import NLS.ZakharovShabat.L2FloquetNonrealTrace
import NLS.ZakharovShabat.FloquetRootProjection
import NLS.ZakharovShabat.L2Discriminant
import Mathlib.Analysis.Analytic.Order
import Mathlib.Topology.Compactness.Lindelof

/-! # Countability of the repeated-root exceptional set of the physical monodromy -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter
namespace NLS.ZakharovShabat

/-- The physical monodromy has distinct roots at every nonreal parameter. -/
theorem l2Monodromy_discriminant_ne_zero_of_nonreal (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (z : ℂ) (hz : z.im ≠ 0) :
    (l2Monodromy u z).trace ^ 2 - 4 ≠ 0 := by
  obtain ⟨μ,ν,b,hsum,hprod,_,hstable,hunstable,_,_⟩ :=
    l2Monodromy_nonreal_exists_stable_unstable_basis_with_trace u hu z hz
  have hne : μ ≠ ν := by intro h; rw [h] at hstable; linarith
  rw [← floquet_root_separation_sq _ μ ν hsum hprod]
  exact pow_ne_zero _ (sub_ne_zero.mpr hne)

/-- The repeated-root parameters of the actual monodromy form a countable set. -/
theorem countable_l2Monodromy_repeated_roots (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) :
    {z : ℂ | (l2Monodromy u z).trace ^ 2 - 4 = 0}.Countable := by
  have ha : AnalyticOnNhd ℂ (fun z : ℂ => (l2Monodromy u z).trace ^ 2 - 4) univ := by
    intro z _
    have hd : AnalyticAt ℂ (fun w : ℂ => l2Discriminant u w) z :=
      (analyticOnNhd_l2Discriminant_joint (z,u) (mem_univ _)).comp
        (f := fun w : ℂ => (w,u)) (analyticAt_id.prod analyticAt_const)
    exact hd.pow 2 |>.sub analyticAt_const
  have hn := l2Monodromy_discriminant_ne_zero_of_nonreal u hu Complex.I (by simp)
  have hc := ha.preimage_zero_mem_codiscrete hn
  have hd : IsDiscrete {z : ℂ | (l2Monodromy u z).trace ^ 2 - 4 = 0} := by
    have he : (fun z : ℂ => (l2Monodromy u z).trace ^ 2 - 4) ⁻¹' {0} =
        {z : ℂ | (l2Monodromy u z).trace ^ 2 - 4 = 0} := by ext z; simp
    rw [← he]
    simpa only [← preimage_compl, compl_compl] using (mem_codiscrete'.mp hc).2
  exact (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete hd

/-- In particular the exceptional parameters on the real spectral axis are countable. -/
theorem countable_l2Monodromy_real_repeated_roots (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) :
    {x : ℝ | (l2Monodromy u (x : ℂ)).trace ^ 2 - 4 = 0}.Countable :=
  (countable_l2Monodromy_repeated_roots u hu).preimage Complex.ofReal_injective

end NLS.ZakharovShabat
