import NLS.ZakharovShabat.L2WholeLinePotentialPeriods
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Local square integrability of the actual periodic physical potential

Two adjacent unit periods give a neighborhood of every point. Their
square integrability and global measurability imply square integrability
on every compact subset of the real line.
-/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter Topology
namespace NLS.ZakharovShabat

/-- The fractional-part periodic representative is globally strongly measurable. -/
theorem stronglyMeasurable_l2WholeLinePotential (u : IntervalPairL2) :
    StronglyMeasurable (l2WholeLinePotential u) :=
  ((Lp.stronglyMeasurable u.ofLp.1).prodMk (Lp.stronglyMeasurable u.ofLp.2)).comp_measurable
    measurable_fract

/-- The squared norm of the physical potential is locally integrable,
including across each integer seam. -/
theorem locallyIntegrable_norm_sq_l2WholeLinePotential (u : IntervalPairL2) :
    LocallyIntegrable (fun t : ℝ => ‖l2WholeLinePotential u t‖^2) volume := by
  intro x
  let n : ℤ := ⌊x⌋
  have hleft := (memLp_l2WholeLinePotential_period u (n-1)).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hright := (memLp_l2WholeLinePotential_period u n).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hleft' : IntegrableOn (fun t : ℝ => ‖l2WholeLinePotential u t‖^2)
      (Ioc ((n : ℝ)-1) n) volume := by
    simpa only [IntegrableOn,Int.cast_sub,Int.cast_one,sub_add_cancel] using! hleft
  have hi := hleft'.union hright
  rw [Ioc_union_Ioc_eq_Ioc (by linarith : (n : ℝ)-1 ≤ n) (by linarith : (n : ℝ) ≤ n+1)] at hi
  refine ⟨Ioc ((n : ℝ)-1) ((n : ℝ)+1),?_,hi⟩
  apply Ioc_mem_nhds
  · have h := Int.floor_le x
    change (⌊x⌋ : ℝ)-1 < x
    linarith
  · exact Int.lt_floor_add_one x

/-- The periodically extended physical potential belongs to L2 on every compact set. -/
theorem memLp_l2WholeLinePotential_on_compact (u : IntervalPairL2)
    {K : Set ℝ} (hK : IsCompact K) :
    MemLp (l2WholeLinePotential u) 2 (volume.restrict K) := by
  apply (memLp_two_iff_integrable_sq_norm
    (stronglyMeasurable_l2WholeLinePotential u).aestronglyMeasurable).mpr
  exact (locallyIntegrable_norm_sq_l2WholeLinePotential u).integrableOn_isCompact hK

/-- In particular, the actual potential is square integrable on any bounded closed interval. -/
theorem memLp_l2WholeLinePotential_Icc (u : IntervalPairL2) (a b : ℝ) :
    MemLp (l2WholeLinePotential u) 2 (volume.restrict (Icc a b)) :=
  memLp_l2WholeLinePotential_on_compact u isCompact_Icc

end NLS.ZakharovShabat
