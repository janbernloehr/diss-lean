import NLS.KdV.HillFiniteTraceContour
import NLS.KdV.HillOuterTraceExhaustion
import NLS.KdV.HillHierarchyMomentSummability

/-! # Convergence of actual outer Hill square periods

The finite contour identity and absolute moment summability identify the
limit on Sobolev coefficient domains. Identifying this limit with a physical
Hamiltonian still requires the exterior asymptotic coefficient.
-/

noncomputable section
open Set Complex Filter
open scoped Topology
namespace NLS.KdV

def hillPeriodOneOuterSquarePeriod (w : SpectralWeight)
    (q : WeightedCoeff w.doubleIndex.toWeight 2)
    (hr : IsRealHillPotential (w.doubleIndex.toCoeff q)) (N m : ℕ) : ℂ :=
  let Q := hillPeriodOneUnitPotential w q
  let hQ := hillPeriodOneUnitPotential_even w q
  let hR := hillPeriodOneUnitPotential_real w q hr
  ((Real.pi : ℂ) * I)⁻¹ *
    ∮ z in C((hillRealOuterCenter Q hQ hR : ℂ), hillRealOuterRadius Q hQ hR N),
      z ^ m * hillL2RealCutPrimitive (SpectralWeight.one.toCoeff Q) z ^ 2

theorem hillPeriodOneOuterSquarePeriod_eq_sum (w : SpectralWeight)
    (q : WeightedCoeff w.doubleIndex.toWeight 2)
    (hr : IsRealHillPotential (w.doubleIndex.toCoeff q)) (N m : ℕ) :
    hillPeriodOneOuterSquarePeriod w q hr N m =
      ∑ k ∈ Finset.range N, (2 * (k + 1 : ℕ) * Real.pi : ℂ) *
        hillPeriodOneHierarchyMoment w q hr (k + 1) m := by
  rw [hillPeriodOneOuterSquarePeriod, hillL2OuterSquarePeriod_eq_partial_moments]
  rw [← Finset.Ico_succ_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp only [Order.succ_eq_add_one, Nat.add_sub_cancel, Nat.add_comm 1, hillPeriodOneHierarchyMoment]

theorem tendsto_hillPeriodOneOuterSquarePeriod_sobolev (m : ℕ)
    (q : WeightedCoeff (SpectralWeight.sobolev (m : ℝ) (by positivity)).doubleIndex.toWeight 2)
    (hr : IsRealHillPotential ((SpectralWeight.sobolev (m : ℝ) (by positivity)).doubleIndex.toCoeff q)) :
    Tendsto (fun N : ℕ => hillPeriodOneOuterSquarePeriod
      (SpectralWeight.sobolev (m : ℝ) (by positivity)) q hr N m) atTop
      (𝓝 (∑' k : ℕ, (2 * (k + 1 : ℕ) * Real.pi : ℂ) *
        hillPeriodOneHierarchyMoment (SpectralWeight.sobolev (m : ℝ) (by positivity)) q hr (k + 1) m)) := by
  simpa only [hillPeriodOneOuterSquarePeriod_eq_sum] using
    (summable_hillPeriodOneHierarchyMoment_sobolev m q hr).of_norm.hasSum.tendsto_sum_nat

end NLS.KdV
