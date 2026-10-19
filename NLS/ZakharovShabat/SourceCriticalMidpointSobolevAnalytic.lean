import NLS.ZakharovShabat.SourceCriticalMidpointHigherSobolev
import NLS.SequenceSpaces.WeightedAnalyticRealization
import NLS.ZakharovShabat.SourceCriticalGapAnalyticDomain
import NLS.SequenceSpaces.SobolevDerivative
import NLS.ZakharovShabat.CanonicalCriticalFree

/-! # Analytic critical-midpoint corrections

The actual critical-midpoint offset is analytic into every H^k with k at most 2s near real original Hs sources.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The actual critical-midpoint offset in a specified Sobolev target. -/
def sourceCriticalMidpointSobolevRemainder (s k : ℕ) (ab : SobolevSource s) : ScalarSobolev k :=
  WeightedCoeff.ofFunctionOrZero (Weight.sobolev (k:ℝ)) 2 (fun n =>
    canonicalCriticalPoints (by norm_num) (by norm_num)
      (periodOnePotential (higherSobolevSourceInclusion s ab)) (periodOnePotential_mem _) n-
    canonicalPeriodicMidpoint (by norm_num) (by norm_num)
      (periodOnePotential (higherSobolevSourceInclusion s ab)) (periodOnePotential_mem _) n)

/-- At every target order up to 2s, the actual critical-midpoint offset is
analytic and uniformly bounded on a complex neighborhood of each real Hs source. -/
theorem exists_local_sourceCriticalMidpointSobolevRemainder_analytic
    (s k : ℕ) (hk : k ≤ 2*s) (a₀ : realTypeHigherSobolevSourceLocus s) :
    ∃ V : Set (SobolevSource s), IsOpen V ∧ a₀.val ∈ V ∧
      ∃ C : ℝ, 0 ≤ C ∧ AnalyticOnNhd ℂ (sourceCriticalMidpointSobolevRemainder s k) V ∧
        ∀ ab ∈ V, ‖sourceCriticalMidpointSobolevRemainder s k ab‖ ≤ C ∧
          ∀ n, (sourceCriticalMidpointSobolevRemainder s k ab).val n =
            canonicalCriticalPoints (by norm_num) (by norm_num)
              (periodOnePotential (higherSobolevSourceInclusion s ab)) (periodOnePotential_mem _) n-
            canonicalPeriodicMidpoint (by norm_num) (by norm_num)
              (periodOnePotential (higherSobolevSourceInclusion s ab)) (periodOnePotential_mem _) n := by
  let J := higherSobolevSourceInclusion s
  obtain ⟨U,hU,haU,C,hC,hbound⟩ := exists_local_higherSobolev_critical_midpoint_bound s a₀
  obtain ⟨D⟩ := nonempty_sourceCriticalGapAnalyticDomain (p := 2) (by norm_num) (by norm_num)
  let V := U ∩ J ⁻¹' D.domain
  have hV : IsOpen V := hU.inter (D.isOpen.preimage J.continuous)
  let f (ab : SobolevSource s) (n : ℤ) :=
    canonicalCriticalPoints (by norm_num) (by norm_num) (periodOnePotential (J ab))
      (periodOnePotential_mem _) n-
    canonicalPeriodicMidpoint (by norm_num) (by norm_num) (periodOnePotential (J ab))
      (periodOnePotential_mem _) n
  have hf (n : ℤ) : AnalyticOnNhd ℂ (fun ab => f ab n) V := by
    intro ab hab
    exact (D.analyticAt_offset (J ab) hab.2 n).comp (J.analyticAt ab)
  have hfull (ab : SobolevSource s) (hab : ab ∈ V) :
      ∃ e : ScalarSobolev k, (∀ n, e.val n = f ab n) ∧ ‖e‖ ≤ C := by
    obtain ⟨e,he,hen⟩ := hbound ab hab.1
    have hk' : (k:ℝ) ≤ ((2*s:ℕ):ℝ) := by exact_mod_cast hk
    refine ⟨WeightedCoeff.sobolevInclusion hk' e,?_,
      (WeightedCoeff.norm_sobolevInclusion_le hk' e).trans hen⟩
    intro n
    simpa only [WeightedCoeff.sobolevInclusion_apply] using he n
  obtain ⟨han,hval⟩ := WeightedCoeff.analytic_realization_of_bound
    (p := 2) (Weight.sobolev (k:ℝ)) f hV hf C hfull
  exact ⟨V,hV,⟨haU,D.real_subset a₀.property⟩,C,hC,han,hval⟩

/-- Every positive integer source order gives the one derivative gain
needed to replace critical points with periodic midpoints. -/
theorem exists_local_sourceCriticalMidpoint_one_smoothing
    (s : ℕ) (hs : 1 ≤ s) (a₀ : realTypeHigherSobolevSourceLocus s) :
    ∃ V : Set (SobolevSource s), IsOpen V ∧ a₀.val ∈ V ∧
      ∃ C : ℝ, 0 ≤ C ∧ AnalyticOnNhd ℂ (sourceCriticalMidpointSobolevRemainder s (s+1)) V ∧
        ∀ ab ∈ V, ‖sourceCriticalMidpointSobolevRemainder s (s+1) ab‖ ≤ C ∧
          ∀ n, (sourceCriticalMidpointSobolevRemainder s (s+1) ab).val n =
            canonicalCriticalPoints (by norm_num) (by norm_num)
              (periodOnePotential (higherSobolevSourceInclusion s ab)) (periodOnePotential_mem _) n-
            canonicalPeriodicMidpoint (by norm_num) (by norm_num)
              (periodOnePotential (higherSobolevSourceInclusion s ab)) (periodOnePotential_mem _) n :=
  exists_local_sourceCriticalMidpointSobolevRemainder_analytic s (s+1) (by omega) a₀

@[simp] theorem sourceCriticalMidpointSobolevRemainder_zero (s k : ℕ) :
    sourceCriticalMidpointSobolevRemainder s k 0 = 0 := by
  apply WeightedCoeff.ofFunctionOrZero_eq_of_coordinates
  intro n
  simp only [WeightedCoeff.zero_val,map_zero,canonicalCriticalPoints_zero,canonicalPeriodicMidpoint_zero,sub_self]

end NLS.ZakharovShabat
