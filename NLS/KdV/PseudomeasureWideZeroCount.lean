import NLS.KdV.PseudomeasureWideAnalytic
import NLS.KdV.PseudomeasureMultiplicityOrder

/-! The original determinant has exactly two analytic zeros on the full
12n strip. Its analytic multiplicities are the original physical algebraic
multiplicities throughout that strip. -/
noncomputable section
open Set Metric
open scoped ENNReal Classical
namespace NLS.KdV
open NLS.ComplexAnalysis

theorem reducedHillStrip_subset_wide (n : ℕ) : reducedHillStrip n ⊆ wideHillStrip n := by
  intro z hz
  change |z.re-freeHillValue n| ≤ 12*(n:ℝ)
  have h : |z.re-freeHillValue n| ≤ 6*(n:ℝ) := hz
  linarith [Nat.cast_nonneg (α:=ℝ) n]

variable (r : ℝ) (hr : 0≤r) (hr1 : r<1/2) (n : ℕ) (hn : 2≤n)
variable (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
variable (hs : 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)
include hn hs

theorem endpointReducedDeterminant_wide_zero_localization (z : ℂ) (hz : z ∈ wideHillStrip n)
    (hd : endpointReducedDeterminant r hr hr1 n (q,z)=0) :
    z ∈ reducedHillStrip n ∧ ‖z-(freeHillValue n:ℂ)‖ ≤ Real.sqrt (n:ℝ)/4 := by
  obtain ⟨f,hf0,hf⟩ := (endpointReducedDeterminant_eq_zero_iff_wide r hr hr1 n hn (q,z) hz hs).mp hd
  exact endpointHillSpectrum_wide_localization r hr hr1 n hn z hz q hs
    ((mem_endpointHillSpectrum_iff r hr hr1 q z).mpr ⟨f,hf0,hf⟩)

theorem endpointReducedDeterminant_wide_two_zeros :
    analyticZeroCount (fun z => endpointReducedDeterminant r hr hr1 n (q,z)) (wideHillStrip n)=2 := by
  have hc : analyticZeroCount (fun z => endpointReducedDeterminant r hr hr1 n (q,z)) (wideHillStrip n)=
      analyticZeroCount (fun z => endpointReducedDeterminant r hr hr1 n (q,z)) (reducedHillStrip n) := by
    apply analyticZeroCount_congr_set
    intro z hd
    exact ⟨fun hz => (endpointReducedDeterminant_wide_zero_localization r hr hr1 n hn q hs z hz hd).1,
      fun hz => reducedHillStrip_subset_wide n hz⟩
  rw [hc]
  exact endpointReducedDeterminant_strip_two_zeros r hr hr1 n (by omega) q
    (endpointHill_small_of_wide_small r hr1 n q hs)

theorem endpointHillAlgebraicMultiplicity_eq_analyticOrderNatAt_wide (z : ℂ) (hz : z ∈ wideHillStrip n) :
    endpointHillAlgebraicMultiplicity r hr hr1 q z=
      analyticOrderNatAt (fun y => endpointReducedDeterminant r hr hr1 n (q,y)) z := by
  by_cases hzN : z ∈ reducedHillStrip n
  · exact endpointHillAlgebraicMultiplicity_eq_analyticOrderNatAt r hr hr1 n (by omega) q
      (endpointHill_small_of_wide_small r hr1 n q hs) z hzN
  · have hd : endpointReducedDeterminant r hr hr1 n (q,z)≠0 := by
      intro h
      exact hzN (endpointReducedDeterminant_wide_zero_localization r hr hr1 n hn q hs z hz h).1
    have horder : analyticOrderNatAt (fun y => endpointReducedDeterminant r hr hr1 n (q,y)) z=0 := by
      by_contra h
      have he : (fun y : ℂ => endpointReducedDeterminant r hr hr1 n (q,y)) z=0 :=
        apply_eq_zero_of_analyticOrderNatAt_ne_zero (f := fun y : ℂ => endpointReducedDeterminant r hr hr1 n (q,y)) h
      exact hd he
    have hmult : endpointHillAlgebraicMultiplicity r hr hr1 q z=0 := by
      by_contra h
      have hsp := (endpointHillAlgebraicMultiplicity_pos_iff r hr hr1 q z).mp (Nat.pos_of_ne_zero h)
      exact hzN (endpointHillSpectrum_wide_localization r hr hr1 n hn z hz q hs hsp).1
    rw [horder,hmult]

theorem endpointHill_wide_strip_algebraic_count_two :
    (∑ᶠ z : ℂ, if z ∈ wideHillStrip n then endpointHillAlgebraicMultiplicity r hr hr1 q z else 0)=2 := by
  calc
    _ = analyticZeroCount (fun z => endpointReducedDeterminant r hr hr1 n (q,z)) (wideHillStrip n) := by
      unfold analyticZeroCount
      apply finsum_congr
      intro z
      split_ifs with hz
      · exact endpointHillAlgebraicMultiplicity_eq_analyticOrderNatAt_wide r hr hr1 n hn q hs z hz
      · rfl
    _ = 2 := endpointReducedDeterminant_wide_two_zeros r hr hr1 n hn q hs

end NLS.KdV
