import NLS.ComplexAnalysis.ZeroCountComparison
import NLS.ZakharovShabat.ResonantDeterminantLocalization

/-!
# Two scalar analytic zeros of the resonant determinant

Rouché's theorem applies to the actual analytic determinant and its centered
square on the refined circle. The resulting count uses analytic zero orders.
Localization then gives the same count on the open refined disc and on the
whole source strip. One cutoff and one open convex potential neighborhood
work for every sufficiently distant signed resonance.
-/

noncomputable section
open scoped ENNReal
open NLS.ComplexAnalysis
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual determinant has total analytic multiplicity two on every distant strip, locally uniformly. -/
theorem exists_uniform_resonantDeterminant_zeroCount (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ n : ℤ, N ≤ n.natAbs →
        AnalyticOnNhd ℂ (resonantDeterminantExtension hp w ψ n) (resonantStrip n) ∧
        (∀ z ∈ Metric.sphere ((Real.pi : ℂ)*n) (Real.pi/4),
          resonantDeterminantExtension hp w ψ n z ≠ 0) ∧
        (resonantStrip n ∩ (resonantDeterminantExtension hp w ψ n) ⁻¹' {0}).Finite ∧
        (∀ z ∈ resonantStrip n, analyticOrderAt (resonantDeterminantExtension hp w ψ n) z ≠ ⊤) ∧
        analyticZeroCount (resonantDeterminantExtension hp w ψ n)
          (Metric.closedBall ((Real.pi : ℂ)*n) (Real.pi/4)) = 2 ∧
        analyticZeroCount (resonantDeterminantExtension hp w ψ n) (refinedResonantDisk n) = 2 ∧
        analyticZeroCount (resonantDeterminantExtension hp w ψ n) (resonantStrip n) = 2 := by
  obtain ⟨N,hN,U,ho,hc,hφ,h0,hb⟩ := exists_uniform_resonantDeterminant_localization hp hp1 w φ
  refine ⟨N,hN,U,ho,hc,hφ,h0,?_⟩
  intro ψ hψ n hn
  obtain ⟨ha,_,hloc,hcomp⟩ := hb ψ hψ n hn
  have hr : 0 < Real.pi/4 := by positivity
  have hsub := closedBall_subset_resonantStrip n (by linarith [Real.pi_pos] : Real.pi/4 ≤ Real.pi/2)
  have had := ha.mono hsub
  have hboundary : ∀ z ∈ Metric.sphere ((Real.pi : ℂ)*n) (Real.pi/4),
      resonantDeterminantExtension hp w ψ n z ≠ 0 :=
    fun z hz => (rouche_ratio_mem_slitPlane (hcomp z hz)).2.1
  have hclosed := analyticZeroCount_eq_degree_of_boundary_lt 2 hr had hcomp
  have hopen : analyticZeroCount (resonantDeterminantExtension hp w ψ n) (refinedResonantDisk n) = 2 := by
    rw [refinedResonantDisk, analyticZeroCount_ball_eq_closedBall hboundary, hclosed]
  have heq : resonantStrip n ∩ (resonantDeterminantExtension hp w ψ n) ⁻¹' {0} =
      Metric.closedBall ((Real.pi : ℂ)*n) (Real.pi/4) ∩
        (resonantDeterminantExtension hp w ψ n) ⁻¹' {0} := by
    ext z
    exact ⟨fun hz => ⟨Metric.ball_subset_closedBall (hloc z hz.1 hz.2).2,hz.2⟩,
      fun hz => ⟨hsub hz.1,hz.2⟩⟩
  obtain ⟨b,hbm⟩ := NormedSpace.sphere_nonempty (E := ℂ) (x := (Real.pi : ℂ)*n) |>.mpr hr.le
  have hbclosed := Metric.sphere_subset_closedBall hbm
  have hbf := hboundary b hbm
  refine ⟨ha,hboundary,?_,?_,hclosed,hopen,?_⟩
  · rw [heq]
    exact finite_analytic_zeros (isCompact_closedBall _ _) (Metric.isConnected_closedBall hr.le) had hbclosed hbf
  · intro z hz
    by_cases hfz : resonantDeterminantExtension hp w ψ n z = 0
    · exact analyticOrderAt_ne_top_on_connected (Metric.isConnected_closedBall hr.le).isPreconnected
        had hbclosed hbf (Metric.ball_subset_closedBall (hloc z hz hfz).2)
    · rw [(ha z hz).analyticOrderAt_eq_zero.mpr hfz]
      exact ENat.zero_ne_top
  · rw [analyticZeroCount_congr_set (resonantDeterminantExtension hp w ψ n)
      (K := resonantStrip n) (L := refinedResonantDisk n)
      (fun z hz => ⟨fun hs => (hloc z hs hz).2, fun hd => refinedResonantDisk_subset_strip n hd⟩), hopen]

end NLS.ZakharovShabat
