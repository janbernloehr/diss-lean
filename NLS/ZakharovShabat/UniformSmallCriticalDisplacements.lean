import NLS.ZakharovShabat.UniformCanonicalCriticalPoints
import NLS.ZakharovShabat.UniformCriticalCounts

/-! # Uniformly small canonical critical displacements
The small-disc counting theorem supplies a root. Uniqueness in the common
quarter-pi disc identifies it with the actual canonical coordinate.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Canonical critical displacements are uniformly small at large signed indices near each potential. -/
theorem exists_uniform_small_canonicalCriticalDisplacements (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∃ U : Set (PairSpace p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ heven : ψ ∈ pairParitySubspace 0, ∀ n : ℤ, N < n.natAbs →
        ‖canonicalCriticalDisplacement hp hp1 ψ heven n‖ < ε := by
  let r := min ε (Real.pi/4)
  have hr : 0 < r := lt_min hε (by positivity)
  obtain ⟨N,hN,U,ho,hc,hφ,h0,hd⟩ := exists_uniform_discriminant_critical_distribution hp hp1 φ hr (min_le_right _ _)
  obtain ⟨M,_,V,hvo,hvc,hvφ,hv0,_,_,hl⟩ := exists_uniform_canonicalCriticalPoints hp hp1 φ
  refine ⟨max N M,lt_of_lt_of_le hN (le_max_left _ _),U ∩ V,ho.inter hvo,hc.inter hvc,
    ⟨hφ,hvφ⟩,⟨h0,hv0⟩,fun ψ hψ heven n hn => ?_⟩
  obtain ⟨z,hz,hroot,_,_⟩ := (hd ψ hψ.1 heven).1 n (lt_of_le_of_lt (le_max_left _ _) hn)
  have hzbig : z ∈ closedBall ((Real.pi : ℂ)*n) (Real.pi/4) :=
    ball_subset_closedBall ((ball_subset_ball (min_le_right _ _)) hz)
  have he := ((hl ψ hψ.2 heven).1.distant n (lt_of_le_of_lt (le_max_right _ _) hn)).2.2.2 z hzbig |>.mp hroot
  rw [canonicalCriticalDisplacement_apply,← he]
  exact (show ‖z-(Real.pi : ℂ)*n‖ < r by simpa only [mem_ball,dist_eq_norm] using hz).trans_le (min_le_left _ _)

end NLS.ZakharovShabat
