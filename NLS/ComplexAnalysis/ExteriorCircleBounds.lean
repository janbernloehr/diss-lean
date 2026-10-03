import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Analytic.Basic

/-! # Extending bounds on escaping circles throughout an exterior domain -/
noncomputable section
open Set Metric Filter Topology
namespace NLS.ComplexAnalysis

/-- Maximum modulus on an annulus propagates the two boundary bounds. -/
theorem norm_le_of_annular_boundary_bound (f : ℂ → ℂ) (r S M : ℝ)
    (hr : 0 < r) (hS : 0 < S)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 S \ ball 0 r))
    (hinner : ∀ z ∈ sphere (0 : ℂ) r, ‖f z‖ ≤ M)
    (houter : ∀ z ∈ sphere (0 : ℂ) S, ‖f z‖ ≤ M)
    (z : ℂ) (hzr : r < ‖z‖) (hzS : ‖z‖ < S) : ‖f z‖ ≤ M := by
  let U : Set ℂ := ball 0 S ∩ (closedBall 0 r)ᶜ
  have hcl : closure U ⊆ closedBall 0 S \ ball 0 r := by
    apply closure_minimal
    · intro w hw
      exact ⟨ball_subset_closedBall hw.1, fun h => hw.2 (ball_subset_closedBall h)⟩
    · exact isClosed_closedBall.sdiff isOpen_ball
  have hd : DiffContOnCl ℂ f U :=
    ⟨(hf.differentiableOn.mono (subset_closure.trans hcl)), hf.continuousOn.mono hcl⟩
  apply Complex.norm_le_of_forall_mem_frontier_norm_le
    (isBounded_ball.subset inter_subset_left) hd
  · intro w hw
    have hb := frontier_inter_subset (ball (0 : ℂ) S) (closedBall (0 : ℂ) r)ᶜ hw
    rw [frontier_ball _ hS.ne', frontier_compl, frontier_closedBall _ hr.ne'] at hb
    exact hb.elim (fun h => houter w h.1) (fun h => hinner w h.2)
  · apply subset_closure
    exact ⟨by simpa only [mem_ball, dist_zero_right] using hzS,
      by simpa only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] using hzr⟩

/-- An eventual uniform bound on circles escaping to infinity implies a
bound on the entire exterior, provided the function is analytic there. -/
theorem exists_exterior_bound_of_escaping_circle_bounds (f : ℂ → ℂ) (A : ℝ)
    (hf : AnalyticOnNhd ℂ f {z : ℂ | A < ‖z‖})
    (ρ : ℕ → ℝ) (hρ : Tendsto ρ atTop atTop) (M : ℝ)
    (hb : ∀ᶠ k : ℕ in atTop, ∀ z ∈ sphere (0 : ℂ) (ρ k), ‖f z‖ ≤ M) :
    ∃ R B : ℝ, 0 < R ∧ ∀ z : ℂ, R < ‖z‖ → ‖f z‖ ≤ B := by
  let R := max A 0 + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hAR : A < R := by dsimp [R]; linarith [le_max_left A 0]
  have hcircle : ContinuousOn f (sphere (0 : ℂ) R) := hf.continuousOn.mono (by
    intro z hz
    have he : ‖z‖ = R := by simpa only [mem_sphere, dist_zero_right] using hz
    change A < ‖z‖
    rw [he]
    exact hAR)
  obtain ⟨B, hB⟩ := ((isCompact_sphere (0 : ℂ) R).image_of_continuousOn hcircle).isBounded.exists_norm_le
  refine ⟨R, max B M, hR, ?_⟩
  intro z hz
  obtain ⟨k, hk, hkR, hkz⟩ := (hb.and ((hρ.eventually_gt_atTop R).and
    (hρ.eventually_gt_atTop ‖z‖))).exists
  apply norm_le_of_annular_boundary_bound f R (ρ k) (max B M) hR (hR.trans hkR)
  · apply hf.mono
    intro w hw
    have hrw : R ≤ ‖w‖ := by simpa only [mem_ball, dist_zero_right, not_lt] using hw.2
    exact hAR.trans_le hrw
  · intro w hw
    exact (hB (f w) (mem_image_of_mem f hw)).trans (le_max_left _ _)
  · intro w hw
    exact (hk w hw).trans (le_max_right _ _)
  · exact hz
  · exact hkz

end NLS.ComplexAnalysis
