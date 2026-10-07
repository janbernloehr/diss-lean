import NLS.Fourier.FourierNLSIntegral

/-! # Uniqueness for local weighted Fourier NLS solutions

Compactness bounds both interaction curves. The cubic Lipschitz estimate
then yields uniqueness from equality at any interior time, for the complete
coefficientwise trajectory predicate rather than only a constructed solution.
-/
noncomputable section
open Set Metric
open scoped NNReal
namespace NLS.Fourier

/-- Strong interaction solutions with the same interior initial value coincide. -/
theorem eqOn_nlsInteraction_of_initial (w : SpectralWeight) (a b initial : ℝ)
    (hi : initial ∈ Ioo a b) (v z : ℝ → WeightedCoeff w.toWeight 1)
    (hv : ∀ time ∈ Icc a b, HasDerivWithinAt v (nlsInteraction w time (v time)) (Icc a b) time)
    (hz : ∀ time ∈ Icc a b, HasDerivWithinAt z (nlsInteraction w time (z time)) (Icc a b) time)
    (hinit : v initial = z initial) : EqOn v z (Icc a b) := by
  have hc : ContinuousOn v (Icc a b) := fun time ht => (hv time ht).continuousWithinAt
  have hd : ContinuousOn z (Icc a b) := fun time ht => (hz time ht).continuousWithinAt
  obtain ⟨R₁,hR₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  obtain ⟨R₂,hR₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hd
  let R := max R₁ R₂
  let K : ℝ≥0 := ⟨6*R^2,by positivity⟩
  have hL (time : ℝ) : LipschitzOnWith K (nlsInteraction w time) (closedBall 0 R) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hx' : ‖x‖ ≤ R := by simpa only [mem_closedBall,dist_zero_right] using hx
    have hy' : ‖y‖ ≤ R := by simpa only [mem_closedBall,dist_zero_right] using hy
    simpa only [dist_eq_norm,K,NNReal.coe_mk] using! norm_nlsInteraction_sub_le w time R x y hx' hy'
  have hvR (time : ℝ) (ht : time ∈ Ioo a b) : v time ∈ closedBall 0 R := by
    rw [mem_closedBall,dist_zero_right]
    exact (hR₁ time ⟨ht.1.le,ht.2.le⟩).trans (le_max_left _ _)
  have hzR (time : ℝ) (ht : time ∈ Ioo a b) : z time ∈ closedBall 0 R := by
    rw [mem_closedBall,dist_zero_right]
    exact (hR₂ time ⟨ht.1.le,ht.2.le⟩).trans (le_max_right _ _)
  exact ODE_solution_unique_of_mem_Icc (fun time _ => hL time) hi hc
    (fun time ht => (hv time ⟨ht.1.le,ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)) hvR hd
    (fun time ht => (hz time ⟨ht.1.le,ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)) hzR hinit

/-- Uniqueness holds for every continuous solution of the original mode equations. -/
theorem IsFourierNLSTrajectoryOn.eqOn_of_eq_at
    {w : SpectralWeight} {a b : ℝ} {u v : ℝ → WeightedCoeff w.toWeight 1}
    (hu : IsFourierNLSTrajectoryOn w a b u) (hv : IsFourierNLSTrajectoryOn w a b v)
    (initial : ℝ) (hi : initial ∈ Ioo a b) (hinit : u initial = v initial) :
    EqOn u v (Icc a b) := by
  have he := eqOn_nlsInteraction_of_initial w a b initial hi
    (nlsToInteraction w u) (nlsToInteraction w v)
    hu.hasDerivWithinAt_interaction hv.hasDerivWithinAt_interaction
    (congrArg (nlsFreeFlow w.toWeight (-initial)) hinit)
  intro time ht
  have h := congrArg (nlsFreeFlow w.toWeight time) (he ht)
  simpa only [nlsFreeFlow_nlsToInteraction] using h

/-- Local existence is unique on the asserted interval, leaving values outside
that interval unrestricted. -/
theorem exists_unique_local_fourierNLSTrajectory (w : SpectralWeight)
    (u₀ : WeightedCoeff w.toWeight 1) :
    ∃ T > 0, ∃ u : ℝ → WeightedCoeff w.toWeight 1,
      u 0 = u₀ ∧ IsFourierNLSTrajectoryOn w (-T) T u ∧
      ∀ v : ℝ → WeightedCoeff w.toWeight 1,
        IsFourierNLSTrajectoryOn w (-T) T v → v 0 = u₀ → EqOn v u (Icc (-T) T) := by
  obtain ⟨T,hT,u,hu0,hu⟩ := exists_local_fourierNLSTrajectory w u₀
  refine ⟨T,hT,u,hu0,hu,?_⟩
  intro v hv hv0
  exact hv.eqOn_of_eq_at hu 0 ⟨by linarith,hT⟩ (hv0.trans hu0.symm)

end NLS.Fourier
