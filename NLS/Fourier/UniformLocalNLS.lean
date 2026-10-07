import NLS.Fourier.FourierNLSEndpointUniqueness

/-! # Uniform local existence at arbitrary initial times

One explicit lifespan works for all spectral weights, all initial times,
and all initial data in a fixed norm ball. This supplies the local step
needed for continuation of bounded Fourier trajectories.
-/
noncomputable section
open Set Metric
open scoped NNReal
namespace NLS.Fourier

/-- A local half-lifespan for initial data with norm at most `B`. -/
def nlsLocalTime (B : ℝ) : ℝ := 1/(2*(B+1)^3+1)

theorem nlsLocalTime_pos (B : ℝ) (hB : 0 ≤ B) : 0 < nlsLocalTime B := by
  unfold nlsLocalTime
  positivity

/-- Uniform local interaction existence, with arbitrary real initial time. -/
theorem exists_nlsInteraction_on_uniform_interval (w : SpectralWeight)
    (B : ℝ) (hB : 0 ≤ B) (initial : ℝ) (a : WeightedCoeff w.toWeight 1) (ha : ‖a‖ ≤ B) :
    ∃ v : ℝ → WeightedCoeff w.toWeight 1, v initial = a ∧
      ∀ time ∈ Icc (initial-nlsLocalTime B) (initial+nlsLocalTime B),
        HasDerivWithinAt v (nlsInteraction w time (v time))
          (Icc (initial-nlsLocalTime B) (initial+nlsLocalTime B)) time := by
  let R : ℝ := B+1
  let L : ℝ≥0 := ⟨2*R^3,by dsimp [R]; positivity⟩
  let K : ℝ≥0 := ⟨6*R^2,by positivity⟩
  have hT := nlsLocalTime_pos B hB
  have hbound (b : WeightedCoeff w.toWeight 1) (hb : b ∈ closedBall a 1) : ‖b‖ ≤ R := by
    have hd : ‖b-a‖ ≤ 1 := mem_closedBall_iff_norm.mp hb
    exact (norm_le_norm_sub_add b a).trans (by dsimp [R]; linarith)
  have hPL : IsPicardLindelof (nlsInteraction w)
      (tmin := initial-nlsLocalTime B) (tmax := initial+nlsLocalTime B)
      ⟨initial,by constructor <;> linarith⟩ a 1 0 L K := by
    constructor
    · intro time _
      apply LipschitzOnWith.of_dist_le_mul
      intro b hb c hc
      simpa only [dist_eq_norm,K,NNReal.coe_mk] using!
        norm_nlsInteraction_sub_le w time R b c (hbound b hb) (hbound c hc)
    · intro b _
      exact ((continuous_nlsInteraction w).comp (continuous_id.prodMk continuous_const)).continuousOn
    · intro time _ b hb
      exact (norm_nlsInteraction_le w time b).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg b) (hbound b hb) 3) (by norm_num))
    · change (L : ℝ)*max (initial+nlsLocalTime B-initial)
        (initial-(initial-nlsLocalTime B)) ≤ (1 : ℝ)-(0 : ℝ)
      simp only [add_sub_cancel_left,sub_sub_cancel,max_self,sub_zero]
      change (2*(B+1)^3)*(1/(2*(B+1)^3+1)) ≤ 1
      rw [mul_one_div,div_le_one (by positivity)]
      linarith
  exact hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

/-- Restore the free evolution of a strong interaction curve. -/
theorem isFourierNLSTrajectoryOn_of_interaction (w : SpectralWeight) (a b : ℝ)
    (v : ℝ → WeightedCoeff w.toWeight 1)
    (hv : ∀ time ∈ Icc a b, HasDerivWithinAt v (nlsInteraction w time (v time)) (Icc a b) time) :
    IsFourierNLSTrajectoryOn w a b (fun time => nlsFreeFlow w.toWeight time (v time)) := by
  have hc : ContinuousOn v (Icc a b) := fun time ht => (hv time ht).continuousWithinAt
  have hg : ContinuousOn (fun time => (time,v time)) (Icc a b) := continuousOn_id.prodMk hc
  have h := (continuous_nlsFreeFlow w.toWeight).comp_continuousOn hg
  refine ⟨?_,fun time ht n => hasDerivWithinAt_nlsFreeFlow_of_interaction w v _ time (hv time ht) n⟩
  simpa only [Function.comp_def] using! h

/-- Original Fourier trajectories exist on the same explicit interval for
all data in the norm ball, with uniqueness from any initial time. -/
theorem exists_fourierNLS_on_uniform_interval (w : SpectralWeight)
    (B : ℝ) (hB : 0 ≤ B) (initial : ℝ) (a : WeightedCoeff w.toWeight 1) (ha : ‖a‖ ≤ B) :
    ∃ u : ℝ → WeightedCoeff w.toWeight 1, u initial = a ∧
      IsFourierNLSTrajectoryOn w (initial-nlsLocalTime B) (initial+nlsLocalTime B) u := by
  obtain ⟨v,hv0,hv⟩ := exists_nlsInteraction_on_uniform_interval w B hB initial
    (nlsFreeFlow w.toWeight (-initial) a) (by simpa only [norm_nlsFreeFlow] using ha)
  refine ⟨fun time => nlsFreeFlow w.toWeight time (v time),?_,
    isFourierNLSTrajectoryOn_of_interaction w _ _ v hv⟩
  change nlsFreeFlow w.toWeight initial (v initial) = a
  rw [hv0,nlsFreeFlow_add,add_neg_cancel,nlsFreeFlow_zero]

end NLS.Fourier
