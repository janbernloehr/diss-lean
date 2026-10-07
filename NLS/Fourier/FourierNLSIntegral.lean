import NLS.Fourier.LocalNLSExistence
import NLS.SequenceSpaces.WeightedCoordinateFTC

/-! # Fourier NLS trajectories and their strong interaction equations

Every norm-continuous solution of the original mode equations has a strong
interaction derivative. Thus the local existence theorem's coefficientwise
conclusion carries the Banach-space integral equation needed for uniqueness.
-/
noncomputable section
open Set Complex MeasureTheory
namespace NLS.Fourier

/-- The original coefficient equations on a closed interval, with norm continuity. -/
structure IsFourierNLSTrajectoryOn (w : SpectralWeight) (a b : ℝ)
    (u : ℝ → WeightedCoeff w.toWeight 1) : Prop where
  continuous : ContinuousOn u (Icc a b)
  equation : ∀ time ∈ Icc a b, ∀ n : ℤ,
    HasDerivWithinAt (fun r => (u r).val n)
      (nlsLinearSymbol n*(u time).val n + (cubicNLS w (u time)).val n) (Icc a b) time

/-- The constructed local coefficient solution satisfies the trajectory predicate. -/
theorem exists_local_fourierNLSTrajectory (w : SpectralWeight) (u₀ : WeightedCoeff w.toWeight 1) :
    ∃ T > 0, ∃ u : ℝ → WeightedCoeff w.toWeight 1,
      u 0 = u₀ ∧ IsFourierNLSTrajectoryOn w (-T) T u := by
  obtain ⟨T,hT,u,hu0,hc,hd⟩ := exists_local_fourierNLS w u₀
  exact ⟨T,hT,u,hu0,⟨hc,hd⟩⟩

/-- Remove the free Schrödinger phases from an original Fourier curve. -/
def nlsToInteraction (w : SpectralWeight) (u : ℝ → WeightedCoeff w.toWeight 1)
    (time : ℝ) : WeightedCoeff w.toWeight 1 := nlsFreeFlow w.toWeight (-time) (u time)

@[simp] theorem nlsFreeFlow_nlsToInteraction (w : SpectralWeight)
    (u : ℝ → WeightedCoeff w.toWeight 1) (time : ℝ) :
    nlsFreeFlow w.toWeight time (nlsToInteraction w u time) = u time := by
  rw [nlsToInteraction,nlsFreeFlow_add,add_neg_cancel,nlsFreeFlow_zero]

namespace IsFourierNLSTrajectoryOn
variable {w : SpectralWeight} {a b : ℝ} {u : ℝ → WeightedCoeff w.toWeight 1}

theorem continuous_interaction (hu : IsFourierNLSTrajectoryOn w a b u) :
    ContinuousOn (nlsToInteraction w u) (Icc a b) := by
  have hg : ContinuousOn (fun time => (-time,u time)) (Icc a b) := continuousOn_id.neg.prodMk hu.continuous
  have h := (continuous_nlsFreeFlow w.toWeight).comp_continuousOn hg
  simpa only [Function.comp_def,nlsToInteraction] using! h

/-- The integrating factor cancels the unbounded linear symbol in every mode. -/
theorem hasDerivWithinAt_interaction_coefficient (hu : IsFourierNLSTrajectoryOn w a b u)
    (time : ℝ) (ht : time ∈ Icc a b) (n : ℤ) :
    HasDerivWithinAt (fun r => (nlsToInteraction w u r).val n)
      ((nlsInteraction w time (nlsToInteraction w u time)).val n) (Icc a b) time := by
  have hd := (NLS.ComplexAnalysis.hasDerivAt_complex_exp_mul (-nlsLinearSymbol n) time).hasDerivWithinAt.mul
    (hu.equation time ht n)
  have hvel : nlsInteraction w time (nlsToInteraction w u time) =
      nlsFreeFlow w.toWeight (-time) (cubicNLS w (u time)) := by
    rw [nlsInteraction,nlsFreeFlow_nlsToInteraction]
  rw [hvel,nlsFreeFlow_apply]
  convert! hd using 1
  · funext r
    simp only [nlsToInteraction,nlsFreeFlow_apply,Complex.ofReal_neg,mul_neg,neg_mul,Pi.mul_apply]
  · simp only [Complex.ofReal_neg,mul_neg,neg_mul]
    ring

/-- The scalar mode equations imply the actual weighted Banach-space derivative. -/
theorem hasDerivWithinAt_interaction (hu : IsFourierNLSTrajectoryOn w a b u)
    (time : ℝ) (ht : time ∈ Icc a b) :
    HasDerivWithinAt (nlsToInteraction w u)
      (nlsInteraction w time (nlsToInteraction w u time)) (Icc a b) time := by
  have hc := hu.continuous_interaction
  have hg : ContinuousOn (fun r => (r,nlsToInteraction w u r)) (Icc a b) := continuousOn_id.prodMk hc
  have hv := (continuous_nlsInteraction w).comp_continuousOn hg
  apply w.hasDerivWithinAt_of_coordinate_derivatives a b _ _ hc hv _ time ht
  intro r hr n
  exact (hu.hasDerivWithinAt_interaction_coefficient r ⟨hr.1.le,hr.2.le⟩ n).hasDerivAt
    (Icc_mem_nhds hr.1 hr.2)

/-- The interaction curve satisfies the full Bochner integral equation. -/
theorem interaction_eq_add_integral (hu : IsFourierNLSTrajectoryOn w a b u)
    (time : ℝ) (ht : time ∈ Icc a b) :
    nlsToInteraction w u time = nlsToInteraction w u a +
      ∫ r in a..time, nlsInteraction w r (nlsToInteraction w u r) := by
  have hc := hu.continuous_interaction
  have hg : ContinuousOn (fun r => (r,nlsToInteraction w u r)) (Icc a b) := continuousOn_id.prodMk hc
  have hv := (continuous_nlsInteraction w).comp_continuousOn hg
  apply w.eq_add_integral_of_coordinate_derivatives a b _ _ hc hv _ time ht
  intro r hr n
  exact (hu.hasDerivWithinAt_interaction_coefficient r ⟨hr.1.le,hr.2.le⟩ n).hasDerivAt
    (Icc_mem_nhds hr.1 hr.2)

/-- Restricting the time interval preserves the full coefficient equations. -/
theorem restrict (hu : IsFourierNLSTrajectoryOn w a b u) {c d : ℝ} (hac : a ≤ c) (hdb : d ≤ b) :
    IsFourierNLSTrajectoryOn w c d u := by
  have hsub : Icc c d ⊆ Icc a b := Icc_subset_Icc hac hdb
  exact ⟨hu.continuous.mono hsub,fun time ht n => (hu.equation time (hsub ht) n).mono hsub⟩

end IsFourierNLSTrajectoryOn
end NLS.Fourier
