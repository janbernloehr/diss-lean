import NLS.Fourier.FourierNLSWeightCompatibility
import NLS.FunctionalAnalysis.IntervalNormGronwall

/-! # Fourier NLS uniqueness from closed-interval initial times

Two-sided Gronwall applies to the difference of interaction curves. In
particular, equality at either endpoint determines the whole closed interval.
-/
noncomputable section
open Set
namespace NLS.Fourier

/-- Interaction solutions on a common bounded set satisfy a two-sided stability bound. -/
theorem norm_sub_nlsInteraction_le_exp (w : SpectralWeight) (a b initial time R : ℝ)
    (hi : initial ∈ Icc a b) (ht : time ∈ Icc a b)
    (v z : ℝ → WeightedCoeff w.toWeight 1)
    (hv : ∀ r ∈ Icc a b, HasDerivWithinAt v (nlsInteraction w r (v r)) (Icc a b) r)
    (hz : ∀ r ∈ Icc a b, HasDerivWithinAt z (nlsInteraction w r (z r)) (Icc a b) r)
    (hvR : ∀ r ∈ Icc a b, ‖v r‖ ≤ R) (hzR : ∀ r ∈ Icc a b, ‖z r‖ ≤ R) :
    ‖v time-z time‖ ≤ ‖v initial-z initial‖*Real.exp (6*R^2*|time-initial|) := by
  have hsub : Icc (min initial time) (max initial time) ⊆ Icc a b :=
    Icc_subset_Icc (le_min hi.1 ht.1) (max_le hi.2 ht.2)
  exact FunctionalAnalysis.norm_le_exp_abs_of_hasDerivWithinAt_Icc
    (fun r hr => ((hv r (hsub hr)).sub (hz r (hsub hr))).mono hsub)
    (fun r hr => norm_nlsInteraction_sub_le w r R (v r) (z r) (hvR r (hsub hr)) (hzR r (hsub hr)))

/-- Equality at any closed-interval initial time, including either endpoint,
determines the interaction solution on the complete interval. -/
theorem eqOn_nlsInteraction_of_initial_closed (w : SpectralWeight) (a b initial : ℝ)
    (hi : initial ∈ Icc a b) (v z : ℝ → WeightedCoeff w.toWeight 1)
    (hv : ∀ r ∈ Icc a b, HasDerivWithinAt v (nlsInteraction w r (v r)) (Icc a b) r)
    (hz : ∀ r ∈ Icc a b, HasDerivWithinAt z (nlsInteraction w r (z r)) (Icc a b) r)
    (hinit : v initial = z initial) : EqOn v z (Icc a b) := by
  obtain ⟨R₁,hR₁⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (fun r hr => (hv r hr).continuousWithinAt)
  obtain ⟨R₂,hR₂⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (fun r hr => (hz r hr).continuousWithinAt)
  intro time ht
  have h := norm_sub_nlsInteraction_le_exp w a b initial time (max R₁ R₂) hi ht v z hv hz
    (fun r hr => (hR₁ r hr).trans (le_max_left _ _))
    (fun r hr => (hR₂ r hr).trans (le_max_right _ _))
  rw [hinit,sub_self,norm_zero,zero_mul] at h
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h)

/-- Endpoint initial values also determine original Fourier trajectories. -/
theorem IsFourierNLSTrajectoryOn.eqOn_of_eq_at_closed
    {w : SpectralWeight} {a b : ℝ} {u v : ℝ → WeightedCoeff w.toWeight 1}
    (hu : IsFourierNLSTrajectoryOn w a b u) (hv : IsFourierNLSTrajectoryOn w a b v)
    (initial : ℝ) (hi : initial ∈ Icc a b) (hinit : u initial = v initial) :
    EqOn u v (Icc a b) := by
  have he := eqOn_nlsInteraction_of_initial_closed w a b initial hi
    (nlsToInteraction w u) (nlsToInteraction w v)
    hu.hasDerivWithinAt_interaction hv.hasDerivWithinAt_interaction
    (congrArg (nlsFreeFlow w.toWeight (-initial)) hinit)
  intro time ht
  have h := congrArg (nlsFreeFlow w.toWeight time) (he ht)
  simpa only [nlsFreeFlow_nlsToInteraction] using h

/-- Cross-weight compatibility includes endpoint initial times and singleton intervals. -/
theorem IsFourierNLSTrajectoryOn.eq_coefficients_of_eq_at_closed
    {w v : SpectralWeight} {a b : ℝ}
    {u : ℝ → WeightedCoeff w.toWeight 1} {z : ℝ → WeightedCoeff v.toWeight 1}
    (hu : IsFourierNLSTrajectoryOn w a b u) (hz : IsFourierNLSTrajectoryOn v a b z)
    (initial : ℝ) (hi : initial ∈ Icc a b)
    (hinit : ∀ n : ℤ, (u initial).val n = (z initial).val n) :
    ∀ time ∈ Icc a b, ∀ n : ℤ, (u time).val n = (z time).val n := by
  have hw : ∀ n, SpectralWeight.one n ≤ w n := fun n => w.one_le n
  have hv : ∀ n, SpectralWeight.one n ≤ v n := fun n => v.one_le n
  have hzero : WeightedCoeff.inclusionCLM (p := 1) w.toWeight SpectralWeight.one.toWeight hw (u initial) =
      WeightedCoeff.inclusionCLM (p := 1) v.toWeight SpectralWeight.one.toWeight hv (z initial) := by
    apply Subtype.ext
    funext n
    simpa only [WeightedCoeff.inclusionCLM_apply] using hinit n
  have he := (hu.inclusion SpectralWeight.one hw).eqOn_of_eq_at_closed
    (hz.inclusion SpectralWeight.one hv) initial hi hzero
  intro time ht n
  have h := congrArg (fun x : WeightedCoeff SpectralWeight.one.toWeight 1 => x.val n) (he ht)
  simpa only [WeightedCoeff.inclusionCLM_apply] using h

end NLS.Fourier
