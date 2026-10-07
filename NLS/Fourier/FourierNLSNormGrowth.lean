import NLS.Fourier.TameCubicNLS
import NLS.Fourier.FourierNLSWeightCompatibility
import NLS.FunctionalAnalysis.IntervalNormGronwall

/-! # Higher norm growth controlled by the raw Fourier norm

A bound on the unweighted ℓ¹ norm controls higher Sobolev norms exponentially
in either time direction. The low norm may come from an independently
constructed compatible trajectory. These are a priori estimates on the
existing interval; extension of that interval is a separate step.
-/
noncomputable section
open Set
namespace NLS.Fourier
namespace IsFourierNLSTrajectoryOn

/-- Tame a priori growth on any closed subinterval, in either direction. -/
theorem norm_le_exp_of_unweighted_bound
    {w : SpectralWeight} {a b : ℝ} {u : ℝ → WeightedCoeff w.toWeight 1}
    (hu : IsFourierNLSTrajectoryOn w a b u)
    (C : ℝ) (hC : 0 ≤ C) (hadd : ∀ n k : ℤ, w (n+k) ≤ C*(w n+w k))
    (initial time : ℝ) (hi : initial ∈ Icc a b) (ht : time ∈ Icc a b)
    (M : ℝ)
    (hb : ∀ r ∈ Icc (min initial time) (max initial time), ‖w.toCoeff (u r)‖ ≤ M) :
    ‖u time‖ ≤ ‖u initial‖*Real.exp ((4*C^2+2*C)*M^2*|time-initial|) := by
  have hs := hu.restrict (le_min hi.1 ht.1) (max_le hi.2 ht.2)
  have hg := FunctionalAnalysis.norm_le_exp_abs_of_hasDerivWithinAt_Icc
    hs.hasDerivWithinAt_interaction (K := (4*C^2+2*C)*M^2) (by
      intro r hr
      calc
        _ ≤ (4*C^2+2*C)*‖nlsToInteraction w u r‖*
            ‖w.toCoeff (nlsToInteraction w u r)‖^2 :=
          norm_nlsInteraction_le_tame w C hC hadd r _
        _ = (4*C^2+2*C)*‖nlsToInteraction w u r‖*‖w.toCoeff (u r)‖^2 := by
          rw [nlsToInteraction, norm_toCoeff_nlsFreeFlow]
        _ ≤ (4*C^2+2*C)*‖nlsToInteraction w u r‖*M^2 := by
          gcongr
          exact hb r hr
        _ = ((4*C^2+2*C)*M^2)*‖nlsToInteraction w u r‖ := by ring)
  simpa only [nlsToInteraction,norm_nlsFreeFlow] using! hg

/-- Every real nonnegative Sobolev order obeys an exponential a priori bound
whose growth rate uses only the raw ℓ¹ bound. -/
theorem sobolev_norm_le_exp
    (s : ℝ) (hs : 0 ≤ s) {a b : ℝ}
    {u : ℝ → WeightedCoeff (SpectralWeight.sobolev s hs).toWeight 1}
    (hu : IsFourierNLSTrajectoryOn (SpectralWeight.sobolev s hs) a b u)
    (initial time : ℝ) (hi : initial ∈ Icc a b) (ht : time ∈ Icc a b)
    (M : ℝ)
    (hb : ∀ r ∈ Icc (min initial time) (max initial time),
      ‖(SpectralWeight.sobolev s hs).toCoeff (u r)‖ ≤ M) :
    ‖u time‖ ≤ ‖u initial‖*Real.exp
      ((4*((2 : ℝ)^s)^2+2*(2 : ℝ)^s)*M^2*|time-initial|) :=
  hu.norm_le_exp_of_unweighted_bound _ (by positivity) (SpectralWeight.sobolev_add_le s hs)
    initial time hi ht M hb

/-- A compatible solution supplies the low norm bound, without a high norm
bound or any ordering between its weight and the original weight. -/
theorem norm_le_exp_of_compatible_trajectory
    {w v : SpectralWeight} {a b : ℝ}
    {u : ℝ → WeightedCoeff w.toWeight 1} {z : ℝ → WeightedCoeff v.toWeight 1}
    (hu : IsFourierNLSTrajectoryOn w a b u) (hz : IsFourierNLSTrajectoryOn v a b z)
    (C : ℝ) (hC : 0 ≤ C) (hadd : ∀ n k : ℤ, w (n+k) ≤ C*(w n+w k))
    (initial time : ℝ) (hi : initial ∈ Ioo a b) (ht : time ∈ Icc a b)
    (hinit : ∀ n : ℤ, (u initial).val n = (z initial).val n)
    (M : ℝ)
    (hb : ∀ r ∈ Icc (min initial time) (max initial time), ‖v.toCoeff (z r)‖ ≤ M) :
    ‖u time‖ ≤ ‖u initial‖*Real.exp ((4*C^2+2*C)*M^2*|time-initial|) := by
  have he := hu.eq_coefficients_of_eq_at hz initial hi hinit
  apply hu.norm_le_exp_of_unweighted_bound C hC hadd initial time ⟨hi.1.le,hi.2.le⟩ ht M
  intro r hr
  have hr' : r ∈ Icc a b :=
    ⟨(le_min hi.1.le ht.1).trans hr.1,hr.2.trans (max_le hi.2.le ht.2)⟩
  have hc : w.toCoeff (u r) = v.toCoeff (z r) := by
    ext n
    simpa only [SpectralWeight.toCoeff_apply] using he r hr' n
  rw [hc]
  exact hb r hr

end IsFourierNLSTrajectoryOn
end NLS.Fourier
