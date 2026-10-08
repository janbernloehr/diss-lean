import NLS.Fourier.SmoothFourierNLSFiniteInterval
import NLS.FunctionalAnalysis.CompatibleIntervalExhaustion

/-! # A single smooth Fourier NLS trajectory for all real times

Uniqueness makes the finite-interval solutions agree on overlaps. Gluing
these curves therefore preserves their original coefficient equations and
norm continuity on every finite interval.
-/
noncomputable section
open Set NLS.FunctionalAnalysis NLS.ZakharovShabat
namespace NLS.Fourier

/-- The Fourier trajectory predicate depends only on the curve on its interval. -/
theorem IsFourierNLSTrajectoryOn.congr
    {w : SpectralWeight} {a b : ℝ} {u v : ℝ → WeightedCoeff w.toWeight 1}
    (hu : IsFourierNLSTrajectoryOn w a b u) (he : EqOn u v (Icc a b)) :
    IsFourierNLSTrajectoryOn w a b v := by
  refine ⟨hu.continuous.congr (fun r hr => (he hr).symm),?_⟩
  intro time ht n
  have hd := hu.equation time ht n
  rw [he ht] at hd
  exact hd.congr_of_mem (fun r hr => congrArg (fun q => q.val n) (he hr).symm) ht

/-- One original Fourier trajectory exists for all real times, with the
coefficient equation and norm continuity on every closed finite interval. -/
theorem exists_global_smooth_fourierNLS
    (u₀ : WeightedCoeff SpectralWeight.one.toWeight 1)
    (hall : ∀ s : ℝ, 0 ≤ s → Memℓp (fun n => (Weight.sobolev s n : ℂ)*u₀.val n) 1) :
    ∃ u : ℝ → WeightedCoeff SpectralWeight.one.toWeight 1,
      u 0 = u₀ ∧ ∀ a b : ℝ, IsFourierNLSTrajectoryOn SpectralWeight.one a b u := by
  have hex (n : ℕ) : ∃ u : ℝ → WeightedCoeff SpectralWeight.one.toWeight 1,
      u 0 = u₀ ∧ IsFourierNLSTrajectoryOn SpectralWeight.one (-exhaustionRadius n) (exhaustionRadius n) u := by
    obtain ⟨u,hu0,hu,_⟩ := exists_smooth_fourierNLS_on_interval
      (-exhaustionRadius n) (exhaustionRadius n) 0
      ⟨(neg_neg_iff_pos.mpr (exhaustionRadius_pos n)).le,(exhaustionRadius_pos n).le⟩ u₀ hall
    exact ⟨u,hu0,hu⟩
  choose v hv0 hv using hex
  have hcomp (m n : ℕ) (hmn : m ≤ n) :
      EqOn (v m) (v n) (Icc (-exhaustionRadius m) (exhaustionRadius m)) := by
    have hr := exhaustionRadius_mono hmn
    exact (hv m).eqOn_of_eq_at_closed ((hv n).restrict (neg_le_neg hr) hr) 0
      ⟨(neg_neg_iff_pos.mpr (exhaustionRadius_pos m)).le,(exhaustionRadius_pos m).le⟩
      ((hv0 m).trans (hv0 n).symm)
  let u := exhaustionCurve v
  have he (n : ℕ) : EqOn u (v n) (Icc (-exhaustionRadius n) (exhaustionRadius n)) :=
    exhaustionCurve_eqOn v hcomp n
  refine ⟨u,?_,?_⟩
  · exact (he 0 ⟨by norm_num [exhaustionRadius],by norm_num [exhaustionRadius]⟩).trans (hv0 0)
  · intro a b
    obtain ⟨n,hna,hbn⟩ := exists_exhaustionRadius_cover a b
    exact ((hv n).congr (he n).symm).restrict hna hbn

/-- Closed-interval Fourier trajectories on all intervals are globally norm-continuous. -/
theorem continuous_of_global_fourierNLS
    {w : SpectralWeight} {u : ℝ → WeightedCoeff w.toWeight 1}
    (hu : ∀ a b : ℝ, IsFourierNLSTrajectoryOn w a b u) : Continuous u := by
  apply continuous_iff_continuousAt.mpr
  intro time
  exact (hu (time-1) (time+1)).continuous.continuousAt
    (Icc_mem_nhds (by linarith) (by linarith))

/-- Every original mode satisfies the ordinary scalar time equation at every real time. -/
theorem hasDerivAt_coefficient_of_global_fourierNLS
    {w : SpectralWeight} {u : ℝ → WeightedCoeff w.toWeight 1}
    (hu : ∀ a b : ℝ, IsFourierNLSTrajectoryOn w a b u) (time : ℝ) (n : ℤ) :
    HasDerivAt (fun r => (u r).val n)
      (nlsLinearSymbol n*(u time).val n + (cubicNLS w (u time)).val n) time :=
  ((hu (time-1) (time+1)).equation time ⟨by linarith,by linarith⟩ n).hasDerivAt
    (Icc_mem_nhds (by linarith) (by linarith))

end NLS.Fourier
