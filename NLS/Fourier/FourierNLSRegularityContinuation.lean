import NLS.Fourier.FourierNLSContinuation
import NLS.Fourier.FourierNLSNormGrowth

/-! # Continuation from a compatible low-norm solution

For a weight with an additive estimate, a compatible reference trajectory
bounds the raw norm. The tame Gronwall estimate supplies the high norm bound
required for continuation past either finite endpoint.
-/
noncomputable section
open Set
namespace NLS.Fourier

/-- Endpoint compatibility supplies the raw norm bound on a closed interval. -/
theorem IsFourierNLSTrajectoryOn.norm_le_exp_of_compatible_closed
    {w v : SpectralWeight} {a b : ℝ}
    {u : ℝ → WeightedCoeff w.toWeight 1} {z : ℝ → WeightedCoeff v.toWeight 1}
    (hu : IsFourierNLSTrajectoryOn w a b u) (hz : IsFourierNLSTrajectoryOn v a b z)
    (C : ℝ) (hC : 0 ≤ C) (hadd : ∀ n k : ℤ, w (n+k) ≤ C*(w n+w k))
    (initial time : ℝ) (hi : initial ∈ Icc a b) (ht : time ∈ Icc a b)
    (hinit : ∀ n : ℤ, (u initial).val n = (z initial).val n)
    (M : ℝ) (hb : ∀ r ∈ Icc a b, ‖v.toCoeff (z r)‖ ≤ M) :
    ‖u time‖ ≤ ‖u initial‖*Real.exp ((4*C^2+2*C)*M^2*|time-initial|) := by
  have he := hu.eq_coefficients_of_eq_at_closed hz initial hi hinit
  apply hu.norm_le_exp_of_unweighted_bound C hC hadd initial time hi ht M
  intro r hr
  have hr' := Icc_subset_Icc (le_min hi.1 ht.1) (max_le hi.2 ht.2) hr
  have hc : w.toCoeff (u r) = v.toCoeff (z r) := by
    ext n
    simpa only [SpectralWeight.toCoeff_apply] using he r hr' n
  rw [hc]
  exact hb r hr'

/-- A compatible low-norm reference up to the right endpoint prevents
finite-time failure of a bounded-order Sobolev trajectory there. No high
norm bound is a premise. -/
theorem exists_fourierNLS_extension_of_compatible_Ico
    (w v : SpectralWeight) (a b : ℝ) (hab : a < b)
    (u : ℝ → WeightedCoeff w.toWeight 1) (z : ℝ → WeightedCoeff v.toWeight 1)
    (hu : ∀ c ∈ Ico a b, IsFourierNLSTrajectoryOn w a c u)
    (hz : IsFourierNLSTrajectoryOn v a b z)
    (hinit : ∀ n : ℤ, (u a).val n = (z a).val n)
    (C : ℝ) (hC : 0 ≤ C) (hadd : ∀ n k : ℤ, w (n+k) ≤ C*(w n+w k)) :
    ∃ d > b, ∃ q : ℝ → WeightedCoeff w.toWeight 1,
      IsFourierNLSTrajectoryOn w a d q ∧ EqOn q u (Ico a b) := by
  obtain ⟨M,hb⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (v.toCoeff.continuous.comp_continuousOn hz.continuous)
  let B := ‖u a‖*Real.exp ((4*C^2+2*C)*M^2*(b-a))
  apply exists_fourierNLS_extension_of_bounded_Ico w a b hab u hu B (by dsimp [B]; positivity)
  intro r hr
  have hv := hz.restrict le_rfl hr.2.le
  have h := (hu r hr).norm_le_exp_of_compatible_closed hv C hC hadd a r
    ⟨le_rfl,hr.1⟩ ⟨hr.1,le_rfl⟩ hinit M (fun t ht => hb t ⟨ht.1,ht.2.trans hr.2.le⟩)
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [abs_of_nonneg (sub_nonneg.mpr hr.1)]
  linarith [hr.2]

/-- A compatible reference also prevents loss of high regularity at a finite
left endpoint, with no assumed high norm bound or endpoint value. -/
theorem exists_fourierNLS_extension_of_compatible_Ioc
    (w v : SpectralWeight) (a b : ℝ) (hab : a < b)
    (u : ℝ → WeightedCoeff w.toWeight 1) (z : ℝ → WeightedCoeff v.toWeight 1)
    (hu : ∀ c ∈ Ioc a b, IsFourierNLSTrajectoryOn w c b u)
    (hz : IsFourierNLSTrajectoryOn v a b z)
    (hinit : ∀ n : ℤ, (u b).val n = (z b).val n)
    (C : ℝ) (hC : 0 ≤ C) (hadd : ∀ n k : ℤ, w (n+k) ≤ C*(w n+w k)) :
    ∃ d < a, ∃ q : ℝ → WeightedCoeff w.toWeight 1,
      IsFourierNLSTrajectoryOn w d b q ∧ EqOn q u (Ioc a b) := by
  obtain ⟨M,hb⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (v.toCoeff.continuous.comp_continuousOn hz.continuous)
  let B := ‖u b‖*Real.exp ((4*C^2+2*C)*M^2*(b-a))
  apply exists_fourierNLS_extension_of_bounded_Ioc w a b hab u hu B (by dsimp [B]; positivity)
  intro r hr
  have hv := hz.restrict hr.1.le le_rfl
  have h := (hu r hr).norm_le_exp_of_compatible_closed hv C hC hadd b r
    ⟨hr.2,le_rfl⟩ ⟨le_rfl,hr.2⟩ hinit M (fun t ht => hb t ⟨hr.1.le.trans ht.1,ht.2⟩)
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [abs_of_nonpos (sub_nonpos.mpr hr.2)]
  linarith [hr.1]

/-- At every nonnegative real Sobolev order, a compatible reference on the
closed interval rules out a finite right endpoint of the higher trajectory. -/
theorem exists_sobolev_fourierNLS_extension_of_reference_Ico
    (s : ℝ) (hs : 0 ≤ s) (v : SpectralWeight) (a b : ℝ) (hab : a < b)
    (u : ℝ → WeightedCoeff (SpectralWeight.sobolev s hs).toWeight 1)
    (z : ℝ → WeightedCoeff v.toWeight 1)
    (hu : ∀ c ∈ Ico a b, IsFourierNLSTrajectoryOn (SpectralWeight.sobolev s hs) a c u)
    (hz : IsFourierNLSTrajectoryOn v a b z)
    (hinit : ∀ n : ℤ, (u a).val n = (z a).val n) :
    ∃ d > b, ∃ q : ℝ → WeightedCoeff (SpectralWeight.sobolev s hs).toWeight 1,
      IsFourierNLSTrajectoryOn (SpectralWeight.sobolev s hs) a d q ∧ EqOn q u (Ico a b) :=
  exists_fourierNLS_extension_of_compatible_Ico _ v a b hab u z hu hz hinit _
    (by positivity) (SpectralWeight.sobolev_add_le s hs)

/-- The analogous left-endpoint Sobolev continuation criterion. -/
theorem exists_sobolev_fourierNLS_extension_of_reference_Ioc
    (s : ℝ) (hs : 0 ≤ s) (v : SpectralWeight) (a b : ℝ) (hab : a < b)
    (u : ℝ → WeightedCoeff (SpectralWeight.sobolev s hs).toWeight 1)
    (z : ℝ → WeightedCoeff v.toWeight 1)
    (hu : ∀ c ∈ Ioc a b, IsFourierNLSTrajectoryOn (SpectralWeight.sobolev s hs) c b u)
    (hz : IsFourierNLSTrajectoryOn v a b z)
    (hinit : ∀ n : ℤ, (u b).val n = (z b).val n) :
    ∃ d < a, ∃ q : ℝ → WeightedCoeff (SpectralWeight.sobolev s hs).toWeight 1,
      IsFourierNLSTrajectoryOn (SpectralWeight.sobolev s hs) d b q ∧ EqOn q u (Ioc a b) :=
  exists_fourierNLS_extension_of_compatible_Ioc _ v a b hab u z hu hz hinit _
    (by positivity) (SpectralWeight.sobolev_add_le s hs)

end NLS.Fourier
