import NLS.ZakharovShabat.ClassicalNLSUniqueness

/-! # Quantitative stability of arbitrary classical NLS solutions

The actual PDE difference estimate gives two-sided-in-time L² stability.
A common uniform bound on a compact interval then turns convergence of
initial data into uniform-in-time L² convergence. No finite-gap assumption
is imposed on either solution. Obtaining the common bound for finite-gap
approximations is a separate energy-coercivity step.
-/
noncomputable section
open Set Filter Topology MeasureTheory
namespace NLS.ZakharovShabat

private theorem norm_le_exp_of_deriv_bound (f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (a b K : ℝ)
    (hb : ∀ r ∈ Icc (min a b) (max a b), ‖deriv f r‖ ≤ K*‖f r‖) :
    ‖f b‖ ≤ ‖f a‖ * Real.exp (K*|b-a|) := by
  by_cases hab : a ≤ b
  · have h := norm_le_gronwallBound_of_norm_deriv_right_le
      hf.continuous.continuousOn
      (fun r _ => (hf r).hasDerivAt.hasDerivWithinAt) (le_refl ‖f a‖)
      (ε := 0) (fun r hr => by
        simpa only [add_zero] using hb r
          (by simpa only [min_eq_left hab,max_eq_right hab] using ⟨hr.1,hr.2.le⟩)) b ⟨hab,le_rfl⟩
    simpa only [gronwallBound_ε0,abs_of_nonneg (sub_nonneg.mpr hab)] using h
  · have hba : b ≤ a := le_of_not_ge hab
    have hneg (r : ℝ) : HasDerivAt (fun s => f (-s)) (-deriv f (-r)) r := by
      simpa [Function.comp_def] using! ((hf (-r)).hasDerivAt.comp r (hasDerivAt_neg r))
    have h := norm_le_gronwallBound_of_norm_deriv_right_le
      (hf.continuous.comp continuous_neg).continuousOn
      (fun r _ => (hneg r).hasDerivWithinAt)
      (a := -a) (b := -b) (δ := ‖f a‖) (K := K) (ε := 0) (by simp)
      (fun r hr => by
        simp only [norm_neg,add_zero]
        apply hb (-r)
        simp only [min_eq_right hba,max_eq_left hba,mem_Icc]
        constructor <;> linarith [hr.1,hr.2]) (-b) ⟨by linarith,le_rfl⟩
    have ht : -b - -a = |b-a| := by rw [abs_of_nonpos (sub_nonpos.mpr hba)]; ring
    simpa only [Function.comp_apply,neg_neg,gronwallBound_ε0,ht] using h

/-- Squared physical L² distance grows by at most an explicit exponential,
in either time direction, for any two bounded classical solutions. -/
theorem IsClassicalNLSTrajectory.difference_energy_le_exp
    {u v : ℝ → C(AddCircle (2 : ℝ), ℂ)} (hu : IsClassicalNLSTrajectory u)
    (hv : IsClassicalNLSTrajectory v) (initial time M : ℝ) (hM : 0 ≤ M)
    (hum : ∀ r ∈ Icc (min initial time) (max initial time), ‖u r‖ ≤ M)
    (hvm : ∀ r ∈ Icc (min initial time) (max initial time), ‖v r‖ ≤ M) :
    classicalNLSDifferenceEnergy (u time) (v time) ≤
      classicalNLSDifferenceEnergy (u initial) (v initial) * Real.exp (12*M^2*|time-initial|) := by
  let e := fun r => classicalNLSDifferenceEnergy (u r) (v r)
  have he : Differentiable ℝ e := fun r => (hu.hasDerivAt_difference_energy hv r).differentiableAt
  have hn (r : ℝ) : 0 ≤ e r := sq_nonneg _
  have h := norm_le_exp_of_deriv_bound e he initial time (12*M^2) (fun r hr => by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hn r)] using
      hu.abs_deriv_difference_energy_le hv r M hM (hum r hr) (hvm r hr))
  simpa only [Real.norm_eq_abs,abs_of_nonneg (hn time),abs_of_nonneg (hn initial)] using h

/-- One explicit constant controls the error over a whole symmetric interval. -/
theorem IsClassicalNLSTrajectory.difference_energy_le_exp_on_Icc
    {u v : ℝ → C(AddCircle (2 : ℝ), ℂ)} (hu : IsClassicalNLSTrajectory u)
    (hv : IsClassicalNLSTrajectory v) (T M : ℝ) (hM : 0 ≤ M)
    (hum : ∀ r ∈ Icc (-T) T, ‖u r‖ ≤ M) (hvm : ∀ r ∈ Icc (-T) T, ‖v r‖ ≤ M)
    (time : ℝ) (ht : time ∈ Icc (-T) T) :
    classicalNLSDifferenceEnergy (u time) (v time) ≤
      classicalNLSDifferenceEnergy (u 0) (v 0) * Real.exp (12*M^2*T) := by
  have hT : 0 ≤ T := by linarith [ht.1,ht.2]
  have hsub : Icc (min 0 time) (max 0 time) ⊆ Icc (-T) T := by
    intro r hr
    exact ⟨(le_min (by linarith) ht.1).trans hr.1,hr.2.trans (max_le hT ht.2)⟩
  refine (hu.difference_energy_le_exp hv 0 time M hM (fun r hr => hum r (hsub hr))
    (fun r hr => hvm r (hsub hr))).trans ?_
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply Real.exp_le_exp.mpr
  simp only [sub_zero]
  exact mul_le_mul_of_nonneg_left (abs_le.mpr ht) (by positivity)

/-- Uniformly bounded classical approximations with convergent initial L²
error converge uniformly in time in squared L² distance. -/
theorem IsClassicalNLSTrajectory.tendstoUniformlyOn_difference_energy
    {ι : Type*} {l : Filter ι} {u : ℝ → C(AddCircle (2 : ℝ), ℂ)}
    (hu : IsClassicalNLSTrajectory u) (v : ι → ℝ → C(AddCircle (2 : ℝ), ℂ))
    (hv : ∀ j, IsClassicalNLSTrajectory (v j)) (T M : ℝ) (hM : 0 ≤ M)
    (hum : ∀ r ∈ Icc (-T) T, ‖u r‖ ≤ M)
    (hvm : ∀ᶠ j in l, ∀ r ∈ Icc (-T) T, ‖v j r‖ ≤ M)
    (hinit : Tendsto (fun j => classicalNLSDifferenceEnergy (v j 0) (u 0)) l (𝓝 0)) :
    TendstoUniformlyOn (fun j r => classicalNLSDifferenceEnergy (v j r) (u r))
      (fun _ => 0) l (Icc (-T) T) := by
  have hc := hinit.mul_const (Real.exp (12*M^2*T))
  simp only [zero_mul] at hc
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [hvm,hc.eventually (gt_mem_nhds hε)] with j hj hsmall
  intro time ht
  have hb := (hv j).difference_energy_le_exp_on_Icc hu T M hM hj hum time ht
  have hn : 0 ≤ classicalNLSDifferenceEnergy (v j time) (u time) := sq_nonneg _
  simpa only [dist_zero_left,Real.norm_eq_abs,abs_of_nonneg hn] using hb.trans_lt hsmall

/-- The corresponding physical L² trajectories converge uniformly on the
compact time interval; the initial hypothesis is convergence in L² itself. -/
theorem IsClassicalNLSTrajectory.tendstoUniformlyOn_toLp
    {ι : Type*} {l : Filter ι} {u : ℝ → C(AddCircle (2 : ℝ), ℂ)}
    (hu : IsClassicalNLSTrajectory u) (v : ι → ℝ → C(AddCircle (2 : ℝ), ℂ))
    (hv : ∀ j, IsClassicalNLSTrajectory (v j)) (T M : ℝ) (hM : 0 ≤ M)
    (hum : ∀ r ∈ Icc (-T) T, ‖u r‖ ≤ M)
    (hvm : ∀ᶠ j in l, ∀ r ∈ Icc (-T) T, ‖v j r‖ ≤ M)
    (hinit : Tendsto (fun j => ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (v j 0)) l
      (𝓝 (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (u 0)))) :
    TendstoUniformlyOn (fun j r => ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (v j r))
      (fun r => ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (u r)) l (Icc (-T) T) := by
  have hi : Tendsto (fun j => classicalNLSDifferenceEnergy (v j 0) (u 0)) l (𝓝 0) := by
    simpa only [classicalNLSDifferenceEnergy,map_sub,sub_self,norm_zero,zero_pow (by decide : 2 ≠ 0)]
      using (hinit.sub_const (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (u 0))).norm.pow 2
  have he := Metric.tendstoUniformlyOn_iff.mp
    (hu.tendstoUniformlyOn_difference_energy v hv T M hM hum hvm hi)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [he (ε^2) (sq_pos_of_pos hε)] with j hj
  intro time ht
  have hb := hj time ht
  have hn : 0 ≤ classicalNLSDifferenceEnergy (v j time) (u time) := sq_nonneg _
  simp only [dist_zero_left,Real.norm_eq_abs,abs_of_nonneg hn] at hb
  rw [dist_comm,dist_eq_norm,← map_sub]
  change ‖ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (v j time-u time)‖^2 < ε^2 at hb
  nlinarith [norm_nonneg (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (v j time-u time))]

end NLS.ZakharovShabat
