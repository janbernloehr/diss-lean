import NLS.Fourier.FourierNLSRegularityContinuation

/-! # Higher-weight existence on a reference solution's full interval

Compactness bounds the reference's raw norm. Tame growth bounds every
partial higher-weight solution by one constant, so finitely many uniform
extensions cover the prescribed interval, without a maximal-solution premise.
-/
noncomputable section
open Set
namespace NLS.Fourier

/-- Construct the higher-weight solution forward across the full reference interval. -/
theorem exists_fourierNLS_on_reference_interval_right
    (w v : SpectralWeight) (a b : ℝ) (hab : a ≤ b)
    (z : ℝ → WeightedCoeff v.toWeight 1) (hz : IsFourierNLSTrajectoryOn v a b z)
    (u₀ : WeightedCoeff w.toWeight 1) (hinit : ∀ n : ℤ, u₀.val n = (z a).val n)
    (C : ℝ) (hC : 0 ≤ C) (hadd : ∀ n k : ℤ, w (n+k) ≤ C*(w n+w k)) :
    ∃ u : ℝ → WeightedCoeff w.toWeight 1, u a = u₀ ∧ IsFourierNLSTrajectoryOn w a b u := by
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (v.toCoeff.continuous.comp_continuousOn hz.continuous)
  let B := ‖u₀‖*Real.exp ((4*C^2+2*C)*M^2*(b-a))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let δ := nlsLocalTime B
  have hδ : 0 < δ := nlsLocalTime_pos B hB
  let t (k : ℕ) := min (a+(k : ℝ)*δ) b
  have hta (k : ℕ) : a ≤ t k := le_min (le_add_of_nonneg_right (by positivity)) hab
  have htb (k : ℕ) : t k ≤ b := min_le_right _ _
  have hstep (k : ℕ) : t (k+1) ≤ t k+δ := by
    dsimp [t]
    by_cases hk : a+(k : ℝ)*δ ≤ b
    · rw [min_eq_left hk]
      calc
        _ ≤ a+((k+1 : ℕ) : ℝ)*δ := min_le_left _ _
        _ = _ := by push_cast; ring
    · rw [min_eq_right (le_of_not_ge hk)]
      exact (min_le_right _ _).trans (by linarith)
  have hbound (c : ℝ) (hac : a ≤ c) (hcb : c ≤ b)
      (u : ℝ → WeightedCoeff w.toWeight 1) (hu0 : u a = u₀)
      (hu : IsFourierNLSTrajectoryOn w a c u) : ‖u c‖ ≤ B := by
    have h := hu.norm_le_exp_of_compatible_closed (hz.restrict le_rfl hcb) C hC hadd a c
      ⟨le_rfl,hac⟩ ⟨hac,le_rfl⟩ (by simpa only [hu0] using hinit) M
      (fun r hr => hM r ⟨hr.1,hr.2.trans hcb⟩)
    rw [hu0] at h
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [abs_of_nonneg (sub_nonneg.mpr hac)]
    linarith
  have hgrid (k : ℕ) : ∃ u : ℝ → WeightedCoeff w.toWeight 1,
      u a = u₀ ∧ IsFourierNLSTrajectoryOn w a (t k) u := by
    induction k with
    | zero =>
      obtain ⟨u,hu0,hu⟩ := exists_fourierNLS_on_uniform_interval w ‖u₀‖ (norm_nonneg _) a u₀ le_rfl
      have htime := nlsLocalTime_pos ‖u₀‖ (norm_nonneg u₀)
      refine ⟨u,hu0,?_⟩
      have ht0 : t 0 = a := by simp only [t,Nat.cast_zero,zero_mul,add_zero,min_eq_left hab]
      rw [ht0]
      exact hu.restrict (by linarith) (by linarith)
    | succ k ih =>
      obtain ⟨u,hu0,hu⟩ := ih
      obtain ⟨q,hq,he⟩ := hu.extend_right (hta k) B hB (hbound (t k) (hta k) (htb k) u hu0 hu)
      exact ⟨q,(he ⟨le_rfl,hta k⟩).trans hu0,hq.restrict le_rfl (hstep k)⟩
  obtain ⟨k,hk⟩ := exists_nat_gt ((b-a)/δ)
  have ht : t k = b := by
    apply min_eq_right
    have h := (div_lt_iff₀ hδ).mp hk
    linarith
  simpa only [ht] using hgrid k

/-- Construct the higher-weight solution backward across the full reference interval. -/
theorem exists_fourierNLS_on_reference_interval_left
    (w v : SpectralWeight) (a b : ℝ) (hab : a ≤ b)
    (z : ℝ → WeightedCoeff v.toWeight 1) (hz : IsFourierNLSTrajectoryOn v a b z)
    (u₀ : WeightedCoeff w.toWeight 1) (hinit : ∀ n : ℤ, u₀.val n = (z b).val n)
    (C : ℝ) (hC : 0 ≤ C) (hadd : ∀ n k : ℤ, w (n+k) ≤ C*(w n+w k)) :
    ∃ u : ℝ → WeightedCoeff w.toWeight 1, u b = u₀ ∧ IsFourierNLSTrajectoryOn w a b u := by
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (v.toCoeff.continuous.comp_continuousOn hz.continuous)
  let B := ‖u₀‖*Real.exp ((4*C^2+2*C)*M^2*(b-a))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let δ := nlsLocalTime B
  have hδ : 0 < δ := nlsLocalTime_pos B hB
  let t (k : ℕ) := max (b-(k : ℝ)*δ) a
  have hta (k : ℕ) : a ≤ t k := le_max_right _ _
  have htb (k : ℕ) : t k ≤ b := max_le (sub_le_self _ (by positivity)) hab
  have hstep (k : ℕ) : t k-δ ≤ t (k+1) := by
    dsimp [t]
    by_cases hk : a ≤ b-(k : ℝ)*δ
    · rw [max_eq_left hk]
      calc
        _ = b-((k+1 : ℕ) : ℝ)*δ := by push_cast; ring
        _ ≤ _ := le_max_left _ _
    · rw [max_eq_right (le_of_not_ge hk)]
      exact (by linarith : a-δ ≤ a).trans (le_max_right _ _)
  have hbound (c : ℝ) (hac : a ≤ c) (hcb : c ≤ b)
      (u : ℝ → WeightedCoeff w.toWeight 1) (hu0 : u b = u₀)
      (hu : IsFourierNLSTrajectoryOn w c b u) : ‖u c‖ ≤ B := by
    have h := hu.norm_le_exp_of_compatible_closed (hz.restrict hac le_rfl) C hC hadd b c
      ⟨hcb,le_rfl⟩ ⟨le_rfl,hcb⟩ (by simpa only [hu0] using hinit) M
      (fun r hr => hM r ⟨hac.trans hr.1,hr.2⟩)
    rw [hu0] at h
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [abs_of_nonpos (sub_nonpos.mpr hcb)]
    linarith
  have hgrid (k : ℕ) : ∃ u : ℝ → WeightedCoeff w.toWeight 1,
      u b = u₀ ∧ IsFourierNLSTrajectoryOn w (t k) b u := by
    induction k with
    | zero =>
      obtain ⟨u,hu0,hu⟩ := exists_fourierNLS_on_uniform_interval w ‖u₀‖ (norm_nonneg _) b u₀ le_rfl
      have htime := nlsLocalTime_pos ‖u₀‖ (norm_nonneg u₀)
      refine ⟨u,hu0,?_⟩
      have ht0 : t 0 = b := by simp only [t,Nat.cast_zero,zero_mul,sub_zero,max_eq_left hab]
      rw [ht0]
      exact hu.restrict (by linarith) (by linarith)
    | succ k ih =>
      obtain ⟨u,hu0,hu⟩ := ih
      obtain ⟨q,hq,he⟩ := hu.extend_left (htb k) B hB (hbound (t k) (hta k) (htb k) u hu0 hu)
      exact ⟨q,(he ⟨htb k,le_rfl⟩).trans hu0,hq.restrict (hstep k) le_rfl⟩
  obtain ⟨k,hk⟩ := exists_nat_gt ((b-a)/δ)
  have ht : t k = a := by
    apply max_eq_right
    have h := (div_lt_iff₀ hδ).mp hk
    linarith
  simpa only [ht] using hgrid k

/-- Every compatible higher-weight initial value extends over the full
reference interval, with exactly the same coefficients there. The initial
time may be an endpoint; no higher-weight trajectory is assumed. -/
theorem exists_fourierNLS_on_reference_interval
    (w v : SpectralWeight) (a b initial : ℝ) (hi : initial ∈ Icc a b)
    (z : ℝ → WeightedCoeff v.toWeight 1) (hz : IsFourierNLSTrajectoryOn v a b z)
    (u₀ : WeightedCoeff w.toWeight 1) (hinit : ∀ n : ℤ, u₀.val n = (z initial).val n)
    (C : ℝ) (hC : 0 ≤ C) (hadd : ∀ n k : ℤ, w (n+k) ≤ C*(w n+w k)) :
    ∃ u : ℝ → WeightedCoeff w.toWeight 1, u initial = u₀ ∧
      IsFourierNLSTrajectoryOn w a b u ∧
      ∀ time ∈ Icc a b, ∀ n : ℤ, (u time).val n = (z time).val n := by
  obtain ⟨l,hl0,hl⟩ := exists_fourierNLS_on_reference_interval_left w v a initial hi.1 z
    (hz.restrict le_rfl hi.2) u₀ hinit C hC hadd
  obtain ⟨r,hr0,hr⟩ := exists_fourierNLS_on_reference_interval_right w v initial b hi.2 z
    (hz.restrict hi.1 le_rfl) u₀ hinit C hC hadd
  let u := FunctionalAnalysis.joinClosedCurves initial l r
  have hu0 : u initial = u₀ := by simp only [u,FunctionalAnalysis.joinClosedCurves_of_le _ _ _ le_rfl,hl0]
  have hu : IsFourierNLSTrajectoryOn w a b u := hl.join hr hi.1 hi.2 (hl0.trans hr0.symm)
  exact ⟨u,hu0,hu,hu.eq_coefficients_of_eq_at_closed hz initial hi (by simpa only [hu0] using hinit)⟩

/-- Persistence at every nonnegative real Sobolev order on the exact full
reference interval, without ordering the reference and Sobolev weights. -/
theorem exists_sobolev_fourierNLS_on_reference_interval
    (s : ℝ) (hs : 0 ≤ s) (v : SpectralWeight) (a b initial : ℝ) (hi : initial ∈ Icc a b)
    (z : ℝ → WeightedCoeff v.toWeight 1) (hz : IsFourierNLSTrajectoryOn v a b z)
    (u₀ : WeightedCoeff (SpectralWeight.sobolev s hs).toWeight 1)
    (hinit : ∀ n : ℤ, u₀.val n = (z initial).val n) :
    ∃ u : ℝ → WeightedCoeff (SpectralWeight.sobolev s hs).toWeight 1, u initial = u₀ ∧
      IsFourierNLSTrajectoryOn (SpectralWeight.sobolev s hs) a b u ∧
      ∀ time ∈ Icc a b, ∀ n : ℤ, (u time).val n = (z time).val n :=
  exists_fourierNLS_on_reference_interval _ v a b initial hi z hz u₀ hinit _
    (by positivity) (SpectralWeight.sobolev_add_le s hs)

end NLS.Fourier
