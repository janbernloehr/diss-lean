import NLS.Fourier.SmoothFourierNLSContinuation

/-! # Smooth NLS existence on every finite time interval

Conserved mass and energy fix one positive extension length for all partial
solutions. A finite grid therefore reaches any prescribed endpoint.
-/
noncomputable section
open Set NLS.ZakharovShabat NLS.FunctionalAnalysis
open scoped ContDiff
namespace NLS.Fourier

/-- Construct a smooth Fourier trajectory forwards on any prescribed finite interval. -/
theorem exists_smooth_fourierNLS_on_interval_right
    (a b : ℝ) (hab : a ≤ b) (u₀ : WeightedCoeff SpectralWeight.one.toWeight 1)
    (hall : ∀ s : ℝ, 0 ≤ s → Memℓp (fun n => (Weight.sobolev s n : ℂ)*u₀.val n) 1) :
    ∃ u : ℝ → WeightedCoeff SpectralWeight.one.toWeight 1,
      u a = u₀ ∧ IsFourierNLSTrajectoryOn SpectralWeight.one a b u := by
  let uH := fourierNLSHilbertData u₀ (hall 1 (by norm_num))
  let B := nlsConservedBound uH
  have hB : 0 ≤ B := nlsConservedBound_nonneg uH
  let δ := nlsLocalTime B
  have hδ : 0 < δ := nlsLocalTime_pos B hB
  let t (k : ℕ) := min (a+(k : ℝ)*δ) b
  have hta (k : ℕ) : a ≤ t k := le_min (le_add_of_nonneg_right (by positivity)) hab
  have hstep (k : ℕ) : t (k+1) ≤ t k+δ := by
    dsimp [t]
    by_cases hk : a+(k : ℝ)*δ ≤ b
    · rw [min_eq_left hk]
      calc
        _ ≤ a+((k+1 : ℕ) : ℝ)*δ := min_le_left _ _
        _ = _ := by push_cast; ring
    · rw [min_eq_right (le_of_not_ge hk)]
      exact (min_le_right _ _).trans (by linarith)
  have hbound (c : ℝ) (hac : a ≤ c)
      (u : ℝ → WeightedCoeff SpectralWeight.one.toWeight 1) (hu0 : u a = u₀)
      (hu : IsFourierNLSTrajectoryOn SpectralWeight.one a c u) : ‖u c‖ ≤ B := by
    apply hu.norm_le_conserved a ⟨le_rfl,hac⟩ (by simpa only [hu0] using hall) uH
      (by simpa only [hu0] using fourierNLSHilbertData_apply u₀ (hall 1 (by norm_num))) c ⟨hac,le_rfl⟩
  have hgrid (k : ℕ) : ∃ u : ℝ → WeightedCoeff SpectralWeight.one.toWeight 1,
      u a = u₀ ∧ IsFourierNLSTrajectoryOn SpectralWeight.one a (t k) u := by
    induction k with
    | zero =>
      obtain ⟨u,hu0,hu⟩ := exists_fourierNLS_on_uniform_interval SpectralWeight.one ‖u₀‖ (norm_nonneg _) a u₀ le_rfl
      have htime := nlsLocalTime_pos ‖u₀‖ (norm_nonneg u₀)
      refine ⟨u,hu0,?_⟩
      have ht0 : t 0 = a := by simp only [t,Nat.cast_zero,zero_mul,add_zero,min_eq_left hab]
      rw [ht0]
      exact hu.restrict (by linarith) (by linarith)
    | succ k ih =>
      obtain ⟨u,hu0,hu⟩ := ih
      obtain ⟨q,hq,he⟩ := hu.extend_right (hta k) B hB (hbound (t k) (hta k) u hu0 hu)
      exact ⟨q,(he ⟨le_rfl,hta k⟩).trans hu0,hq.restrict le_rfl (hstep k)⟩
  obtain ⟨k,hk⟩ := exists_nat_gt ((b-a)/δ)
  have ht : t k = b := by
    apply min_eq_right
    have h := (div_lt_iff₀ hδ).mp hk
    linarith
  simpa only [ht] using hgrid k


/-- Construct a smooth Fourier trajectory backwards on any prescribed finite interval. -/
theorem exists_smooth_fourierNLS_on_interval_left
    (a b : ℝ) (hab : a ≤ b) (u₀ : WeightedCoeff SpectralWeight.one.toWeight 1)
    (hall : ∀ s : ℝ, 0 ≤ s → Memℓp (fun n => (Weight.sobolev s n : ℂ)*u₀.val n) 1) :
    ∃ u : ℝ → WeightedCoeff SpectralWeight.one.toWeight 1,
      u b = u₀ ∧ IsFourierNLSTrajectoryOn SpectralWeight.one a b u := by
  let uH := fourierNLSHilbertData u₀ (hall 1 (by norm_num))
  let B := nlsConservedBound uH
  have hB : 0 ≤ B := nlsConservedBound_nonneg uH
  let δ := nlsLocalTime B
  have hδ : 0 < δ := nlsLocalTime_pos B hB
  let t (k : ℕ) := max (b-(k : ℝ)*δ) a
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
  have hbound (c : ℝ) (hcb : c ≤ b)
      (u : ℝ → WeightedCoeff SpectralWeight.one.toWeight 1) (hu0 : u b = u₀)
      (hu : IsFourierNLSTrajectoryOn SpectralWeight.one c b u) : ‖u c‖ ≤ B := by
    apply hu.norm_le_conserved b ⟨hcb,le_rfl⟩ (by simpa only [hu0] using hall) uH
      (by simpa only [hu0] using fourierNLSHilbertData_apply u₀ (hall 1 (by norm_num))) c ⟨le_rfl,hcb⟩
  have hgrid (k : ℕ) : ∃ u : ℝ → WeightedCoeff SpectralWeight.one.toWeight 1,
      u b = u₀ ∧ IsFourierNLSTrajectoryOn SpectralWeight.one (t k) b u := by
    induction k with
    | zero =>
      obtain ⟨u,hu0,hu⟩ := exists_fourierNLS_on_uniform_interval SpectralWeight.one ‖u₀‖ (norm_nonneg _) b u₀ le_rfl
      have htime := nlsLocalTime_pos ‖u₀‖ (norm_nonneg u₀)
      refine ⟨u,hu0,?_⟩
      have ht0 : t 0 = b := by simp only [t,Nat.cast_zero,zero_mul,sub_zero,max_eq_left hab]
      rw [ht0]
      exact hu.restrict (by linarith) (by linarith)
    | succ k ih =>
      obtain ⟨u,hu0,hu⟩ := ih
      obtain ⟨q,hq,he⟩ := hu.extend_left (htb k) B hB (hbound (t k) (htb k) u hu0 hu)
      exact ⟨q,(he ⟨htb k,le_rfl⟩).trans hu0,hq.restrict (hstep k) le_rfl⟩
  obtain ⟨k,hk⟩ := exists_nat_gt ((b-a)/δ)
  have ht : t k = a := by
    apply max_eq_right
    have h := (div_lt_iff₀ hδ).mp hk
    linarith
  simpa only [ht] using hgrid k
/-- A smooth datum at any point of a prescribed closed interval gives an
actual Fourier and classical physical solution on the whole interval. -/
theorem exists_smooth_fourierNLS_on_interval
    (a b initial : ℝ) (hi : initial ∈ Icc a b)
    (u₀ : WeightedCoeff SpectralWeight.one.toWeight 1)
    (hall : ∀ s : ℝ, 0 ≤ s → Memℓp (fun n => (Weight.sobolev s n : ℂ)*u₀.val n) 1) :
    ∃ u : ℝ → WeightedCoeff SpectralWeight.one.toWeight 1,
      u initial = u₀ ∧ IsFourierNLSTrajectoryOn SpectralWeight.one a b u ∧
      IsClassicalNLSTrajectoryOn a b (fourierNLSPhysicalCurve SpectralWeight.one u) := by
  obtain ⟨v,hv0,hv⟩ := exists_smooth_fourierNLS_on_interval_left a initial hi.1 u₀ hall
  obtain ⟨z,hz0,hz⟩ := exists_smooth_fourierNLS_on_interval_right initial b hi.2 u₀ hall
  let u := joinClosedCurves initial v z
  have hu0 : u initial = u₀ := (joinClosedCurves_of_le initial v z le_rfl).trans hv0
  have hu : IsFourierNLSTrajectoryOn SpectralWeight.one a b u :=
    hv.join hz hi.1 hi.2 (hv0.trans hz0.symm)
  exact ⟨u,hu0,hu,hu.isClassical_physical_of_all_sobolev initial hi (by simpa only [hu0] using hall)⟩

/-- Every smooth period-one physical initial function has a classical solution
on any prescribed finite closed interval, with the initial time anywhere in it. -/
theorem exists_classicalNLS_on_interval_of_smooth_periodic
    (a b initial : ℝ) (hi : initial ∈ Icc a b)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1) :
    ∃ u : ℝ → C(AddCircle (2 : ℝ), ℂ),
      (fun x : ℝ => u initial (x : AddCircle (2 : ℝ))) = f ∧
      IsClassicalNLSTrajectoryOn a b u := by
  obtain ⟨z,hz0,_,hz⟩ := exists_smooth_fourierNLS_on_interval a b initial hi
    (smoothPeriodOneFourierData f hf hp) (smoothPeriodOneFourierData_all_sobolev f hf hp)
  refine ⟨fourierNLSPhysicalCurve SpectralWeight.one z,?_,hz⟩
  simpa only [fourierNLSPhysicalCurve_apply,hz0] using periodOneSynthesis_smoothPeriodOneFourierData f hf hp

end NLS.Fourier
