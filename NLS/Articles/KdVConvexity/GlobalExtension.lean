import NLS.Articles.KdVConvexity.AnalyticSeries

/-! # An analytic contour sum around the entire positive action quadrant

The open domain is constructed from all complex patches on which the actual
terms are analytic with a common quadratic action bound. Local patches at
every nonnegative action therefore yield one ambient analytic extension.
No spectral moment, physical energy identity, or KdV Birkhoff construction
is supplied by these analytic reduction lemmas.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Filter Topology Asymptotics
namespace NLS.Articles.KdVConvexity

/-- The union of all complex open patches with analytic terms and a common
quadratic bound. Its definition does not presuppose that it contains the cone. -/
def globalSeriesDomain (R : ℕ+ → ActionSpace → ℂ) : Set ActionSpace :=
  ⋃₀ {T : Set ActionSpace | IsOpen T ∧
    (∀ n, AnalyticOnNhd ℂ (R n) T) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ T, ∀ n, ‖R n b‖ ≤ C * ‖b n‖ ^ 2}

/-- The constructed domain is open in the complex Hilbert norm topology. -/
theorem isOpen_globalSeriesDomain (R : ℕ+ → ActionSpace → ℂ) :
    IsOpen (globalSeriesDomain R) := by
  exact isOpen_sUnion (fun T hT => hT.1)

/-- The sum is analytic on the entire union of all admissible patches.
The same series is used on overlaps, so no extension is chosen by patch. -/
theorem analyticOnNhd_globalSeriesDomain (R : ℕ+ → ActionSpace → ℂ) :
    AnalyticOnNhd ℂ (fun a => ∑' n, R n a) (globalSeriesDomain R) := by
  intro a ha
  obtain ⟨T, ⟨hT, hR, C, hC, hbound⟩, haT⟩ := mem_sUnion.mp ha
  exact analyticOnNhd_tsum_of_local_quadratic_bound R T hT hR
    (fun b hb => ⟨T, hT, hb, subset_rfl, C, hC, hbound⟩) a haT

/-- Every point of the domain has an actual absolutely convergent sum. -/
theorem summable_norm_on_globalSeriesDomain (R : ℕ+ → ActionSpace → ℂ)
    {a : ActionSpace} (ha : a ∈ globalSeriesDomain R) :
    Summable (fun n => ‖R n a‖) := by
  obtain ⟨T, ⟨_, _, C, _, hbound⟩, haT⟩ := mem_sUnion.mp ha
  exact (summable_norm_of_quadratic_bound a (fun n => R n a) C (hbound a haT)).1

/-- The quadratic action estimate forces the actual series to vanish at zero. -/
theorem tsum_zero_on_globalSeriesDomain (R : ℕ+ → ActionSpace → ℂ)
    (h0 : (0 : ActionSpace) ∈ globalSeriesDomain R) : (∑' n, R n 0) = 0 := by
  obtain ⟨T, ⟨_, _, C, _, hbound⟩, h0T⟩ := mem_sUnion.mp h0
  have hzero (n : ℕ+) : R n 0 = 0 := by
    apply norm_eq_zero.mp
    exact le_antisymm (by simpa using hbound 0 h0T n) (norm_nonneg _)
  simp only [hzero, tsum_zero]

/-- The scalar sum has zero differential at the origin, as a consequence
of its proved quadratic growth, with no Taylor coefficient assumption. -/
theorem hasFDerivAt_tsum_zero (R : ℕ+ → ActionSpace → ℂ)
    (h0 : (0 : ActionSpace) ∈ globalSeriesDomain R) :
    HasFDerivAt (fun a => ∑' n, R n a) (0 : ActionSpace →L[ℂ] ℂ) 0 := by
  obtain ⟨T, ⟨hT, _, C, _, hbound⟩, h0T⟩ := mem_sUnion.mp h0
  have ho : (fun a => ∑' n, R n a) =O[𝓝 (0 : ActionSpace)] (fun a => ‖a‖ ^ 2) := by
    apply Asymptotics.IsBigO.of_bound C
    filter_upwards [hT.mem_nhds h0T] with a ha
    have hs := summable_norm_of_quadratic_bound a (fun n => R n a) C (hbound a ha)
    have hnorm := (norm_tsum_le_tsum_norm hs.1).trans hs.2
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖a‖)] using hnorm
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  simpa only [zero_add, tsum_zero_on_globalSeriesDomain R h0,
    zero_apply, sub_zero] using
      ho.trans_isLittleO (Asymptotics.isLittleO_norm_pow_id (by norm_num : 1 < (2 : ℕ)))

/-- Real nonpositive contour terms have a real nonpositive analytic sum. -/
theorem tsum_real_nonpositive (R : ℕ+ → ActionSpace → ℂ)
    {a : ActionSpace} (ha : a ∈ globalSeriesDomain R)
    (hsign : ∀ n, (R n a).im = 0 ∧ (R n a).re ≤ 0) :
    (∑' n, R n a).im = 0 ∧ (∑' n, R n a).re ≤ 0 := by
  have hs := (summable_norm_on_globalSeriesDomain R ha).of_norm
  constructor
  · rw [Complex.im_tsum hs]
    simp only [fun n => (hsign n).1, tsum_zero]
  · rw [Complex.re_tsum hs]
    exact tsum_nonpos (fun n => (hsign n).2)

/-- Local spectral bounds at every nonnegative action give one analytic
function on a complex open neighborhood of the entire positive ell2 quadrant.

This proves the analytic reduction in Proposition 4.7(ii); constructing the
KdV terms and proving `hlocal` and `hsign` for them remain separate obligations.
In particular, this theorem is not the physical KdV extension assertion. -/
theorem exists_global_analytic_sum_of_local_quadratic_bounds
    (R : ℕ+ → ActionSpace → ℂ)
    (hlocal : ∀ a ∈ positiveQuadrant, ∃ T : Set ActionSpace, IsOpen T ∧ a ∈ T ∧
      (∀ n, AnalyticOnNhd ℂ (R n) T) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ T, ∀ n, ‖R n b‖ ≤ C * ‖b n‖ ^ 2)
    (hsign : ∀ a ∈ positiveQuadrant, ∀ n, (R n a).im = 0 ∧ (R n a).re ≤ 0) :
    ∃ V : Set ActionSpace, IsOpen V ∧ positiveQuadrant ⊆ V ∧
      AnalyticOnNhd ℂ (fun a => ∑' n, R n a) V ∧
      (∀ a ∈ V, Summable (fun n => ‖R n a‖)) ∧
      (∀ a ∈ positiveQuadrant, (∑' n, R n a).im = 0 ∧ (∑' n, R n a).re ≤ 0) ∧
      (∑' n, R n 0) = 0 := by
  have hcone : positiveQuadrant ⊆ globalSeriesDomain R := by
    intro a ha
    obtain ⟨T, hT, haT, hR, C, hC, hb⟩ := hlocal a ha
    exact mem_sUnion.mpr ⟨T, ⟨hT, hR, C, hC, hb⟩, haT⟩
  refine ⟨globalSeriesDomain R, isOpen_globalSeriesDomain R, hcone,
    analyticOnNhd_globalSeriesDomain R, fun _ ha => summable_norm_on_globalSeriesDomain R ha,
    fun a ha => tsum_real_nonpositive R (hcone ha) (hsign a ha), ?_⟩
  apply tsum_zero_on_globalSeriesDomain R (hcone ?_)
  intro n
  simp

end NLS.Articles.KdVConvexity
