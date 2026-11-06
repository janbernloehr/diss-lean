import NLS.ComplexAnalysis.SimplePoleCauchyInterpolation
import NLS.ComplexAnalysis.AnalyticZeroCount
import Mathlib.Analysis.Normed.Module.Connected

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open scoped ENNReal ComplexConjugate Classical

namespace NLS.ComplexAnalysis



theorem exists_finite_zero_circle_sets (g : ℂ → ℂ) (hg : AnalyticOnNhd ℂ g univ)
    (R : ℕ → ℝ) (hR : ∀ k, 0<R k)
    (hc : ∀ k, ∀ z∈sphere (0 : ℂ) (R k), g z≠0) :
    ∃ s : ℕ → Finset ℂ, ∀ k z, z∈s k ↔ z∈closedBall (0 : ℂ) (R k) ∧ g z=0 := by
  have hfin (k : ℕ) : (closedBall (0 : ℂ) (R k) ∩ g ⁻¹' {0}).Finite := by
    obtain ⟨b,hb⟩ := NormedSpace.sphere_nonempty (E := ℂ) (x := (0 : ℂ)) |>.mpr (hR k).le
    exact finite_analytic_zeros (isCompact_closedBall _ _) (isConnected_closedBall (hR k).le)
      (hg.mono (subset_univ _)) (sphere_subset_closedBall hb) (hc k b hb)
  refine ⟨fun k => (hfin k).toFinset,?_⟩
  intro k z
  simp

/-- The residue expansion has uniform error on every bounded set of
evaluation points avoiding the poles. No lower bound on the denominator
at the evaluation points is required. -/
theorem eventually_simpleQuotientPrincipalParts_error_on_ball
    (f g : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f univ) (hg : AnalyticOnNhd ℂ g univ)
    (hsimple : ∀ a, g a=0 → deriv g a≠0)
    (R : ℕ → ℝ) (hR : ∀ k, 0<R k) (hescape : Tendsto R atTop atTop)
    (hc : ∀ k, ∀ z∈sphere (0 : ℂ) (R k), g z≠0)
    (s : ℕ → Finset ℂ)
    (hs : ∀ k z, z∈s k ↔ z∈closedBall (0 : ℂ) (R k) ∧ g z=0)
    (hsmall : ∀ ε : ℝ, 0<ε → ∀ᶠ k : ℕ in atTop,
      ∀ z∈sphere (0 : ℂ) (R k), ‖f z/g z‖≤ε)
    (A ε : ℝ) (hε : 0<ε) :
    ∀ᶠ k : ℕ in atTop, ∀ w : ℂ, ‖w‖≤A → g w≠0 →
      ‖simpleQuotientPrincipalParts f g (s k) w-f w/g w‖<ε := by
  filter_upwards [hsmall (ε/4) (by positivity),
    hescape.eventually_gt_atTop (2*A+1)] with k hk hbigR w hwA hw
  have hbig : 2*‖w‖+1<R k := by linarith
  have hsub : (s k : Set ℂ)⊆ball (0 : ℂ) (R k) := by
    intro a ha
    obtain ⟨hball,hzero⟩ := (hs k a).mp ha
    exact lt_of_le_of_ne hball (fun he => hc k a he hzero)
  have hwball : w∈ball (0 : ℂ) (R k) := by
    rw [mem_ball,dist_zero_right]
    linarith [norm_nonneg w]
  have hid := circleIntegral_simpleQuotient_cauchy_eq_interpolation_error (hR k)
    (hf.mono (subset_univ _)) (hg.mono (subset_univ _)) (s k) hsub
    (fun a ha => ((hs k a).mp ha).2)
    (fun a ha => hsimple a ((hs k a).mp ha).2)
    (fun a ha hzero => (hs k a).mpr ⟨ha,hzero⟩) hwball hw
  have hfactor : (2*(Real.pi : ℂ)*I)≠0 := by simp [Real.pi_ne_zero]
  have heq : (2*(Real.pi : ℂ)*I)⁻¹ • (∮ z in C((0 : ℂ),R k),f z/g z/(z-w))=
      f w/g w-simpleQuotientPrincipalParts f g (s k) w := by
    rw [smul_eq_mul,hid,inv_mul_cancel_left₀ hfactor]
  have hbound : ∀ z∈sphere (0 : ℂ) (R k), ‖f z/g z/(z-w)‖≤(ε/2)/(R k) := by
    intro z hz
    have hnorm : ‖z‖=R k := by simpa only [mem_sphere,dist_zero_right] using hz
    have hden : R k/2≤‖z-w‖ := by
      have hh := norm_sub_norm_le z w
      rw [hnorm] at hh
      linarith
    rw [norm_div]
    apply (div_le_div₀ (by positivity : 0≤ε/4) (hk z hz) (by linarith [hR k] : 0<R k/2) hden).trans_eq
    field_simp [(hR k).ne']
    norm_num
  have hh := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const (hR k).le hbound
  rw [heq] at hh
  rw [norm_sub_rev]
  apply hh.trans_lt
  have he : R k*((ε/2)/(R k))=ε/2 := by field_simp [(hR k).ne']
  rw [he]
  linarith

/-- The actual circle-ordered simple-pole expansion converges at
every point where the denominator is nonzero. -/
theorem tendsto_simpleQuotientPrincipalParts_of_circle_decay
    (f g : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f univ) (hg : AnalyticOnNhd ℂ g univ)
    (hsimple : ∀ a, g a=0 → deriv g a≠0)
    (R : ℕ → ℝ) (hR : ∀ k, 0<R k) (hescape : Tendsto R atTop atTop)
    (hc : ∀ k, ∀ z∈sphere (0 : ℂ) (R k), g z≠0)
    (s : ℕ → Finset ℂ)
    (hs : ∀ k z, z∈s k ↔ z∈closedBall (0 : ℂ) (R k) ∧ g z=0)
    (hsmall : ∀ ε : ℝ, 0<ε → ∀ᶠ k : ℕ in atTop,
      ∀ z∈sphere (0 : ℂ) (R k), ‖f z/g z‖≤ε)
    (w : ℂ) (hw : g w≠0) :
    Tendsto (fun k => simpleQuotientPrincipalParts f g (s k) w) atTop (𝓝 (f w/g w)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [eventually_simpleQuotientPrincipalParts_error_on_ball f g hf hg hsimple
    R hR hescape hc s hs hsmall ‖w‖ ε hε] with k hk
  simpa only [dist_eq_norm] using hk w le_rfl hw

end NLS.ComplexAnalysis
