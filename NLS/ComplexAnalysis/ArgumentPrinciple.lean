import NLS.ComplexAnalysis.FinitePoleRemoval
import NLS.ComplexAnalysis.AnalyticZeroCount
import Mathlib.Analysis.Normed.Module.Connected

/-!
# The scalar argument principle on a disc

For a function analytic on a neighborhood of a closed disc and nonzero on
its boundary, the integral of its logarithmic derivative is `2πi` times
the sum of its analytic zero orders. The proof removes the finitely many
principal parts and applies Cauchy's theorem to the analytic remainder.
-/

noncomputable section
open Filter Topology Metric
open scoped Classical
namespace NLS.ComplexAnalysis

/-- Interior poles contribute their analytic orders to the contour integral. -/
theorem circleIntegral_logDerivPrincipalParts (f : ℂ → ℂ) (s : Finset ℂ)
    {c : ℂ} {R : ℝ} (hR : 0 < R) (hs : (s : Set ℂ) ⊆ ball c R) :
    (∮ z in C(c, R), logDerivPrincipalParts f s z) =
      (2 * Real.pi * Complex.I) * ∑ a ∈ s, (analyticOrderNatAt f a : ℂ) := by
  have hi : ∀ a ∈ s, CircleIntegrable (fun z : ℂ => (analyticOrderNatAt f a : ℂ)/(z-a)) c R := by
    intro a ha
    apply ContinuousOn.circleIntegrable hR.le
    intro z hz
    have hn : z-a ≠ 0 := sub_ne_zero.mpr (fun he => (ne_of_lt (hs ha)) (he ▸ hz))
    have ha : AnalyticAt ℂ (fun z : ℂ => (analyticOrderNatAt f a : ℂ)/(z-a)) z :=
      analyticAt_const.div (analyticAt_id.sub analyticAt_const) hn
    exact ha.continuousAt.continuousWithinAt
  unfold logDerivPrincipalParts
  rw [circleIntegral.integral_fun_sum hi, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [div_eq_mul_inv, circleIntegral.integral_const_mul,
    circleIntegral.integral_sub_inv_of_mem_ball (hs ha)]
  ring

/-- The scalar argument principle, stated using any finite set covering exactly the disc's zeros. -/
theorem circleIntegral_logDeriv_eq_sum {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hb : ∀ z ∈ sphere c R, f z ≠ 0)
    (hfinite : ∀ z ∈ closedBall c R, analyticOrderAt f z ≠ ⊤)
    (s : Finset ℂ) (hs : (s : Set ℂ) ⊆ ball c R)
    (hcover : ∀ z ∈ closedBall c R, f z = 0 → z ∈ s) :
    (∮ z in C(c, R), logDeriv f z) =
      (2 * Real.pi * Complex.I) * ∑ a ∈ s, (analyticOrderNatAt f a : ℂ) := by
  let g := toMeromorphicNFOn (fun z => logDeriv f z - logDerivPrincipalParts f s z) (closedBall c R)
  have hg : AnalyticOnNhd ℂ g (closedBall c R) := analyticOnNhd_logDeriv_remainder hf hfinite s hcover
  have hzs : ∀ z ∈ sphere c R, z ∉ s := fun z hz hmem => (ne_of_lt (hs hmem)) hz
  have hgi : CircleIntegrable g c R :=
    ContinuousOn.circleIntegrable hR.le (hg.continuousOn.mono sphere_subset_closedBall)
  have hpi : CircleIntegrable (logDerivPrincipalParts f s) c R := by
    apply ContinuousOn.circleIntegrable hR.le
    exact fun z hz => (analyticAt_logDerivPrincipalParts f s (hzs z hz)).continuousAt.continuousWithinAt
  calc
    (∮ z in C(c, R), logDeriv f z) =
        ∮ z in C(c, R), g z + logDerivPrincipalParts f s z := by
      apply circleIntegral.integral_congr hR.le
      intro z hz
      have he := logDeriv_remainder_normalForm_eq hf s (sphere_subset_closedBall hz) (hzs z hz) (hb z hz)
      dsimp [g]
      rw [he, sub_add_cancel]
    _ = (∮ z in C(c, R), g z) + ∮ z in C(c, R), logDerivPrincipalParts f s z :=
      circleIntegral.integral_add hgi hpi
    _ = (2 * Real.pi * Complex.I) * ∑ a ∈ s, (analyticOrderNatAt f a : ℂ) := by
      rw [DiffContOnCl.circleIntegral_eq_zero hR.le (hg.differentiableOn.diffContOnCl_ball subset_rfl),
        zero_add, circleIntegral_logDerivPrincipalParts f s hR hs]

/-- The integral of `f'/f` counts scalar analytic zeros, including repeated zeros. -/
theorem circleIntegral_logDeriv_eq_analyticZeroCount {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hb : ∀ z ∈ sphere c R, f z ≠ 0) :
    (∮ z in C(c, R), logDeriv f z) =
      (2 * Real.pi * Complex.I) * (analyticZeroCount f (closedBall c R) : ℂ) := by
  obtain ⟨b, hbmem⟩ := NormedSpace.sphere_nonempty (E := ℂ) (x := c) |>.mpr hR.le
  have hconn := isConnected_closedBall (x := c) hR.le
  have hfin := finite_analytic_zeros (isCompact_closedBall c R) hconn hf
    (sphere_subset_closedBall hbmem) (hb b hbmem)
  let s := hfin.toFinset
  have hsmem : ∀ z, z ∈ s ↔ z ∈ closedBall c R ∧ f z = 0 := by
    intro z
    simp [s]
  have hs : (s : Set ℂ) ⊆ ball c R := by
    intro z hz
    obtain ⟨hzk, hfz⟩ := (hsmem z).mp hz
    exact lt_of_le_of_ne hzk (fun he => hb z he hfz)
  have hcover : ∀ z ∈ closedBall c R, f z = 0 → z ∈ s :=
    fun z hz hfz => (hsmem z).mpr ⟨hz,hfz⟩
  rw [circleIntegral_logDeriv_eq_sum hR hf hb
    (fun z hz => analyticOrderAt_ne_top_on_connected hconn.isPreconnected hf
      (sphere_subset_closedBall hbmem) (hb b hbmem) hz) s hs hcover,
    analyticZeroCount_eq_sum s (hs.trans ball_subset_closedBall) (fun z hz => hcover z hz.1 hz.2)]
  simp only [Nat.cast_sum]

end NLS.ComplexAnalysis
