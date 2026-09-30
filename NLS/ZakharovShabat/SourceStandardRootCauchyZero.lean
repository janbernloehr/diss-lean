import NLS.ComplexAnalysis.CircleCauchyTransform
import NLS.ZakharovShabat.SourceStandardRootContourAnyCircle

/-!
# The interior Cauchy transform of a reciprocal standard root is zero

Inversion on a sufficiently large enclosing circle gives an analytic
factor vanishing at the inverted origin. Annular Cauchy's theorem moves
that zero integral to every circle enclosing the whole selected gap.
Consequently an additive primitive constant disappears after division
by the selected standard root and interior Cauchy projection.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat

theorem eventually_circleIntegral_normalizedRoot_inv_div_sub_eq_zero
    (t g c z : ℂ) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ < R →
      (∮ w in C(c,R), (normalizedStandardRoot t g w)⁻¹/(w-z)) = 0 := by
  let H : ℂ → ℂ := fun u => u*shiftedInverseRootFactor t g c u/(1-(z-c)*u)
  have hH : AnalyticAt ℂ H 0 :=
    (analyticAt_id.mul (shiftedInverseRootFactor_analyticAt_zero t g c)).div
      (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)) (by simp)
  obtain ⟨ρ,hρ,hHOn⟩ := hH.exists_ball_analyticOnNhd
  let R₀ : ℝ := max (max ‖t-c‖ ‖z-c‖) ρ⁻¹
  have hR₀ : 0 < R₀ := (inv_pos.mpr hρ).trans_le (le_max_right _ _)
  refine ⟨R₀,hR₀,?_⟩
  intro R hR₀R
  have hR : 0 < R := hR₀.trans hR₀R
  have htcR : ‖t-c‖ < R := ((le_max_left _ _).trans (le_max_left _ _)).trans_lt hR₀R
  have hzcR : ‖z-c‖ < R := ((le_max_right _ _).trans (le_max_left _ _)).trans_lt hR₀R
  have hρinvR : ρ⁻¹ < R := (le_max_right _ _).trans_lt hR₀R
  have hρR : 1 < ρ*R := by
    have h := mul_lt_mul_of_pos_left hρinvR hρ
    simpa only [mul_inv_cancel₀ hρ.ne'] using h
  have hRinvρ : R⁻¹ < ρ := by
    rw [show R⁻¹ = 1/R by ring]
    exact (div_lt_iff₀ hR).2 (by nlinarith [hρR])
  have hHdiff : DifferentiableOn ℂ H (closedBall (0:ℂ) |R⁻¹|) := by
    intro u hu
    have hnorm : ‖u‖ ≤ R⁻¹ := by
      simpa only [mem_closedBall,dist_zero_right,abs_of_pos (inv_pos.mpr hR)] using hu
    have huρ : u ∈ ball (0:ℂ) ρ := by
      simpa only [mem_ball,dist_zero_right] using lt_of_le_of_lt hnorm hRinvρ
    exact (hHOn u huρ).differentiableAt.differentiableWithinAt
  have hHdisc : DiffContOnCl ℂ H (ball (0:ℂ) |R⁻¹|) :=
    DiffContOnCl.mk_ball (hHdiff.mono ball_subset_closedBall) hHdiff.continuousOn
  have heq : (∮ w in C(c,R), (normalizedStandardRoot t g w)⁻¹/(w-z)) =
      ∮ w in C(c,R), (-1:ℂ)*((w-c)⁻¹*H ((w-c)⁻¹)) := by
    apply circleIntegral.integral_congr hR.le
    intro w hw
    have hwc : w ≠ c := by
      intro he
      have hd := mem_sphere.mp hw
      rw [he,dist_self] at hd
      linarith
    have hwt : w ≠ t := by
      intro he
      have hd := mem_sphere.mp hw
      rw [he,dist_eq_norm] at hd
      exact (ne_of_lt htcR) hd
    have hwz : w ≠ z := by
      intro he
      have hd := mem_sphere.mp hw
      rw [he,dist_eq_norm] at hd
      exact (ne_of_lt hzcR) hd
    change (normalizedStandardRoot t g w)⁻¹/(w-z) = (-1:ℂ)*((w-c)⁻¹*H ((w-c)⁻¹))
    rw [normalizedRoot_inv_shifted_factor t g c w hwc hwt]
    have hden : 1-(z-c)*(w-c)⁻¹ ≠ 0 := by
      have he : 1-(z-c)*(w-c)⁻¹ = (w-z)/(w-c) := by
        field_simp [sub_ne_zero.mpr hwc]
        ring
      rw [he]
      exact div_ne_zero (sub_ne_zero.mpr hwz) (sub_ne_zero.mpr hwc)
    dsimp only [H]
    field_simp [sub_ne_zero.mpr hwc,sub_ne_zero.mpr hwz,hden]
    ring
  rw [heq,circleIntegral.integral_const_mul,
    circleIntegral_inverse_pulled_holomorphic H c R hR hHdisc]
  simp [H]

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The selected root needs no condition on the other gaps: its reciprocal
Cauchy transform vanishes throughout an enclosing disc. -/
theorem circleIntegral_sourceStandardRoot_inv_div_sub_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (m : ℤ)
    (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hgap : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c r)
    (z : ℂ) (hz : z ∈ ball c r) :
    (∮ w in C(c,r), (sourceStandardRoot hp hp1 ψ m w)⁻¹/(w-z)) = 0 := by
  let t := canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m
  let g := (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m)^2
  obtain ⟨R₀,_,hlarge⟩ := eventually_circleIntegral_normalizedRoot_inv_div_sub_eq_zero t g c z
  let R : ℝ := max r R₀+1
  have hrR : r ≤ R := by dsimp [R]; linarith [le_max_left r R₀]
  have hR₀R : R₀ < R := by dsimp [R]; linarith [le_max_right r R₀]
  let f : ℂ → ℂ := fun w => (sourceStandardRoot hp hp1 ψ m w)⁻¹/(w-z)
  have hdiff (w : ℂ) (hw : w ∉ ball c r) : DifferentiableAt ℂ f w :=
    ((sourceStandardRoot_inv_analyticAt hp hp1 ψ m w (fun h => hw (hgap h))).differentiableAt).div
      (differentiableAt_id.sub_const z) (sub_ne_zero.mpr (fun he => hw (he ▸ hz)))
  have hann : (∮ w in C(c,R), f w) = ∮ w in C(c,r), f w := by
    apply Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
      hr hrR (s := ∅) countable_empty
    · intro w hw
      exact (hdiff w hw.2).continuousAt.continuousWithinAt
    · intro w hw
      exact hdiff w (fun h => hw.1.2 (ball_subset_closedBall h))
  calc
    _ = ∮ w in C(c,R), f w := hann.symm
    _ = 0 := hlarge R hR₀R

theorem circleCauchyTransform_sourceStandardRoot_inv_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (m : ℤ)
    (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hgap : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c r)
    (z : ℂ) (hz : z ∈ ball c r) :
    circleCauchyTransform (fun w => (sourceStandardRoot hp hp1 ψ m w)⁻¹) c r z = 0 := by
  unfold circleCauchyTransform
  rw [circleIntegral_sourceStandardRoot_inv_div_sub_eq_zero hp hp1 ψ m c r hr hgap z hz,mul_zero]

/-- The inner Cauchy projection of a primitive divided by the selected
root is independent of every additive primitive constant. -/
theorem circleCauchyTransform_div_sourceStandardRoot_sub_const
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (m : ℤ)
    (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hgap : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c r)
    (F : ℂ → ℂ) (hF : ContinuousOn F (sphere c r)) (a z : ℂ) (hz : z ∈ ball c r) :
    circleCauchyTransform (fun w => (F w-a)/sourceStandardRoot hp hp1 ψ m w) c r z =
      circleCauchyTransform (fun w => F w/sourceStandardRoot hp hp1 ψ m w) c r z := by
  have hroot : AnalyticOnNhd ℂ (fun w => (sourceStandardRoot hp hp1 ψ m w)⁻¹) (sphere c r) := by
    intro w hw
    exact sourceStandardRoot_inv_analyticAt hp hp1 ψ m w
      (fun h => sphere_disjoint_ball.le_bot ⟨hw,hgap h⟩)
  have hkernel : ContinuousOn (fun w : ℂ => (w-z)⁻¹) (sphere c r) :=
    (continuousOn_id.sub continuousOn_const).inv₀ (fun w hw => sub_ne_zero.mpr
      (fun he => by
        change w = z at he
        exact sphere_disjoint_ball.le_bot ⟨he ▸ hw,hz⟩))
  have hden : ContinuousOn (fun w => (sourceStandardRoot hp hp1 ψ m w)⁻¹/(w-z)) (sphere c r) := by
    simp only [div_eq_mul_inv]
    convert hroot.continuousOn.mul hkernel using 1
    rfl
  have hmain : CircleIntegrable (fun w => (F w/sourceStandardRoot hp hp1 ψ m w)/(w-z)) c r := by
    have hc : ContinuousOn (fun w => (F w/sourceStandardRoot hp hp1 ψ m w)/(w-z)) (sphere c r) := by
      simp only [div_eq_mul_inv]
      convert (hF.mul hroot.continuousOn).mul hkernel using 1
      rfl
    exact hc.circleIntegrable hr.le
  have hconst : CircleIntegrable (fun w => a*((sourceStandardRoot hp hp1 ψ m w)⁻¹/(w-z))) c r := by
    exact (hden.const_mul a).circleIntegrable hr.le
  have heq : (∮ w in C(c,r), ((F w-a)/sourceStandardRoot hp hp1 ψ m w)/(w-z)) =
      (∮ w in C(c,r), (F w/sourceStandardRoot hp hp1 ψ m w)/(w-z)) -
        a*(∮ w in C(c,r), (sourceStandardRoot hp hp1 ψ m w)⁻¹/(w-z)) := by
    calc
      _ = ∮ w in C(c,r), (F w/sourceStandardRoot hp hp1 ψ m w)/(w-z) -
          a*((sourceStandardRoot hp hp1 ψ m w)⁻¹/(w-z)) := by
        apply circleIntegral.integral_congr hr.le
        intro w _
        simp only [div_eq_mul_inv]
        ring
      _ = _ := by
        rw [circleIntegral.integral_sub hmain hconst,
          circleIntegral.integral_const_mul]
  unfold circleCauchyTransform
  rw [heq,circleIntegral_sourceStandardRoot_inv_div_sub_eq_zero hp hp1 ψ m c r hr hgap z hz,
    mul_zero,sub_zero]

end NLS.ZakharovShabat
