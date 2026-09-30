import NLS.ComplexAnalysis.ParametricCircleIntegralHigher
import NLS.FunctionalAnalysis.CircleIntegral
import Mathlib.Analysis.Calculus.DSlope

/-!
# Cauchy transforms and annular decomposition

The Cauchy transform of a circle density is analytic away from that
circle. A function analytic on a closed annulus is the outer Cauchy
transform minus the inner one on its interior. This separates the
contribution of an enclosed spectral gap without requiring that the
gap be a pole or a removable point singularity.
-/

noncomputable section
open Set Complex Filter Topology Metric
namespace NLS.ComplexAnalysis

/-- The Cauchy transform with the usual `1/(2πi)` normalization. -/
def circleCauchyTransform (f : ℂ → ℂ) (c : ℂ) (R : ℝ) (z : ℂ) : ℂ :=
  (2*Real.pi*I : ℂ)⁻¹ * ∮ w in C(c,R), f w/(w-z)

/-- The circle Cauchy transform is analytic on both components of the
circle complement whenever the density is analytic near the circle. -/
theorem analyticOnNhd_circleCauchyTransform (f : ℂ → ℂ) (c : ℂ) (R : ℝ)
    (hR : 0 ≤ R) (hf : AnalyticOnNhd ℂ f (sphere c R)) :
    AnalyticOnNhd ℂ (circleCauchyTransform f c R) (sphere c R)ᶜ := by
  let D : Set (ℂ × ℂ) := {t | AnalyticAt ℂ f t.1 ∧ t.1 ≠ t.2}
  let F : ℂ × ℂ → ℂ := fun t => f t.1/(t.1-t.2)
  have hD : IsOpen D :=
    ((isOpen_analyticAt ℂ f).preimage continuous_fst).inter
      (isOpen_ne_fun continuous_fst continuous_snd)
  have hF : AnalyticOnNhd ℂ F D := by
    intro t ht
    exact (ht.1.comp analyticAt_fst).div (analyticAt_fst.sub analyticAt_snd)
      (sub_ne_zero.mpr ht.2)
  have hcircle : ∀ z ∈ (sphere c R)ᶜ, ∀ w ∈ sphere c R, (w,z) ∈ D := by
    intro z hz w hw
    refine ⟨hf w hw, ?_⟩
    change w ≠ z
    exact fun he => hz (he ▸ hw)
  have hraw := analyticOnNhd_circleIntegral_of_jointAnalytic F hD hF c R hR
    isClosed_sphere.isOpen_compl hcircle
  intro z hz
  exact analyticAt_const.mul (hraw z hz)

/-- The Cauchy kernel has zero integral when its pole is outside the
closed disc. -/
theorem circleIntegral_inv_sub_eq_zero_of_notMem_closedBall
    (c w : ℂ) (R : ℝ) (hR : 0 ≤ R) (hw : w ∉ closedBall c R) :
    (∮ z in C(c,R), (z-w)⁻¹) = 0 := by
  have hd : DifferentiableOn ℂ (fun z : ℂ => (z-w)⁻¹) (closedBall c R) := by
    intro z hz
    exact ((differentiableAt_id.sub_const w).inv
      (sub_ne_zero.mpr (fun h => hw (h ▸ hz)))).differentiableWithinAt
  exact (DiffContOnCl.mk_ball (hd.mono ball_subset_closedBall) hd.continuousOn).circleIntegral_eq_zero hR

/-- Cauchy's formula on an annulus, with both boundary terms and their
orientations. No hypothesis is made about the function inside the hole. -/
theorem circleCauchyTransform_outer_sub_inner (f : ℂ → ℂ) (c : ℂ)
    (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R \ ball c r))
    (z : ℂ) (hz : z ∈ ball c R \ closedBall c r) :
    circleCauchyTransform f c R z-circleCauchyTransform f c r z = f z := by
  have hR : 0 < R := hr.trans_le hrR
  have hsub : ball c R \ closedBall c r ⊆ closedBall c R \ ball c r := by
    intro w hw
    exact ⟨ball_subset_closedBall hw.1, fun h => hw.2 (ball_subset_closedBall h)⟩
  have hA : closedBall c R \ ball c r ∈ 𝓝 z :=
    mem_of_superset ((isOpen_ball.sdiff isClosed_closedBall).mem_nhds hz) hsub
  have hds : ContinuousOn (dslope f z) (closedBall c R \ ball c r) :=
    (continuousOn_dslope hA).2 ⟨hf.continuousOn, (hf z (hsub hz)).differentiableAt⟩
  have heq := Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
    hr hrR (countable_singleton z) hds (by
      intro w hw
      apply (differentiableAt_dslope_of_ne (by simpa only [mem_singleton_iff] using hw.2)).2
      exact (hf w (hsub hw.1)).differentiableAt)
  have hneR : ∀ w ∈ sphere c R, w ≠ z := fun w hw =>
    fun he => sphere_disjoint_ball.le_bot ⟨he ▸ hw, hz.1⟩
  have hner : ∀ w ∈ sphere c r, w ≠ z := fun w hw =>
    fun he => hz.2 (he ▸ sphere_subset_closedBall hw)
  have hcircleR : sphere c R ⊆ closedBall c R \ ball c r := by
    intro w hw
    refine ⟨sphere_subset_closedBall hw, ?_⟩
    have hwR := mem_sphere.mp hw
    intro hwr
    have hwr := mem_ball.mp hwr
    linarith
  have hcircler : sphere c r ⊆ closedBall c R \ ball c r := by
    intro w hw
    refine ⟨mem_closedBall.mpr ((mem_sphere.mp hw).le.trans hrR), ?_⟩
    exact fun h => sphere_disjoint_ball.le_bot ⟨hw,h⟩
  have hrewrite (ρ : ℝ) (hρ : 0 ≤ ρ)
      (hcircle : sphere c ρ ⊆ closedBall c R \ ball c r)
      (hne : ∀ w ∈ sphere c ρ, w ≠ z) :
      (∮ w in C(c,ρ), dslope f z w) =
        (∮ w in C(c,ρ), f w/(w-z)) -
          f z*(∮ w in C(c,ρ), (w-z)⁻¹) := by
    have hk : ContinuousOn (fun w : ℂ => f w/(w-z)) (sphere c ρ) :=
      (hf.continuousOn.mono hcircle).div (continuousOn_id.sub continuousOn_const)
        (fun w hw => sub_ne_zero.mpr (hne w hw))
    have hp : ContinuousOn (fun w : ℂ => f z*(w-z)⁻¹) (sphere c ρ) :=
      continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).inv₀
        (fun w hw => sub_ne_zero.mpr (hne w hw)))
    calc
      _ = ∮ w in C(c,ρ), f w/(w-z)-f z*(w-z)⁻¹ := by
        apply circleIntegral.integral_congr hρ
        intro w hw
        rw [dslope_of_ne _ (hne w hw)]
        simp only [slope, vsub_eq_sub, smul_eq_mul, div_eq_mul_inv]
        ring
      _ = _ := by rw [circleIntegral.integral_sub (hk.circleIntegrable hρ)
        (hp.circleIntegrable hρ), circleIntegral.integral_const_mul]
  rw [hrewrite R hR.le hcircleR hneR, hrewrite r hr.le hcircler hner,
    circleIntegral.integral_sub_inv_of_mem_ball hz.1,
    circleIntegral_inv_sub_eq_zero_of_notMem_closedBall c z r hr.le hz.2,
    mul_zero, sub_zero] at heq
  have hπ : (2*Real.pi*I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  unfold circleCauchyTransform
  have hdiff : (∮ w in C(c,R), f w/(w-z))-(∮ w in C(c,r), f w/(w-z)) =
      (2*Real.pi*I : ℂ)*f z := by linear_combination heq
  rw [← mul_sub, hdiff, ← mul_assoc, inv_mul_cancel₀ hπ, one_mul]

end NLS.ComplexAnalysis
