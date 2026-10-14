import NLS.ZakharovShabat.SourcePsiFree

/-!
# Why the local contour domain must exclude interior poles

At the free central gap G₀={0}, the function f(z)=z/(z-1/2) is analytic
on an open neighborhood containing both G₀ and the unit circle. It is
real on the real axis and vanishes on G₀, but its normalized standard-root
contour is -1. Thus the wording in Lemma 12.3 cannot mean mere inclusion
of the gap and the curve in an arbitrary open set: the contour deformation
must stay in the numerator's analytic region.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- A numerator with a pole between the central gap and the unit circle. -/
def sourceLocalContourPole (z : ℂ) : ℂ := z/(z-1/2)

theorem sourceLocalContourPole_analytic :
    AnalyticOnNhd ℂ sourceLocalContourPole {(1/2:ℂ)}ᶜ := by
  intro z hz
  exact analyticAt_id.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hz)

theorem sourceLocalContourPole_real (x : ℝ) : (sourceLocalContourPole (x:ℂ)).im = 0 := by
  simp [sourceLocalContourPole,Complex.div_im]

theorem sourceLocalContourPole_zero : sourceLocalContourPole 0 = 0 := by
  simp [sourceLocalContourPole]

theorem sourceLocalContourPole_circle : sphere (0:ℂ) 1 ⊆ {(1/2:ℂ)}ᶜ := by
  intro z hz he
  have h := mem_sphere_zero_iff_norm.mp hz
  rw [mem_singleton_iff.mp he] at h
  norm_num at h

/-- The counterexample's circle avoids every free periodic gap. -/
theorem sourceLocalContourPole_circle_rootDomain (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    sphere (0:ℂ) 1 ⊆ sourceCanonicalRootDomain hp hp1 (0:CoeffPair p) := by
  intro z hz k hzk
  rw [sourcePeriodicSegment_zero_source,mem_singleton_iff] at hzk
  have hn := mem_sphere_zero_iff_norm.mp hz
  rw [hzk] at hn
  by_cases hk : k = 0
  · simp [hk] at hn
  · have ha : (1:ℝ) ≤ |(k:ℝ)| := by exact_mod_cast Int.one_le_abs hk
    have he : Real.pi*|(k:ℝ)| = 1 := by
      simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,
        Complex.norm_intCast] using hn
    nlinarith [Real.pi_gt_three]

/-- The literal integral is nonzero despite the numerator vanishing on the free gap. -/
theorem circleIntegral_sourceLocalContourPole (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    (∮ z in C((0:ℂ),1), sourceLocalContourPole z/sourceStandardRoot hp hp1 (0:CoeffPair p) 0 z) =
      -(2*(Real.pi:ℂ)*I) := by
  have heq : (∮ z in C((0:ℂ),1), sourceLocalContourPole z/sourceStandardRoot hp hp1 (0:CoeffPair p) 0 z) =
      ∮ z in C((0:ℂ),1), -((z-1/2)⁻¹) := by
    apply circleIntegral.integral_congr (by norm_num)
    intro z hz
    have hz0 : z ≠ 0 := by
      intro he
      have h := mem_sphere_zero_iff_norm.mp hz
      simp [he] at h
    have hza : z-1/2 ≠ 0 := sub_ne_zero.mpr (sourceLocalContourPole_circle hz)
    change sourceLocalContourPole z/sourceStandardRoot hp hp1 (0:CoeffPair p) 0 z = -((z-1/2)⁻¹)
    rw [sourceStandardRoot_zero_source hp hp1 0 z]
    simp only [Int.cast_zero,mul_zero,zero_sub,sourceLocalContourPole]
    field_simp
  have ha : (1/2:ℂ) ∈ ball (0:ℂ) 1 := by norm_num [Metric.mem_ball,dist_eq_norm]
  have hn : (fun z : ℂ => -((z-1/2)⁻¹)) = (fun z : ℂ => (-1)*((z-1/2)⁻¹)) := by
    funext z
    ring
  rw [heq,hn,circleIntegral.integral_const_mul,circleIntegral.integral_sub_inv_of_mem_ball ha]
  ring

/-- An open numerator domain containing the gap and the curve alone does not
imply either the bound or real mean-value conclusion in Lemma 12.3. -/
theorem sourceLocalContourPole_counterexample (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ U : Set ℂ, IsOpen U ∧ sourcePeriodicSegment hp hp1 (0:CoeffPair p) 0 ⊆ U ∧
      sphere (0:ℂ) 1 ⊆ U ∧ AnalyticOnNhd ℂ sourceLocalContourPole U ∧
      (∀ x : ℝ, (sourceLocalContourPole (x:ℂ)).im = 0) ∧
      (∀ z ∈ sourcePeriodicSegment hp hp1 (0:CoeffPair p) 0, sourceLocalContourPole z = 0) ∧
      (2*(Real.pi:ℂ)*I)⁻¹ *
        (∮ z in C((0:ℂ),1), sourceLocalContourPole z/sourceStandardRoot hp hp1 (0:CoeffPair p) 0 z) = -1 ∧
      ‖(2*(Real.pi:ℂ))⁻¹ *
        (∮ z in C((0:ℂ),1), sourceLocalContourPole z/sourceStandardRoot hp hp1 (0:CoeffPair p) 0 z)‖ = 1 := by
  have hgap : sourcePeriodicSegment hp hp1 (0:CoeffPair p) 0 = {0} := by
    simpa using sourcePeriodicSegment_zero_source hp hp1 (p := p) 0
  refine ⟨{(1/2:ℂ)}ᶜ,isClosed_singleton.isOpen_compl,?_,sourceLocalContourPole_circle,
    sourceLocalContourPole_analytic,sourceLocalContourPole_real,?_,?_,?_⟩
  · rw [hgap]
    simp
  · intro z hz
    rw [hgap,mem_singleton_iff] at hz
    rw [hz,sourceLocalContourPole_zero]
  · rw [circleIntegral_sourceLocalContourPole]
    have h : (2*(Real.pi:ℂ)*I) ≠ 0 := by simp [Real.pi_ne_zero]
    rw [mul_neg,inv_mul_cancel₀ h]
  · rw [circleIntegral_sourceLocalContourPole]
    have h : (2*(Real.pi:ℂ)) ≠ 0 := by simp [Real.pi_ne_zero]
    rw [mul_neg,← mul_assoc,inv_mul_cancel₀ h,one_mul,norm_neg,norm_I]

end NLS.ZakharovShabat
