import NLS.ZakharovShabat.SourceStandardRootInverseCorrection
import NLS.ZakharovShabat.SourcePsiNearFreeCollapsedGap

/-!
# A complex-gap contour estimate for the selected standard root

The fixed-circle integral is compared with the collapsed-gap Cauchy
residue. The error is quadratic in the complex periodic gap. This
replaces the real-gap maximum principle when the source is complex.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The weighted selected-root contour on a near-free complex gap is
the collapsed Cauchy contribution plus a quadratic-gap error. -/
theorem norm_nearFree_complexGap_weighted_circle_le
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (m : ℤ) (σ : ℂ)
    (hmid : ‖sourceStandardRootMidpoint hp hp1 ψ m -
      (Real.pi : ℂ)*m‖ ≤ Real.pi/64)
    (hgap : ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖ ≤ Real.pi/32)
    (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f
      (closedBall ((Real.pi : ℂ)*m) (Real.pi/8)))
    (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ z ∈ closedBall ((Real.pi : ℂ)*m) (Real.pi/8),
      ‖f z‖ ≤ M) :
    ‖(2*(Real.pi:ℂ))⁻¹ *
      (∮ z in C((Real.pi : ℂ)*m,Real.pi/8),
        ((σ-z)/sourceStandardRoot hp hp1 ψ m z)*f z)‖ ≤
      ‖sourceStandardRootMidpoint hp hp1 ψ m-σ‖ *
        ‖f (sourceStandardRootMidpoint hp hp1 ψ m)‖ +
      (Real.pi/8)*
        (‖σ-(Real.pi : ℂ)*m‖+Real.pi/8)*M*
          (‖sourcePeriodicGapDisplacement hp hp1 ψ m‖^2/
            (2*(Real.pi/16)^3)) := by
  let c : ℂ := (Real.pi : ℂ)*m
  let R : ℝ := Real.pi/8
  let τ := sourceStandardRootMidpoint hp hp1 ψ m
  let w : ℂ → ℂ := sourceStandardRoot hp hp1 ψ m
  let P : ℂ → ℂ := fun z => (σ-z)*f z
  let g₀ : ℂ → ℂ := fun z => ((σ-z)/(τ-z))*f z
  let g₁ : ℂ → ℂ := fun z =>
    P z*((w z)⁻¹-(τ-z)⁻¹)
  have hR : 0 < R := by dsimp [R]; positivity
  have hτball : τ ∈ ball c R := by
    rw [mem_ball,dist_eq_norm]
    exact hmid.trans_lt (by dsimp [R]; nlinarith [Real.pi_pos])
  have hfR : AnalyticOnNhd ℂ f (closedBall c R) := hf
  have hfcont : ContinuousOn f (sphere c R) :=
    hfR.continuousOn.mono sphere_subset_closedBall
  have hPcont : ContinuousOn P (sphere c R) :=
    (continuousOn_const.sub continuousOn_id).mul hfcont
  have hτne (z : ℂ) (hz : z ∈ sphere c R) : τ ≠ z := by
    intro he
    have hs := mem_sphere.mp hz
    rw [← he] at hs
    exact (ne_of_lt (mem_ball.mp hτball)) hs
  have hlinCont : ContinuousOn (fun z : ℂ => (τ-z)⁻¹)
      (sphere c R) := by
    apply ContinuousOn.inv₀
    · exact continuousOn_const.sub continuousOn_id
    · intro z hz
      exact sub_ne_zero.mpr (hτne z hz)
  have hseg : sourcePeriodicSegment hp hp1 ψ m ⊆ ball c R :=
    sourcePeriodicSegment_subset_free_eighth_ball hp hp1 ψ m hmid hgap
  have havoid (z : ℂ) (hz : z ∈ sphere c R) :
      z ∉ sourcePeriodicSegment hp hp1 ψ m := by
    intro hzin
    exact (ne_of_lt (mem_ball.mp (hseg hzin))) (mem_sphere.mp hz)
  have hrootCont : ContinuousOn (fun z => (w z)⁻¹) (sphere c R) := by
    intro z hz
    exact (sourceStandardRoot_inv_analyticAt hp hp1 ψ m z
      (havoid z hz)).continuousAt.continuousWithinAt
  have h₀int : CircleIntegrable g₀ c R := by
    have hcont : ContinuousOn g₀ (sphere c R) := by
      change ContinuousOn (fun z => ((σ-z)*(τ-z)⁻¹)*f z) (sphere c R)
      exact ((continuousOn_const.sub continuousOn_id).mul hlinCont).mul hfcont
    exact hcont.circleIntegrable hR.le
  have h₁int : CircleIntegrable g₁ c R :=
    (hPcont.mul (hrootCont.sub hlinCont)).circleIntegrable hR.le
  have hsame :
      (∮ z in C(c,R), ((σ-z)/(w z))*f z) =
        (∮ z in C(c,R), g₀ z) + (∮ z in C(c,R), g₁ z) := by
    rw [← circleIntegral.integral_add h₀int h₁int]
    apply circleIntegral.integral_congr hR.le
    intro z hz
    have hw : w z ≠ 0 :=
      sourceStandardRoot_ne_zero_off_segment hp hp1 ψ m z
        (havoid z hz)
    have hd : τ-z ≠ 0 := sub_ne_zero.mpr (hτne z hz)
    dsimp [g₀,g₁,P]
    field_simp [hw,hd]
    ring
  have hCauchy : (∮ z in C(c,R), g₀ z) =
      (2*(Real.pi:ℂ)*I)*(τ-σ)*f τ := by
    change (∮ z in C(c,R), ((σ-z)/(τ-z))*f z) = _
    exact circleIntegral_collapsedGap_ratio_of_mem_ball
      c τ σ R hR hτball f hfR
  have hcorr : ‖∮ z in C(c,R), g₁ z‖ ≤
      2*Real.pi*R*((‖σ-c‖+R)*M*
        (‖sourcePeriodicGapDisplacement hp hp1 ψ m‖^2/
          (2*(Real.pi/16)^3))) := by
    exact norm_circleIntegral_sourceStandardRoot_inverse_correction_freeCircle_le
      hp hp1 ψ m σ hmid hgap f M hM
        (fun z hz => hbound z (sphere_subset_closedBall hz))
  have hπ : (2*(Real.pi:ℂ)) ≠ 0 := by simp [Real.pi_ne_zero]
  rw [hsame,hCauchy]
  calc
    ‖(2*(Real.pi:ℂ))⁻¹ *
        ((2*(Real.pi:ℂ)*I)*(τ-σ)*f τ +
          ∮ z in C(c,R), g₁ z)‖ ≤
      ‖(2*(Real.pi:ℂ))⁻¹ *
        ((2*(Real.pi:ℂ)*I)*(τ-σ)*f τ)‖ +
      ‖(2*(Real.pi:ℂ))⁻¹ *
        (∮ z in C(c,R), g₁ z)‖ := by
          rw [mul_add]
          exact norm_add_le _ _
    _ ≤ ‖τ-σ‖*‖f τ‖ +
        R*((‖σ-c‖+R)*M*
          (‖sourcePeriodicGapDisplacement hp hp1 ψ m‖^2/
            (2*(Real.pi/16)^3))) := by
      have hmain : ‖(2*(Real.pi:ℂ))⁻¹ *
          ((2*(Real.pi:ℂ)*I)*(τ-σ)*f τ)‖ =
          ‖τ-σ‖*‖f τ‖ := by
        have heq : (2*(Real.pi:ℂ))⁻¹ *
            ((2*(Real.pi:ℂ)*I)*(τ-σ)*f τ) =
            I*(τ-σ)*f τ := by field_simp [hπ]
        rw [heq]
        simp
      rw [hmain,norm_mul]
      have hpiNorm : ‖(2*(Real.pi:ℂ))⁻¹‖ =
          (2*Real.pi)⁻¹ := by
        simp [Complex.norm_real,Real.pi_pos.le]
      rw [hpiNorm]
      have hscaled :
        (2*Real.pi)⁻¹ * ‖∮ z in C(c,R), g₁ z‖ ≤
          R*((‖σ-c‖+R)*M*
            (‖sourcePeriodicGapDisplacement hp hp1 ψ m‖^2/
              (2*(Real.pi/16)^3))) := by
        calc
          (2*Real.pi)⁻¹ * ‖∮ z in C(c,R), g₁ z‖ ≤
            (2*Real.pi)⁻¹ *
              (2*Real.pi*R*((‖σ-c‖+R)*M*
                (‖sourcePeriodicGapDisplacement hp hp1 ψ m‖^2/
                  (2*(Real.pi/16)^3)))) :=
            mul_le_mul_of_nonneg_left hcorr (by positivity)
          _ = _ := by field_simp [Real.pi_ne_zero]
      exact add_le_add le_rfl hscaled
    _ = _ := by dsimp [R,c,τ]; ring

end NLS.ZakharovShabat
