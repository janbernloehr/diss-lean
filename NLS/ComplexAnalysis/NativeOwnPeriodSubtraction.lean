import NLS.ComplexAnalysis.DiscBounds
/-! # Own-period subtraction in a native complex Banach space

Subtracting the unit vector cancels the genuine Bochner period with the
negative unit quadratic-root period. Maximum modulus bounds the full
regular numerator norm on the filled disc, including the own coordinate.
-/
noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis
variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B]

theorem native_own_period_subtraction [CompleteSpace B]
    (G : ℂ → B) (Q U S : ℂ → ℂ) (e : B) (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hproduct : ∀ z ∈ sphere c R, Q z*U z=S z)
    (hiG : CircleIntegrable (fun z => (S z)⁻¹ • G z) c R)
    (hiQ : CircleIntegrable (fun z => (Q z)⁻¹) c R)
    (hpG : (∮ z in C(c,R), (S z)⁻¹ • G z) = (2*(Real.pi : ℂ)) • e)
    (hpQ : (∮ z in C(c,R), (Q z)⁻¹) = -(2*(Real.pi : ℂ)*I)) :
    CircleIntegrable (fun z => (Q z)⁻¹ • ((-I/U z) • G z-e)) c R ∧
      (∮ z in C(c,R), (Q z)⁻¹ • ((-I/U z) • G z-e)) = 0 := by
  have hpoint (z : ℂ) (hz : z ∈ sphere c R) :
      (Q z)⁻¹ • ((-I/U z) • G z-e) =
        (-I) • ((S z)⁻¹ • G z)-(Q z)⁻¹ • e := by
    have hs : (Q z)⁻¹ * (-I/U z) = (-I)*(S z)⁻¹ := by
      rw [← hproduct z hz,mul_inv_rev,div_eq_mul_inv]
      ring
    simp only [smul_sub,smul_smul,hs]
  have hi1 : CircleIntegrable (fun z => (-I) • ((S z)⁻¹ • G z)) c R :=
    hiG.continuousOn_smul continuousOn_const
  have hi2 : CircleIntegrable (fun z => (Q z)⁻¹ • e) c R :=
    hiQ.smul_continuousOn continuousOn_const
  have hi : CircleIntegrable (fun z => (Q z)⁻¹ • ((-I/U z) • G z-e)) c R := by
    apply (hi1.sub hi2).congr_ae
    exact Filter.Eventually.of_forall (fun theta => (hpoint _ (circleMap_mem_sphere c hR theta)).symm)
  refine ⟨hi,?_⟩
  calc
    _ = ∮ z in C(c,R), (-I) • ((S z)⁻¹ • G z)-(Q z)⁻¹ • e := circleIntegral.integral_congr hR hpoint
    _ = (-I) • ((2*(Real.pi : ℂ)) • e)-(-(2*(Real.pi : ℂ)*I)) • e := by
      rw [circleIntegral.integral_sub hi1 hi2,circleIntegral.integral_smul,circleIntegral.integral_smul_const,hpG,hpQ]
    _ = 0 := by rw [smul_smul,show (-I)*(2*(Real.pi : ℂ)) = -(2*(Real.pi : ℂ)*I) by ring,sub_self]

theorem norm_native_own_regular_numerator_le
    (G : ℂ → B) (Q U S : ℂ → ℂ) (e : B) (c : ℂ) (R C : ℝ) (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ (fun z => (-I/U z) • G z) (closedBall c R))
    (hproduct : ∀ z ∈ sphere c R, Q z*U z=S z)
    (hQn : ∀ z ∈ sphere c R, Q z ≠ 0)
    (hQbound : ∀ z ∈ sphere c R, ‖Q z‖ ≤ 2*R)
    (hGbound : ∀ z ∈ sphere c R, ‖(S z)⁻¹ • G z‖ ≤ C/R) :
    ∀ z ∈ closedBall c R, ‖(-I/U z) • G z-e‖ ≤ 2*C+‖e‖ := by
  have hboundary (z : ℂ) (hz : z ∈ sphere c R) : ‖(-I/U z) • G z‖ ≤ 2*C := by
    have hs : -I/U z = ((-I)*Q z)*(S z)⁻¹ := by
      rw [← hproduct z hz,mul_inv_rev,div_eq_mul_inv]
      calc
        _ = (-I)*(Q z*(Q z)⁻¹)*(U z)⁻¹ := by rw [mul_inv_cancel₀ (hQn z hz),mul_one]
        _ = _ := by ring
    rw [hs,← smul_smul,norm_smul,norm_mul,norm_neg,norm_I,one_mul]
    calc
      _ ≤ (2*R)*(C/R) := mul_le_mul (hQbound z hz) (hGbound z hz) (norm_nonneg _) (by positivity)
      _ = _ := by field_simp
  have hdisc (z : ℂ) (hz : z ∈ closedBall c R) : ‖(-I/U z) • G z‖ ≤ 2*C := by
    apply Complex.norm_le_of_forall_mem_frontier_norm_le (isBounded_ball (x := c) (r := R))
      (DiffContOnCl.mk_ball (hf.differentiableOn.mono ball_subset_closedBall) hf.continuousOn)
    · intro w hw
      rw [frontier_ball c hR.ne'] at hw
      exact hboundary w hw
    · rw [closure_ball c hR.ne']
      exact hz
  intro z hz
  exact (norm_sub_le _ _).trans (by linarith [hdisc z hz])
end NLS.ComplexAnalysis
