import NLS.ComplexAnalysis.NearIdentityAnalyticInverse
import Mathlib.Topology.MetricSpace.Contracting

/-!
# Near-identity inversion preserves closed real subspaces

When the map preserves a closed real subspace, the identity-based
fixed-point iteration stays in that subspace. Its fixed point agrees
with any inverse image in the surrounding source ball by the lower
distance bound. This applies to complex analytic inverses even though
the invariant subspace is only real linear.
-/

noncomputable section
open Set Metric
open scoped NNReal
namespace NLS.ComplexAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Every sufficiently nearby inverse image remains in a preserved
closed real subspace. The inverse image is compared with a fixed point
constructed inside the intersection of that subspace and a closed ball. -/
theorem mem_closedSubmodule_of_near_identity_inverse
    (f : E → E) (a : E) (R ρ : ℝ) (hρ : 0 < ρ) (hρR : ρ < R)
    (hf : AnalyticOnNhd ℂ f (ball a R))
    (hnear : ∀ x ∈ ball a R,
      ‖fderiv ℂ f x-ContinuousLinearMap.id ℂ E‖ ≤ (1/2 : ℝ))
    (S : Submodule ℝ E) (hS : IsClosed (S : Set E)) (ha : a ∈ S)
    (hmap : ∀ x ∈ ball a R, x ∈ S → f x ∈ S)
    (y : E) (hyS : y ∈ S) (hy : ‖y-f a‖ < ρ/2)
    (x : E) (hx : x ∈ ball a R) (hfx : f x = y) : x ∈ S := by
  let k : E → E := fun z => f z-z
  have hk (z : E) (hz : z ∈ ball a R) : DifferentiableAt ℂ k z :=
    (hf z hz).differentiableAt.sub differentiableAt_id
  have hder (z : E) (hz : z ∈ ball a R) : ‖fderiv ℂ k z‖ ≤ (1/2 : ℝ) := by
    have he : fderiv ℂ k z = fderiv ℂ f z-ContinuousLinearMap.id ℂ E :=
      ((hf z hz).differentiableAt.hasFDerivAt.sub (hasFDerivAt_id z)).fderiv
    rw [he]
    exact hnear z hz
  let Φ : E → E := fun z => z-f z+y
  have hLip (u : E) (hu : u ∈ ball a R) (v : E) (hv : v ∈ ball a R) :
      ‖Φ u-Φ v‖ ≤ (1/2 : ℝ)*‖u-v‖ := by
    rw [show Φ u-Φ v = -(k u-k v) by dsimp [Φ,k]; abel,norm_neg]
    exact (convex_ball a R).norm_image_sub_le_of_norm_fderiv_le
      (𝕜 := ℂ) (f := k) hk hder hv hu
  let D : Set E := closedBall a ρ ∩ (S : Set E)
  have hD : IsClosed D := isClosed_closedBall.inter hS
  have hsub : closedBall a ρ ⊆ ball a R := closedBall_subset_ball hρR
  have hΦD : MapsTo Φ D D := by
    intro z hz
    have hzR := hsub hz.1
    refine ⟨?_,S.add_mem (S.sub_mem hz.2 (hmap z hzR hz.2)) hyS⟩
    rw [mem_closedBall,dist_eq_norm]
    have hzρ : ‖z-a‖ ≤ ρ := by simpa only [mem_closedBall,dist_eq_norm] using hz.1
    calc
      ‖Φ z-a‖ = ‖(Φ z-Φ a)+(Φ a-a)‖ := by congr 1; abel
      _ ≤ ‖Φ z-Φ a‖+‖Φ a-a‖ := norm_add_le _ _
      _ ≤ (1/2 : ℝ)*‖z-a‖+‖y-f a‖ := by
        have he : Φ a-a = y-f a := by dsimp [Φ]; abel
        rw [he]
        exact add_le_add (hLip z hzR a (mem_ball_self (hρ.trans hρR))) le_rfl
      _ ≤ ρ := by linarith
  let F : D → D := fun z => ⟨Φ z,hΦD z.property⟩
  have hc : ContractingWith (1/2 : ℝ≥0) F := by
    refine ⟨by norm_num,LipschitzWith.of_dist_le_mul ?_⟩
    intro u v
    simpa only [Subtype.dist_eq,dist_eq_norm,NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat]
      using hLip u (hsub u.property.1) v (hsub v.property.1)
  let : CompleteSpace D := hD.completeSpace_coe
  let : Nonempty D := ⟨⟨a,mem_closedBall_self hρ.le,ha⟩⟩
  let z := hc.fixedPoint F
  have hzfix : Φ z = (z : E) := congrArg Subtype.val hc.fixedPoint_isFixedPt
  have hfz : f z = y := by
    dsimp [Φ] at hzfix
    exact (add_left_cancel (hzfix.trans (sub_add_cancel (z : E) (f z)).symm)).symm
  have hbound := norm_sub_le_two_mul_norm_image_sub_of_derivative_near_id
    f a R hf hnear x z hx (hsub z.property.1)
  have heq : x = (z : E) := by
    rw [hfx,hfz,sub_self,norm_zero,mul_zero] at hbound
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hbound (norm_nonneg _)))
  rw [heq]
  exact z.property.2

end NLS.ComplexAnalysis
