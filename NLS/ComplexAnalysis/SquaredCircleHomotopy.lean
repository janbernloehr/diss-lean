import NLS.ComplexAnalysis.AffineLoopHomotopy
import NLS.ComplexAnalysis.HolomorphicPathPullback

/-! # Deforming a squared frequency circle to an energy circle

The quadratic image differs from the circle of radius 2*c*rho about
c^2 by exactly rho^2. A smooth affine deformation stays outside radius
c*rho and inside radius 3*c*rho. This preserves the energy one-form,
with its exact Jacobian 2*z.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped unitInterval
namespace NLS.ComplexAnalysis

theorem norm_sq_sub_sq_of_small_sphere (c rho : ℝ) (hc : 0 < c) (hrho : 0 < rho)
    (hrhoc : rho ≤ c/8) (z : ℂ) (hz : z ∈ sphere (c : ℂ) rho) :
    c*rho < ‖z^2-(c : ℂ)^2‖ ∧ ‖z^2-(c : ℂ)^2‖ ≤ 3*c*rho := by
  have hd : ‖z-(c : ℂ)‖ = rho := by simpa only [mem_sphere,dist_eq_norm] using hz
  have htwo : ‖(2 : ℂ)*(c : ℂ)‖ = 2*c := by simp [abs_of_pos hc]
  have hlo : 2*c ≤ ‖z+(c : ℂ)‖+rho := by
    calc
      _ = ‖(z+(c : ℂ))-(z-(c : ℂ))‖ := by rw [show (z+(c : ℂ))-(z-(c : ℂ)) = 2*(c : ℂ) by ring,htwo]
      _ ≤ _ := by simpa only [hd] using norm_sub_le (z+(c : ℂ)) (z-(c : ℂ))
  have hhi : ‖z+(c : ℂ)‖ ≤ rho+2*c := by
    calc
      _ = ‖(z-(c : ℂ))+2*(c : ℂ)‖ := by congr 1; ring
      _ ≤ _ := by simpa only [hd,htwo] using norm_add_le (z-(c : ℂ)) (2*(c : ℂ))
  rw [show z^2-(c : ℂ)^2 = (z-(c : ℂ))*(z+(c : ℂ)) by ring,norm_mul,hd]
  constructor
  · have hh : c < ‖z+(c : ℂ)‖ := by linarith
    nlinarith [mul_pos hrho (sub_pos.mpr hh)]
  · nlinarith [mul_nonneg hrho.le (show 0 ≤ 3*c-‖z+(c : ℂ)‖ by linarith)]

theorem square_circleMap_sub_linear (c rho theta : ℝ) :
    (circleMap (c : ℂ) rho theta)^2-circleMap ((c : ℂ)^2) (2*c*rho) theta =
      (circleMap 0 rho theta)^2 := by
  simp only [circleMap]
  push_cast
  ring

theorem squaredCirclePath_contDiffOn (c : ℂ) (rho : ℝ) :
    ContDiffOn ℝ 2 ((circlePath c rho).map (continuous_id.pow 2)).extend (Icc 0 1) := by
  apply ((circlePath_contDiffOn c rho).pow 2).congr
  intro t ht
  rw [Path.extend_apply _ ht,Path.extend_apply _ ht]
  rfl

theorem squaredCircleHomotopy_annulus (c rho : ℝ) (hc : 0 < c) (hrho : 0 < rho)
    (hrhoc : rho ≤ c/8) (s u : I) :
    c*rho < dist ((ContinuousMap.Homotopy.affine
      (circlePath ((c : ℂ)^2) (2*c*rho) : C(I, ℂ))
      ((circlePath (c : ℂ) rho).map (continuous_id.pow 2) : C(I, ℂ))) (s,u)) ((c : ℂ)^2) ∧
    dist ((ContinuousMap.Homotopy.affine
      (circlePath ((c : ℂ)^2) (2*c*rho) : C(I, ℂ))
      ((circlePath (c : ℂ) rho).map (continuous_id.pow 2) : C(I, ℂ))) (s,u)) ((c : ℂ)^2) ≤ 3*c*rho := by
  apply affineCircleHomotopy_annulus ((c : ℂ)^2) (2*c*rho) (c*rho) (3*c*rho) (rho^2)
    (by positivity) (sq_nonneg _)
  · nlinarith [mul_pos hrho (show 0 < c-rho by linarith)]
  · nlinarith [mul_nonneg hrho.le (show 0 ≤ c-rho by linarith)]
  · intro v
    change dist ((circleMap (c : ℂ) rho ((2*Real.pi)*(v : ℝ)))^2)
      (circleMap ((c : ℂ)^2) (2*c*rho) ((2*Real.pi)*(v : ℝ))) ≤ rho^2
    rw [dist_eq_norm,square_circleMap_sub_linear,norm_pow,norm_circleMap_zero,abs_of_pos hrho]

/-- Homotopy invariance for the exact squared-circle substitution. The
function need only be analytic near the closed annular shell. -/
theorem circleIntegral_square_pullback_eq_energy_circle
    (f : ℂ → ℂ) (c rho : ℝ) (hc : 0 < c) (hrho : 0 < rho) (hrhoc : rho ≤ c/8)
    (hf : AnalyticOnNhd ℂ f
      (closedBall ((c : ℂ)^2) (3*c*rho) \ closedBall ((c : ℂ)^2) (c*rho))) :
    (∮ z in C((c : ℂ),rho), f (z^2)*(2*z)) =
      ∮ z in C(((c : ℂ)^2),2*c*rho), f z := by
  let gamma := (circlePath (c : ℂ) rho).map (continuous_id.pow 2)
  let H := ContinuousMap.Homotopy.affine
    (circlePath ((c : ℂ)^2) (2*c*rho) : C(I, ℂ)) (gamma : C(I, ℂ))
  have hclosed : IsClosed (range H) := (isCompact_range (map_continuous H)).isClosed
  have hdiff (z : ℂ) (hz : z ∈ closure (range H)) : DifferentiableAt ℂ f z := by
    rw [hclosed.closure_eq] at hz
    obtain ⟨⟨s,u⟩,rfl⟩ := hz
    have hb := squaredCircleHomotopy_annulus c rho hc hrho hrhoc s u
    exact (hf _ ⟨hb.2,by simpa only [mem_closedBall,not_le] using hb.1⟩).differentiableAt
  have heq := curveIntegral_eq_of_holomorphic_homotopy f H
    (affineHomotopy_loop (γ₁ := circlePath ((c : ℂ)^2) (2*c*rho)) (γ₂ := gamma))
    (t := range H) (fun s _ u _ => ⟨(s,u),rfl⟩) hdiff
    (affineHomotopy_contDiffOn (circlePath_contDiffOn _ _) (squaredCirclePath_contDiffOn _ _))
  have hsq (z : ℂ) : HasDerivAt (fun w : ℂ => w^2) (2*z) z := by
    simpa using! (hasDerivAt_id z).pow 2
  have hp := (holomorphicPathPullback_integral_and_integrability f
    (fun z => f (z^2)*(2*z)) (fun z : ℂ => z^2) (fun z : ℂ => 2*z) (continuous_id.pow 2)
    (circlePath (c : ℂ) rho) ((circlePath_contDiffOn _ _).of_le (by norm_num))
    (fun _ _ => hsq _) (fun _ _ => rfl)).2
  rw [curveIntegral_circlePath] at hp
  rw [curveIntegral_circlePath] at heq
  exact hp.symm.trans heq.symm

end NLS.ComplexAnalysis
