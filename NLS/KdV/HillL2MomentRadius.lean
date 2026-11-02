import NLS.KdV.HillL2HighMomentFamilies
import NLS.KdV.ActionHamiltonianMoments

/-! # Uniform energy-radius independence of actual high L2 periods

One source annulus controls every integer power of the shifted primitive.
The original energy-circle cubic and Arnold periods retain their exact
normalizations on all the smaller checked circles.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

theorem exists_hillL2_high_power_period_radius_independence
    (q : Coeff 2) (rho : ℝ) (hrho : 0 < rho) (hrho1 : rho ≤ 1) :
    ∃ N : ℕ, ∃ V : Set (Coeff 2), 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      (∀ a ∈ V, ∀ n : ℕ+, N ≤ (n : ℕ) →
        ∀ z ∈ closedBall (freeHillValue (n : ℕ) : ℂ) (n : ℝ),
          rho*(n : ℝ) ≤ ‖z-(freeHillValue (n : ℕ) : ℂ)‖ →
            (z,a) ∈ hillL2ContinuationDomain) ∧
      ∀ a ∈ V, ∀ n : ℕ+, N ≤ (n : ℕ) →
        ∀ r ∈ Icc (rho*(n : ℝ)) (n : ℝ), ∀ m : ℕ,
          ((Real.pi : ℂ)⁻¹ * ∮ z in C((freeHillValue (n : ℕ) : ℂ),(n : ℝ)),
            (hillL2ContinuedPrimitive (z,a)+I*(n : ℂ)*Real.pi)^m) =
          (Real.pi : ℂ)⁻¹ * ∮ z in C((freeHillValue (n : ℕ) : ℂ),r),
            (hillL2ContinuedPrimitive (z,a)+I*(n : ℂ)*Real.pi)^m := by
  obtain ⟨N,V,hN,hV,hq,hcover⟩ := exists_hillL2_high_energy_annulus_neighborhood q rho hrho hrho1
  refine ⟨N,V,hN,hV,hq,hcover,?_⟩
  intro a ha n hn r hr m
  have hrpos : 0 < r := (by positivity : 0 < rho*(n : ℝ)).trans_le hr.1
  have hF : AnalyticOnNhd ℂ
      (fun z => (hillL2ContinuedPrimitive (z,a)+I*(n : ℂ)*Real.pi)^m)
      (closedBall (freeHillValue (n : ℕ) : ℂ) (n : ℝ) \ ball (freeHillValue (n : ℕ) : ℂ) r) := by
    intro z hz
    have hfar : rho*(n : ℝ) ≤ ‖z-(freeHillValue (n : ℕ) : ℂ)‖ :=
      hr.1.trans (by simpa only [mem_ball,dist_eq_norm,not_lt] using hz.2)
    have hd := hcover a ha n hn z hz.1 hfar
    exact (((analyticOnNhd_hillL2ContinuedPrimitive _ hd).comp
      (f := fun z : ℂ => (z,a)) (analyticAt_id.prod analyticAt_const)).add analyticAt_const).pow m
  have heq := circleIntegral_eq_of_differentiable_on_annulus_off_countable hrpos hr.2
    countable_empty hF.continuousOn (fun z hz =>
      (hF z ⟨ball_subset_closedBall hz.1.1,
        fun ht => hz.1.2 (ball_subset_closedBall ht)⟩).differentiableAt)
  exact congrArg (fun w : ℂ => (Real.pi : ℂ)⁻¹*w) heq

/-- The indexed shift contributes no constant period to the actual
level-zero Arnold action. Source coverage is the only circle hypothesis. -/
theorem hillL2HighContourMoment_zero_eq_shifted_period
    (a : Coeff 2) (n : ℕ+)
    (hc : ∀ z ∈ sphere (freeHillValue (n : ℕ) : ℂ) (n : ℝ),
      (z,a) ∈ hillL2ContinuationDomain) :
    hillL2HighContourMoment (n : ℕ) 0 a =
      -(Real.pi : ℂ)⁻¹ * ∮ z in C((freeHillValue (n : ℕ) : ℂ),(n : ℝ)),
        hillL2ContinuedPrimitive (z,a)+I*(n : ℂ)*Real.pi := by
  let D : Set ℂ := {z | (z,a) ∈ hillL2ContinuationDomain}
  have hF : AnalyticOnNhd ℂ (fun z => hillL2ContinuedPrimitive (z,a)) D := by
    intro z hz
    exact (analyticOnNhd_hillL2ContinuedPrimitive _ hz).comp
      (f := fun z : ℂ => (z,a)) (analyticAt_id.prod analyticAt_const)
  have heq := primitiveAction_add_const_of_analyticOnNhd _ D hF
    (freeHillValue (n : ℕ) : ℂ) (I*(n : ℂ)*Real.pi) (n : ℝ) (by positivity) hc
  change -(Real.pi : ℂ)⁻¹ * (∮ z in C((freeHillValue (n : ℕ) : ℂ),(n : ℝ)),
    z^0*hillL2ContinuedPrimitive (z,a)) = _
  simp only [pow_zero,one_mul]
  exact heq.symm

end NLS.KdV
