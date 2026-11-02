import NLS.KdV.HillL2AnnulusCoverage
import NLS.KdV.HillL2CubicContourMoments

/-! # One complex L2 neighborhood for the complete high moment tail

The actual source domain covers every sufficiently high energy circle
on one complex L2 neighborhood. Joint contour analyticity therefore
controls every polynomial primitive moment and the shifted cubic moment
on that same neighborhood, without a parity or reality hypothesis.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

theorem exists_analytic_hillL2HighContourMomentFamilies (q : Coeff 2) :
    ∃ N : ℕ, ∃ V : Set (Coeff 2), 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ n : ℕ+, N ≤ (n : ℕ) →
        (∀ m : ℕ, AnalyticOnNhd ℂ (hillL2HighContourMoment (n : ℕ) m) V) ∧
        AnalyticOnNhd ℂ (hillL2HighCubicContourMoment (n : ℕ)) V := by
  obtain ⟨N,V,hN,hV,hq,hcover⟩ := exists_hillL2_high_energy_annulus_neighborhood q 1
    (by norm_num) le_rfl
  refine ⟨N,V,hN,hV,hq,?_⟩
  intro n hn
  have hc (a : Coeff 2) (ha : a ∈ V) (z : ℂ)
      (hz : z ∈ sphere (freeHillValue (n : ℕ) : ℂ) (n : ℝ)) :
      (z,a) ∈ hillL2ContinuationDomain := by
    apply hcover a ha n hn z (sphere_subset_closedBall hz)
    have he : ‖z-(freeHillValue (n : ℕ) : ℂ)‖ = (n : ℝ) := by
      simpa only [mem_sphere,dist_eq_norm] using hz
    rw [one_mul,he]
  constructor
  · intro m
    let F : ℂ × Coeff 2 → ℂ := fun t => t.1^m*hillL2ContinuedPrimitive t
    have hF : AnalyticOnNhd ℂ F hillL2ContinuationDomain :=
      (analyticOnNhd_fst.pow m).mul analyticOnNhd_hillL2ContinuedPrimitive
    have hi := analyticOnNhd_circleIntegral_of_jointAnalytic F
      isOpen_hillL2ContinuationDomain hF (freeHillValue (n : ℕ) : ℂ) (n : ℝ)
      (by positivity) hV hc
    intro a ha
    change AnalyticAt ℂ (fun b => -(Real.pi : ℂ)⁻¹ *
      ∮ z in C((freeHillValue (n : ℕ) : ℂ),(n : ℝ)), z^m*hillL2ContinuedPrimitive (z,b)) a
    exact (hi a ha).const_smul (c := -(Real.pi : ℂ)⁻¹)
  · let F : ℂ × Coeff 2 → ℂ := fun t => (hillL2ContinuedPrimitive t+I*(n : ℂ)*Real.pi)^3
    have hF : AnalyticOnNhd ℂ F hillL2ContinuationDomain :=
      (analyticOnNhd_hillL2ContinuedPrimitive.add analyticOnNhd_const).pow 3
    have hi := analyticOnNhd_circleIntegral_of_jointAnalytic F
      isOpen_hillL2ContinuationDomain hF (freeHillValue (n : ℕ) : ℂ) (n : ℝ)
      (by positivity) hV hc
    intro a ha
    exact (hi a ha).const_smul (c := (Real.pi : ℂ)⁻¹)

end NLS.KdV
