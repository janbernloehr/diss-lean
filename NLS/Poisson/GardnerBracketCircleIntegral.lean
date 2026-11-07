import NLS.Poisson.GardnerHamiltonianDirection
import NLS.ComplexAnalysis.ParametricCircleIntegral

/-! The actual H-minus-one Gardner cotangent pairing commutes with
jointly analytic circle integration, with the derivative sign retained. -/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.Poisson

theorem gardnerCotangentBivector_circleIntegral_of_jointAnalytic
    (F : ℂ × WeightedCoeff (Weight.sobolev (-1)) 2 → ℂ)
    (U : Set (ℂ × WeightedCoeff (Weight.sobolev (-1)) 2))
    (hU : IsOpen U) (hF : AnalyticOnNhd ℂ F U)
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R) (q : WeightedCoeff (Weight.sobolev (-1)) 2)
    (hcircle : ∀ z ∈ sphere c R, (z,q) ∈ U)
    (L : WeightedCoeff (Weight.sobolev (-1)) 2 →L[ℂ] ℂ) :
    gardnerCotangentBivector L (fderiv ℂ (fun a => ∮ z in C(c,R), F (z,a)) q) =
      ∮ z in C(c,R), gardnerCotangentBivector L (fderiv ℂ (fun a => F (z,a)) q) := by
  obtain ⟨V,hV,hqV,M,_,hbound⟩ := exists_uniform_joint_fderiv_bound_on_circle F U hU hF c R q hcircle
  let h := gardnerHamiltonianDirection L
  have hbiv (K : WeightedCoeff (Weight.sobolev (-1)) 2 →L[ℂ] ℂ) :
      gardnerCotangentBivector L K = -K h := by
    rw [apply_gardnerHamiltonianDirection]
    exact gardnerCotangentBivector_antisymm L K
  rw [hbiv,fderiv_circleIntegral_apply_of_jointAnalytic F U hU hF c R hR V hV q hqV M
    (fun a ha θ => (hbound _ (circleMap_mem_sphere c hR θ) a ha).1)
    (fun a ha θ => (hbound _ (circleMap_mem_sphere c hR θ) a ha).2) h]
  calc
    _ = ∮ z in C(c,R), (-1:ℂ)*(fderiv ℂ (fun a => F (z,a)) q) h := by
      rw [circleIntegral.integral_const_mul,neg_one_mul]
    _ = _ := by
      apply circleIntegral.integral_congr hR
      intro z _
      simpa only [neg_one_mul] using (hbiv (fderiv ℂ (fun a => F (z,a)) q)).symm

end NLS.Poisson
