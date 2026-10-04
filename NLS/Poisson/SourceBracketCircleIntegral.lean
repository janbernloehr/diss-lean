import NLS.Poisson.SourceHamiltonianDirection
import NLS.ComplexAnalysis.ParametricCircleIntegral

/-! # Source Poisson pairing commutes with analytic circle integration

For a fixed source cotangent, the bracket is evaluation in its actual
Hamiltonian direction with the antisymmetric sign. Differentiation
under the circle integral therefore transports the pairing exactly.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.Poisson
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sourceBivector_circleIntegral_of_jointAnalytic
    (h2p : (2 : ℝ≥0∞) ≤ p) (F : ℂ × CoeffPair p → ℂ) (U : Set (ℂ × CoeffPair p))
    (hU : IsOpen U) (hF : AnalyticOnNhd ℂ F U)
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R) (ψ : CoeffPair p)
    (hcircle : ∀ z ∈ sphere c R, (z,ψ) ∈ U) (L : CoeffPair p →L[ℂ] ℂ) :
    sourceBivector h2p L (fderiv ℂ (fun χ => ∮ z in C(c,R), F (z,χ)) ψ) =
      ∮ z in C(c,R), sourceBivector h2p L (fderiv ℂ (fun χ => F (z,χ)) ψ) := by
  obtain ⟨V,hV,hψV,M,_,hbound⟩ := exists_uniform_joint_fderiv_bound_on_circle F U hU hF c R ψ hcircle
  let h := sourceHamiltonianDirection h2p L
  have hbiv (M : CoeffPair p →L[ℂ] ℂ) : sourceBivector h2p L M = -M h := by
    rw [apply_sourceHamiltonianDirection]
    exact sourceBivector_antisymm h2p L M
  rw [hbiv]
  rw [fderiv_circleIntegral_apply_of_jointAnalytic F U hU hF c R hR V hV ψ hψV M
    (fun χ hχ θ => (hbound _ (circleMap_mem_sphere c hR θ) χ hχ).1)
    (fun χ hχ θ => (hbound _ (circleMap_mem_sphere c hR θ) χ hχ).2) h]
  calc
    _ = ∮ z in C(c,R), (-1 : ℂ)*(fderiv ℂ (fun χ => F (z,χ)) ψ) h := by
      rw [circleIntegral.integral_const_mul,neg_one_mul]
    _ = _ := by
      apply circleIntegral.integral_congr hR
      intro z _
      simpa only [neg_one_mul] using (hbiv (fderiv ℂ (fun χ => F (z,χ)) ψ)).symm

end NLS.Poisson
