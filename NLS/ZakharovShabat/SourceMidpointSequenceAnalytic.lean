import NLS.ZakharovShabat.SourcePeriodicMidpointAsymptotics
import NLS.ZakharovShabat.SourceBoundaryDisplacementAnalytic
import NLS.SequenceSpaces.BoundedCoordinateDifferentiable

/-! # Banach analyticity of the actual midpoint displacement sequence

The scalar midpoint contour invariants and the locally uniform sequence
bounds give analyticity into the original coefficient space, on one open
complex neighborhood of the entire real source locus.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual midpoint displacement is analytic as a full coefficient-valued map. -/
theorem exists_sourcePeriodicMidpointDisplacement_analytic_common_domain
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      AnalyticOnNhd ℂ (sourcePeriodicMidpointDisplacement hp hp1) W := by
  obtain ⟨W,hW,_,hreal,hcoord⟩ := exists_global_source_analytic_midpoint_squaredGap hp hp1
  refine ⟨W,hW,hreal,fun φ hφ => ?_⟩
  obtain ⟨_,_,U,hU,hφU,R,_,hbound⟩ :=
    exists_uniform_small_sourcePeriodicMidpointDisplacement hp hp1 φ (ε := 1) (by norm_num)
  apply (Coeff.analyticOnNhd_of_bounded_coordinatewise
    (sourcePeriodicMidpointDisplacement hp hp1) (hW.inter hU) ?_ R ?_) φ ⟨hφ,hφU⟩
  · intro n ψ hψ
    simp only [sourcePeriodicMidpointDisplacement_apply]
    exact ((hcoord ψ hψ.1 n).1).sub analyticAt_const
  · intro ψ hψ
    exact (hbound ψ hψ.2).1

/-- Coordinate evaluation of the full midpoint derivative is the actual scalar root derivative. -/
theorem fderiv_sourcePeriodicMidpointDisplacement_apply_of_differentiableAt
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ h : CoeffPair p) (n : ℤ)
    (hφ : DifferentiableAt ℂ (sourcePeriodicMidpointDisplacement hp hp1) φ) :
    (fderiv ℂ (sourcePeriodicMidpointDisplacement hp hp1) φ) h n =
      (fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem _) n) φ) h := by
  rw [Coeff.fderiv_apply_of_differentiableAt _ _ _ _ hφ]
  simp only [sourcePeriodicMidpointDisplacement_apply,fderiv_sub_const]

/-- Coordinate evaluation of the full boundary derivative is the actual scalar root derivative. -/
theorem fderiv_sourceBoundaryDisplacement_apply_of_differentiableAt
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition) (φ h : CoeffPair p) (n : ℤ)
    (hφ : DifferentiableAt ℂ (sourceBoundaryDisplacement hp hp1 b) φ) :
    (fderiv ℂ (sourceBoundaryDisplacement hp hp1 b) φ) h n =
      (fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n) φ) h := by
  rw [Coeff.fderiv_apply_of_differentiableAt _ _ _ _ hφ]
  simp only [sourceBoundaryDisplacement_apply,fderiv_sub_const]

end NLS.ZakharovShabat
