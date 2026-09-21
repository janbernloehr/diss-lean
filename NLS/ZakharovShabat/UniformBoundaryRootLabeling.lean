import NLS.ZakharovShabat.BoundaryRootMultiplicity
import NLS.ZakharovShabat.PeriodOneBoundaryAsymptotics

/-! # Complete boundary sequences on common potential neighborhoods
One common cutoff works for both ordinary boundary conditions and all
nearby reflected potentials. Pullback gives the same result for original
period-one coefficient potentials. These labels are not yet ordered or
asserted continuous in the potential.
-/

noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Both actual boundary spectra have complete lp-displaced labels on one neighborhood and cutoff. -/
theorem exists_uniform_boundaryRootLabeling (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : dirichletSubspace (p := p)) :
    ∃ N : ℕ, 0 < N ∧ ∃ U : Set (dirichletSubspace (p := p)), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ b : BoundaryCondition, ∃ ξ : ℤ → ℂ, BoundaryRootLabeling b hp ψ.val ψ.property N ξ := by
  obtain ⟨N,V,hN,hvo,hvc,hvφ,hv0,hcount,_⟩ := exists_uniform_analytic_boundaryEigenvalues hp φ
  obtain ⟨_,_,W,hwo,hwc,hwφ,hw0,hdisp⟩ := exists_uniform_boundaryDisplacementSummability hp hp1 φ
  exact ⟨N,hN,V ∩ W,hvo.inter hwo,hvc.inter hwc,⟨hvφ,hwφ⟩,⟨hv0,hw0⟩,
    fun ψ hψ b => exists_boundaryRootLabeling b hp ψ.val ψ.property N (hcount ψ hψ.1 N le_rfl) (hdisp ψ hψ.2 b).1⟩

/-- Every reflected finite-p potential admits complete actual boundary labels with lp displacement. -/
theorem exists_complete_boundaryRootLabeling (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : dirichletSubspace (p := p)) (b : BoundaryCondition) :
    ∃ N : ℕ, 0 < N ∧ ∃ ξ : ℤ → ℂ, BoundaryRootLabeling b hp φ.val φ.property N ξ := by
  obtain ⟨N,hN,_,_,_,hφ,_,h⟩ := exists_uniform_boundaryRootLabeling hp hp1 φ
  exact ⟨N,hN,h φ hφ b⟩

/-- Original period-one potentials have complete labels after the proved ordinary interval extension. -/
theorem exists_uniform_periodOneBoundaryRootLabeling (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ N : ℕ, 0 < N ∧ ∃ U : Set (CoeffPair p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ b : BoundaryCondition, ∃ ξ : ℤ → ℂ,
        BoundaryRootLabeling b hp (periodOneBoundaryPotential hp hp1 ψ).val
          (periodOneBoundaryPotential hp hp1 ψ).property N ξ := by
  let F := periodOneBoundaryPotential hp hp1
  obtain ⟨N,hN,V,ho,hc,hφ,h0,h⟩ := exists_uniform_boundaryRootLabeling hp hp1 (F φ)
  exact ⟨N,hN,F ⁻¹' V,ho.preimage F.continuous,hc.linear_preimage (F.restrictScalars ℝ).toLinearMap,
    hφ,by simpa only [mem_preimage,map_zero] using h0,fun ψ hψ b => h (F ψ) hψ b⟩

end NLS.ZakharovShabat
