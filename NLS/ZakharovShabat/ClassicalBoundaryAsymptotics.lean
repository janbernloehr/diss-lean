import NLS.ZakharovShabat.BoundaryDisplacementSummability
import NLS.ZakharovShabat.ClassicalIntervalAnalytic

/-!
# Square-summable displacements of the original physical boundary eigenvalues

The bounded reflected-potential map transfers the coefficient estimate to
arbitrary physical interval L² potentials. The same neighborhood also retains
the identification with the unique original Dirichlet or Neumann eigenvalue
in every sufficiently high disc.
-/

noncomputable section
open Metric Set
namespace NLS.ZakharovShabat
open BoundaryCondition

/-- The two original physical boundary problems have ℓ² displacement sequences and common quantitative tails. -/
theorem exists_uniform_classicalBoundaryAsymptotics (u : IntervalPairL2) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set IntervalPairL2,
      IsOpen U ∧ Convex ℝ U ∧ u ∈ U ∧ 0 ∈ U ∧ ∀ v ∈ U, ∀ b : BoundaryCondition,
        Memℓp (fun n : ℤ => classicalEigenvalue b v n-(Real.pi : ℂ)*n) 2 ∧
        (∀ n : ℤ, N₀ ≤ n.natAbs →
          classicalEigenvalues b (intervalL2Representative v) ∩
            ball ((Real.pi : ℂ)*n) (Real.pi/4) = {classicalEigenvalue b v n}) ∧
        ∀ N : ℕ, N₀ ≤ N →
          Summable (spectralDisplacementPowerTail 2 N (classicalEigenvalue b v)) ∧
          (∑' n : ℤ, spectralDisplacementPowerTail 2 N (classicalEigenvalue b v) n) ≤
            rootDisplacementBudget SpectralWeight.one (unitBaseEquiv.symm (intervalPotentialCoefficients v)) N := by
  obtain ⟨N₁,hN₁,V,ho₁,hc₁,hu₁,h0₁,hbound⟩ := exists_uniform_boundaryDisplacementSummability
    (p := 2) (by norm_num) (by norm_num) (intervalPotentialToDirichlet u)
  obtain ⟨N₂,U₂,_,ho₂,hc₂,hu₂,h0₂,_,hclassical⟩ := exists_uniform_analytic_classicalEigenvalues u
  let F := intervalPotentialToDirichlet
  refine ⟨max N₁ (N₂+1),hN₁.trans (le_max_left _ _),(F ⁻¹' V) ∩ U₂,
    (ho₁.preimage F.continuous).inter ho₂,
    (hc₁.linear_preimage (F.restrictScalars ℝ).toLinearMap).inter hc₂,
    ⟨hu₁,hu₂⟩,⟨by simpa using h0₁,h0₂⟩,?_⟩
  intro v hv b
  have hb := hbound (F v) hv.1 b
  refine ⟨hb.1,?_,fun N hN => hb.2 N (by omega)⟩
  intro n hn
  exact (hclassical b n (by omega)).2 v hv.2

end NLS.ZakharovShabat
