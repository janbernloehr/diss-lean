import NLS.ZakharovShabat.ClassicalAuxiliaryCounting
import NLS.ZakharovShabat.ClassicalBoundaryAsymptotics

/-!
# Physical starred square-summability and algebraic counts

On one common open convex physical L² neighborhood, both original auxiliary
branches have square-summable displacements and quantitative tails, while every
larger cutoff retains the actual physical multiplicity counts. High-index
branches are analytic and identified with simple original auxiliary eigenvalues.
-/

noncomputable section
open Set Metric
namespace NLS.ZakharovShabat
open BoundaryCondition

/-- The original physical auxiliary branches satisfy the starred part of Corollary 6.2,
with analytic simple branches, physical algebraic counts, and all larger quantitative tails. -/
theorem exists_uniform_classicalAuxiliaryAsymptotics (u : IntervalPairL2) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set IntervalPairL2,
      IsOpen U ∧ Convex ℝ U ∧ u ∈ U ∧ 0 ∈ U ∧
      (∀ v ∈ U, ∀ N : ℕ, N₀ ≤ N → ClassicalAuxiliaryCountingData v N) ∧
      (∀ b : BoundaryCondition, ∀ n : ℤ, N₀ ≤ n.natAbs →
        AnalyticOnNhd ℂ (fun v : IntervalPairL2 => classicalAuxiliaryEigenvalue b v n) U) ∧
      ∀ v ∈ U, ∀ b : BoundaryCondition,
        Memℓp (fun n : ℤ => classicalAuxiliaryEigenvalue b v n - (Real.pi : ℂ) * n) 2 ∧
        (∀ n : ℤ, N₀ ≤ n.natAbs →
          classicalAuxiliarySpectrum b v ∩ ball ((Real.pi : ℂ) * n) (Real.pi / 4) = {classicalAuxiliaryEigenvalue b v n} ∧
          classicalAuxiliaryAlgebraicMultiplicity b v (classicalAuxiliaryEigenvalue b v n) = 1) ∧
        ∀ N : ℕ, N₀ ≤ N →
          Summable (spectralDisplacementPowerTail 2 N (classicalAuxiliaryEigenvalue b v)) ∧
          (∑' n : ℤ, spectralDisplacementPowerTail 2 N (classicalAuxiliaryEigenvalue b v) n) ≤
            rootDisplacementBudget SpectralWeight.one
              (unitBaseEquiv.symm (intervalPotentialCoefficients (intervalAuxiliaryPotential v))) N := by
  let F := intervalAuxiliaryPotential.toContinuousLinearEquiv.toContinuousLinearMap
  obtain ⟨N₁,hN₁,U₁,ho₁,hc₁,hu₁,h0₁,hbound⟩ := exists_uniform_classicalBoundaryAsymptotics (F u)
  obtain ⟨N₂,U₂,_,ho₂,hc₂,hu₂,h0₂,hcount,han⟩ := exists_uniform_classicalAuxiliaryCountingData u
  refine ⟨max N₁ (N₂+1),hN₁.trans (le_max_left _ _),(F ⁻¹' U₁) ∩ U₂,
    (ho₁.preimage F.continuous).inter ho₂,
    (hc₁.linear_preimage (F.restrictScalars ℝ).toLinearMap).inter hc₂,
    ⟨hu₁,hu₂⟩,⟨by simpa only [Set.mem_preimage,map_zero] using h0₁,h0₂⟩,?_,?_,?_⟩
  · intro v hv N hN
    exact hcount v hv.2 N (by omega)
  · intro b n hn v hv
    exact han b n (by omega) v hv.2
  · intro v hv b
    have hb := hbound (F v) hv.1 b
    refine ⟨hb.1,?_,fun N hN => hb.2.2 N (by omega)⟩
    intro n hn
    exact (hcount v hv.2 N₂ le_rfl).disk_simple b n (by omega)

end NLS.ZakharovShabat
