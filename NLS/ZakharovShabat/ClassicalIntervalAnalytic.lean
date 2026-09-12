import NLS.ZakharovShabat.PhysicalPotentialExtension
import NLS.ZakharovShabat.ClassicalIntervalEigenvalues
import NLS.ZakharovShabat.BoundaryEigenvalues

/-!
# Analytic eigenvalue branches for original physical potentials

Pulling back the reflected-potential neighborhood along the bounded physical
extension gives one open convex neighborhood and one cutoff for both original
boundary problems. Each high disk contains exactly the trace-defined classical
eigenvalue, and that value depends analytically on the original `L²` potential.
Coefficient algebraic multiplicities are not redefined as physical operator
multiplicities: identifying original generalized eigenspaces remains separate.
-/

noncomputable section
open MeasureTheory Set Metric
namespace NLS.ZakharovShabat
namespace BoundaryCondition

/-- The high-index trace branch, now parameterized by the original physical potential class. -/
def classicalEigenvalue (b : BoundaryCondition) (u : IntervalPairL2) (n : ℤ) : ℂ :=
  eigenvalue b (by simp) (intervalPotentialCoefficients u) n

/-- Choosing the original representative does not change its eigenvalue set. -/
theorem classicalEigenvalues_representative_ofFunction (b : BoundaryCondition) (φ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) :
    classicalEigenvalues b (intervalL2Representative (intervalL2OfFunction φ hφ)) = classicalEigenvalues b φ :=
  classicalEigenvalues_congr_ae b (intervalL2Representative_ofFunction φ hφ)

/-- The physical parameterization agrees with the original Fourier-integral trace formula. -/
@[simp] theorem classicalEigenvalue_ofFunction (b : BoundaryCondition) (φ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) (n : ℤ) :
    classicalEigenvalue b (intervalL2OfFunction φ hφ) n =
      eigenvalue b (by simp) (dirichletPotentialCoefficients φ hφ) n := by
  simp only [classicalEigenvalue, intervalPotentialCoefficients_ofFunction]

/-- Analyticity transfers through the physical extension whenever the fixed circle is admissible. -/
theorem analyticAt_classicalEigenvalue (b : BoundaryCondition) (u : IntervalPairL2) (n : ℤ)
    (hc : sphere ((Real.pi : ℂ) * n) (Real.pi / 4) ⊆
      ZakharovShabat.resolventSet (by simp) (intervalPotentialCoefficients u)) :
    AnalyticAt ℂ (fun v : IntervalPairL2 => classicalEigenvalue b v n) u :=
  (analyticAt_eigenvalue b (by simp) (intervalPotentialToDirichlet u) n hc).comp
    (f := intervalPotentialToDirichlet) (analyticAt_intervalPotentialToDirichlet u)

/-- Uniform coefficient counting identifies the unique actual original eigenvalue in a high disk. -/
theorem classicalEigenvalues_inter_disk (b : BoundaryCondition) (u : IntervalPairL2) {N : ℕ}
    (h : BoundaryCountingData (by simp) (intervalPotentialCoefficients u)
      (intervalPotentialToDirichlet u).property N) (n : ℤ) (hn : N < n.natAbs) :
    classicalEigenvalues b (intervalL2Representative u) ∩ ball ((Real.pi : ℂ) * n) (Real.pi / 4) =
      {classicalEigenvalue b u n} := by
  ext z
  rw [mem_inter_iff, classicalEigenvalues_eq_boundarySpectrum b _ (memLp_intervalL2Representative u)]
  change (z ∈ spectrum b (by simp) (intervalPotentialCoefficients u)
    (intervalPotentialToDirichlet u).property ∧
    z ∈ ball ((Real.pi : ℂ) * n) (Real.pi / 4)) ↔ z ∈ ({classicalEigenvalue b u n} : Set ℂ)
  rw [← mem_enclosedSpectrum b (by simp) (intervalPotentialCoefficients u)
    (intervalPotentialToDirichlet u).property _ z _, (h.eigenvalue_spec b n hn).1]
  exact Finset.mem_singleton

/-- Both original free trace branches retain every signed integer frequency. -/
@[simp] theorem classicalEigenvalue_zero (b : BoundaryCondition) (n : ℤ) :
    classicalEigenvalue b 0 n = (Real.pi : ℂ) * n := by
  have hz : intervalPotentialCoefficients 0 = 0 := map_zero intervalPotentialCLM
  rw [classicalEigenvalue, hz, eigenvalue_zero]

end BoundaryCondition
open BoundaryCondition

/-- One original physical neighborhood supports both analytic high-index boundary branches. -/
theorem exists_uniform_analytic_classicalEigenvalues (u : IntervalPairL2) :
    ∃ N₀ : ℕ, ∃ U : Set IntervalPairL2,
      0 < N₀ ∧ IsOpen U ∧ Convex ℝ U ∧ u ∈ U ∧ 0 ∈ U ∧
      (∀ v ∈ U, ∀ N : ℕ, N₀ ≤ N → BoundaryCountingData (by simp)
        (intervalPotentialCoefficients v) (intervalPotentialToDirichlet v).property N) ∧
      ∀ b : BoundaryCondition, ∀ n : ℤ, N₀ < n.natAbs →
        AnalyticOnNhd ℂ (fun v : IntervalPairL2 => classicalEigenvalue b v n) U ∧
        ∀ v ∈ U, classicalEigenvalues b (intervalL2Representative v) ∩
          ball ((Real.pi : ℂ) * n) (Real.pi / 4) = {classicalEigenvalue b v n} := by
  obtain ⟨N₀, V, hN₀, ho, hconv, hu, h0, hdata, _⟩ :=
    exists_uniform_analytic_boundaryEigenvalues (by simp) (intervalPotentialToDirichlet u)
  let U : Set IntervalPairL2 := intervalPotentialToDirichlet ⁻¹' V
  have hU (v : IntervalPairL2) (hv : v ∈ U) (N : ℕ) (hN : N₀ ≤ N) :
      BoundaryCountingData (by simp) (intervalPotentialCoefficients v)
        (intervalPotentialToDirichlet v).property N := hdata _ hv N hN
  refine ⟨N₀, U, hN₀, ho.preimage intervalPotentialToDirichlet.continuous,
    hconv.linear_preimage (intervalPotentialToDirichlet.toLinearMap.restrictScalars ℝ), hu, ?_, hU, ?_⟩
  · change intervalPotentialToDirichlet 0 ∈ V
    simpa only [map_zero] using h0
  · intro b n hn
    refine ⟨?_, fun v hv => classicalEigenvalues_inter_disk b v (hU v hv N₀ le_rfl) n hn⟩
    intro v hv
    exact analyticAt_classicalEigenvalue b v n ((hU v hv N₀ le_rfl).periodic.disk_resolvent n hn)

end NLS.ZakharovShabat
