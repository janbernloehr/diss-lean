import NLS.ZakharovShabat.ClassicalAuxiliaryMultiplicity
import NLS.ZakharovShabat.ClassicalIntervalCounting
import NLS.ZakharovShabat.AuxiliaryEigenvalueAsymptotics

/-!
# Physical auxiliary algebraic counts and analytic high-index branches

Spectral clusters and multiplicities are defined in the actual physical spaces.
A common physical neighborhood and every larger cutoff support both central
counts and simple high-disc eigenvalues. The high-index branches are analytic
and equal the actual auxiliary coefficient trace branches. The central box
uses the proved safe height; the printed general-p height remains separate.
-/

noncomputable section
open MeasureTheory Set Metric
namespace NLS.ZakharovShabat
namespace BoundaryCondition

theorem finite_classicalAuxiliarySpectrum_inter_of_isBounded (b : BoundaryCondition) (u : IntervalPairL2)
    {K : Set ℂ} (hK : Bornology.IsBounded K) : Set.Finite (classicalAuxiliarySpectrum b u ∩ K) := by
  rw [classicalAuxiliarySpectrum_eq_eigenvalues]
  exact finite_classicalAuxiliaryEigenvalues_inter_of_isBounded b _ (memLp_intervalL2Representative u) hK

/-- The actual physical auxiliary spectral cluster in the central box. -/
def classicalAuxiliaryCentralSpectrum (b : BoundaryCondition) (u : IntervalPairL2) (N : ℕ) : Finset ℂ :=
  (finite_classicalAuxiliarySpectrum_inter_of_isBounded b u (isBounded_centralSpectralBox N)).toFinset

@[simp] theorem mem_classicalAuxiliaryCentralSpectrum (b : BoundaryCondition) (u : IntervalPairL2) (N : ℕ) (z : ℂ) :
    z ∈ classicalAuxiliaryCentralSpectrum b u N ↔ z ∈ classicalAuxiliarySpectrum b u ∧ z ∈ centralSpectralBox N :=
  Set.Finite.mem_toFinset _

theorem classicalAuxiliaryCentralSpectrum_eq (b : BoundaryCondition) (u : IntervalPairL2) (N : ℕ) :
    classicalAuxiliaryCentralSpectrum b u N = classicalCentralSpectrum b (intervalAuxiliaryPotential u) N := by
  ext z
  rw [mem_classicalAuxiliaryCentralSpectrum, mem_classicalCentralSpectrum, classicalAuxiliarySpectrum_eq_conjugate]

/-- The physical auxiliary high-index trace branch. -/
def classicalAuxiliaryEigenvalue (b : BoundaryCondition) (u : IntervalPairL2) (n : ℤ) : ℂ :=
  classicalEigenvalue b (intervalAuxiliaryPotential u) n

/-- This is the actual coefficient auxiliary trace branch for the source Neumann extension. -/
theorem classicalAuxiliaryEigenvalue_eq_auxiliaryEigenvalue (b : BoundaryCondition) (u : IntervalPairL2) (n : ℤ) :
    classicalAuxiliaryEigenvalue b u n = auxiliaryEigenvalue (by simp) b
      (neumannPotentialCoefficients (intervalL2Representative u) (memLp_intervalL2Representative u)) n := by
  rw [classicalAuxiliaryEigenvalue, classicalEigenvalue, intervalPotentialCoefficients_auxiliaryPotential]
  rfl

@[simp] theorem classicalAuxiliaryEigenvalue_zero (b : BoundaryCondition) (n : ℤ) :
    classicalAuxiliaryEigenvalue b 0 n = (Real.pi : ℂ) * n := by
  rw [classicalAuxiliaryEigenvalue, map_zero, classicalEigenvalue_zero]

end BoundaryCondition
open BoundaryCondition

/-- Actual physical auxiliary counts, with multiplicity defined by physical Jordan chains. -/
structure ClassicalAuxiliaryCountingData (u : IntervalPairL2) (N : ℕ) : Prop where
  spectrum_subset : ∀ b : BoundaryCondition,
    classicalAuxiliarySpectrum b u ⊆ centralSpectralBox N ∪ highSpectralDisks N (Real.pi / 4)
  central_multiplicity : ∀ b : BoundaryCondition,
    (∑ z ∈ classicalAuxiliaryCentralSpectrum b u N, classicalAuxiliaryAlgebraicMultiplicity b u z) = 2 * N + 1
  disk_simple : ∀ b : BoundaryCondition, ∀ n : ℤ, N < n.natAbs →
    classicalAuxiliarySpectrum b u ∩ ball ((Real.pi : ℂ) * n) (Real.pi / 4) = {classicalAuxiliaryEigenvalue b u n} ∧
      classicalAuxiliaryAlgebraicMultiplicity b u (classicalAuxiliaryEigenvalue b u n) = 1

/-- Ordinary physical counts transfer through the actual full-root-space equivalence. -/
theorem classicalAuxiliaryCountingData_of_classical (u : IntervalPairL2) (N : ℕ)
    (h : ClassicalBoundaryCountingData (intervalAuxiliaryPotential u) N) : ClassicalAuxiliaryCountingData u N := by
  constructor
  · intro b
    rw [classicalAuxiliarySpectrum_eq_conjugate]
    exact h.spectrum_subset b
  · intro b
    simp only [classicalAuxiliaryCentralSpectrum_eq, classicalAuxiliaryAlgebraicMultiplicity_eq]
    exact h.central_multiplicity b
  · intro b n hn
    simpa only [classicalAuxiliarySpectrum_eq_conjugate, classicalAuxiliaryAlgebraicMultiplicity_eq,
      classicalAuxiliaryEigenvalue] using h.disk_simple b n hn

/-- One physical open convex neighborhood gives both auxiliary counts at every larger cutoff
and analyticity of their actual high-index branches. -/
theorem exists_uniform_classicalAuxiliaryCountingData (u : IntervalPairL2) :
    ∃ N₀ : ℕ, ∃ U : Set IntervalPairL2,
      0 < N₀ ∧ IsOpen U ∧ Convex ℝ U ∧ u ∈ U ∧ 0 ∈ U ∧
      (∀ v ∈ U, ∀ N : ℕ, N₀ ≤ N → ClassicalAuxiliaryCountingData v N) ∧
      ∀ b : BoundaryCondition, ∀ n : ℤ, N₀ < n.natAbs →
        AnalyticOnNhd ℂ (fun v : IntervalPairL2 => classicalAuxiliaryEigenvalue b v n) U := by
  let F := intervalAuxiliaryPotential.toContinuousLinearEquiv.toContinuousLinearMap
  obtain ⟨N₀,U,hN,ho,hc,hu,h0,hcount,han⟩ := exists_uniform_classicalBoundaryCountingData (F u)
  refine ⟨N₀,F ⁻¹' U,hN,ho.preimage F.continuous,hc.linear_preimage (F.restrictScalars ℝ).toLinearMap,
    hu,by simpa only [Set.mem_preimage, map_zero] using h0,?_,?_⟩
  · intro v hv N hN'
    exact classicalAuxiliaryCountingData_of_classical v N (hcount (F v) hv N hN')
  · intro b n hn v hv
    exact (han b n hn (F v) hv).comp (F.analyticAt v)

/-- Each distant disc contains exactly one eigenvalue, simple in the physical algebraic sense. -/
theorem ClassicalAuxiliaryCountingData.disk_unique_simple {u : IntervalPairL2} {N : ℕ}
    (h : ClassicalAuxiliaryCountingData u N) (b : BoundaryCondition) (n : ℤ) (hn : N < n.natAbs) :
    ∃! z : ℂ, z ∈ classicalAuxiliarySpectrum b u ∧ z ∈ ball ((Real.pi : ℂ) * n) (Real.pi / 4) ∧
      classicalAuxiliaryAlgebraicMultiplicity b u z = 1 := by
  have he := h.disk_simple b n hn
  have hz : classicalAuxiliaryEigenvalue b u n ∈ classicalAuxiliarySpectrum b u ∩ ball ((Real.pi : ℂ) * n) (Real.pi / 4) := by
    rw [he.1]
    exact Set.mem_singleton _
  refine ⟨classicalAuxiliaryEigenvalue b u n, ⟨hz.1, hz.2, he.2⟩, ?_⟩
  intro w hw
  have hw' : w ∈ classicalAuxiliarySpectrum b u ∩ ball ((Real.pi : ℂ) * n) (Real.pi / 4) := ⟨hw.1, hw.2.1⟩
  rwa [he.1, Set.mem_singleton_iff] at hw'

end NLS.ZakharovShabat
