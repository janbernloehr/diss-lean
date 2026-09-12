import NLS.ZakharovShabat.ClassicalIntervalMultiplicity
import NLS.ZakharovShabat.ClassicalIntervalAnalytic

/-!
# Counting original physical boundary eigenvalues with algebraic multiplicity

The central finite set is defined from the original physical spectrum, and
multiplicity from the original physical root space. Their proved correspondence
with the coefficient problem transfers central counts and high-disk simplicity
on one common physical neighborhood. The box is the existing height-`N` box;
the overview theorem's different norm-dependent height remains separate.
-/

noncomputable section
open MeasureTheory Set Metric
namespace NLS.ZakharovShabat
namespace BoundaryCondition

/-- Only finitely many original physical spectral points lie in a bounded region. -/
theorem finite_classicalSpectrum_inter_of_isBounded (b : BoundaryCondition) (u : IntervalPairL2)
    {K : Set ℂ} (hK : Bornology.IsBounded K) : Set.Finite (classicalSpectrum b u ∩ K) := by
  rw [classicalSpectrum_eq_classicalEigenvalues]
  exact finite_classicalEigenvalues_inter_of_isBounded b _ (memLp_intervalL2Representative u) hK

/-- The actual original spectral points in the central box, with no coefficient spectrum in the definition. -/
def classicalCentralSpectrum (b : BoundaryCondition) (u : IntervalPairL2) (N : ℕ) : Finset ℂ :=
  (finite_classicalSpectrum_inter_of_isBounded b u (isBounded_centralSpectralBox N)).toFinset

@[simp] theorem mem_classicalCentralSpectrum (b : BoundaryCondition) (u : IntervalPairL2) (N : ℕ) (z : ℂ) :
    z ∈ classicalCentralSpectrum b u N ↔ z ∈ classicalSpectrum b u ∧ z ∈ centralSpectralBox N :=
  Set.Finite.mem_toFinset _

/-- The physical central set and the coefficient central set agree exactly. -/
theorem classicalCentralSpectrum_eq (b : BoundaryCondition) (u : IntervalPairL2) (N : ℕ) :
    classicalCentralSpectrum b u N = centralSpectrum b (by simp) (intervalPotentialCoefficients u)
      (intervalPotentialCoefficients_mem u) N := by
  ext z
  rw [mem_classicalCentralSpectrum, mem_centralSpectrum, classicalSpectrum_eq_boundarySpectrum]

end BoundaryCondition
open BoundaryCondition

/-- The two original physical spectral counts, using physical root-space multiplicities. -/
structure ClassicalBoundaryCountingData (u : IntervalPairL2) (N : ℕ) : Prop where
  spectrum_subset : ∀ b : BoundaryCondition,
    classicalSpectrum b u ⊆ centralSpectralBox N ∪ highSpectralDisks N (Real.pi / 4)
  central_multiplicity : ∀ b : BoundaryCondition,
    (∑ z ∈ classicalCentralSpectrum b u N, classicalAlgebraicMultiplicity b u z) = 2 * N + 1
  disk_simple : ∀ b : BoundaryCondition, ∀ n : ℤ, N < n.natAbs →
    classicalSpectrum b u ∩ ball ((Real.pi : ℂ) * n) (Real.pi / 4) = {classicalEigenvalue b u n} ∧
      classicalAlgebraicMultiplicity b u (classicalEigenvalue b u n) = 1

/-- Coefficient counting transfers to the independently defined original spectrum and multiplicities. -/
theorem classicalBoundaryCountingData_of_coefficient (u : IntervalPairL2) (N : ℕ)
    (h : BoundaryCountingData (by simp) (intervalPotentialCoefficients u) (intervalPotentialCoefficients_mem u) N) :
    ClassicalBoundaryCountingData u N := by
  constructor
  · intro b
    rw [classicalSpectrum_eq_boundarySpectrum]
    exact h.spectrum_subset b
  · intro b
    simp only [classicalCentralSpectrum_eq, classicalAlgebraicMultiplicity_eq]
    exact h.central_multiplicity b
  · intro b n hn
    constructor
    · rw [classicalSpectrum_eq_classicalEigenvalues]
      exact classicalEigenvalues_inter_disk b u h n hn
    · rw [classicalAlgebraicMultiplicity_eq]
      exact (h.eigenvalue_spec b n hn).2

/-- The Hilbert realization of the common counting neighborhood and analytic simple branches. -/
theorem exists_uniform_classicalBoundaryCountingData (u : IntervalPairL2) :
    ∃ N₀ : ℕ, ∃ U : Set IntervalPairL2,
      0 < N₀ ∧ IsOpen U ∧ Convex ℝ U ∧ u ∈ U ∧ 0 ∈ U ∧
      (∀ v ∈ U, ∀ N : ℕ, N₀ ≤ N → ClassicalBoundaryCountingData v N) ∧
      ∀ b : BoundaryCondition, ∀ n : ℤ, N₀ < n.natAbs →
        AnalyticOnNhd ℂ (fun v : IntervalPairL2 => classicalEigenvalue b v n) U := by
  obtain ⟨N₀, U, hN₀, ho, hc, hu, h0, hdata, han⟩ := exists_uniform_analytic_classicalEigenvalues u
  exact ⟨N₀, U, hN₀, ho, hc, hu, h0,
    fun v hv N hN => classicalBoundaryCountingData_of_coefficient v N (hdata v hv N hN),
    fun b n hn => (han b n hn).1⟩

/-- Every original high disk contains one algebraically simple eigenvalue of the physical operator. -/
theorem ClassicalBoundaryCountingData.disk_unique_simple {u : IntervalPairL2} {N : ℕ}
    (h : ClassicalBoundaryCountingData u N) (b : BoundaryCondition) (n : ℤ) (hn : N < n.natAbs) :
    ∃! z : ℂ, z ∈ classicalSpectrum b u ∧ z ∈ ball ((Real.pi : ℂ) * n) (Real.pi / 4) ∧
      classicalAlgebraicMultiplicity b u z = 1 := by
  have he := h.disk_simple b n hn
  have hz : classicalEigenvalue b u n ∈ classicalSpectrum b u ∩ ball ((Real.pi : ℂ) * n) (Real.pi / 4) := by
    rw [he.1]
    exact Set.mem_singleton _
  refine ⟨classicalEigenvalue b u n, ⟨hz.1, hz.2, he.2⟩, ?_⟩
  intro w hw
  have hw' : w ∈ classicalSpectrum b u ∩ ball ((Real.pi : ℂ) * n) (Real.pi / 4) := ⟨hw.1, hw.2.1⟩
  rwa [he.1, Set.mem_singleton_iff] at hw'

end NLS.ZakharovShabat
