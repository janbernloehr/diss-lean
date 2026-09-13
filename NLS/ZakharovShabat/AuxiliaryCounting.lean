import NLS.ZakharovShabat.AuxiliaryRootSpaces
import NLS.ZakharovShabat.AuxiliaryEigenvalueAsymptotics

/-!
# Auxiliary spectral multiplicity counts

The finite clusters are defined from the actual auxiliary spectrum, and their
multiplicities from actual auxiliary root chains. Both auxiliary problems have
one simple eigenvalue in each distant disc and central count `2N+1`, uniformly
on a common neighborhood and for every larger cutoff. The central box is the
proved safe box; this does not assert the unresolved printed general-p height.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
namespace BoundaryCondition
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] (b : BoundaryCondition)

/-- The actual auxiliary spectrum in a bounded open disc. -/
def auxiliaryEnclosedSpectrum (hp : p ≠ ⊤) (φ : PairSpace p) (hφ : φ ∈ neumannSubspace)
    (c : ℂ) (r : ℝ) : Finset ℂ :=
  (finite_auxiliarySpectrum_inter_of_isBounded b hp φ hφ (Metric.isBounded_ball (x := c) (r := r))).toFinset

/-- The actual auxiliary spectrum in the proved central box. -/
def auxiliaryCentralSpectrum (hp : p ≠ ⊤) (φ : PairSpace p) (hφ : φ ∈ neumannSubspace)
    (N : ℕ) : Finset ℂ :=
  (finite_auxiliarySpectrum_inter_of_isBounded b hp φ hφ (isBounded_centralSpectralBox N)).toFinset

theorem mem_auxiliaryEnclosedSpectrum (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ neumannSubspace) (c z : ℂ) (r : ℝ) :
    z ∈ auxiliaryEnclosedSpectrum b hp φ hφ c r ↔ z ∈ auxiliarySpectrum b hp φ hφ ∧ z ∈ Metric.ball c r :=
  Set.Finite.mem_toFinset _

theorem mem_auxiliaryCentralSpectrum (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ neumannSubspace) (N : ℕ) (z : ℂ) :
    z ∈ auxiliaryCentralSpectrum b hp φ hφ N ↔ z ∈ auxiliarySpectrum b hp φ hφ ∧ z ∈ centralSpectralBox N :=
  Set.Finite.mem_toFinset _

theorem auxiliaryEnclosedSpectrum_eq (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ neumannSubspace) (c : ℂ) (r : ℝ) : auxiliaryEnclosedSpectrum b hp φ hφ c r =
      enclosedSpectrum b hp (auxiliaryPotential φ) ((auxiliaryPotential_mem_dirichlet_iff φ).mpr hφ) c r := by
  ext z
  rw [mem_auxiliaryEnclosedSpectrum, mem_enclosedSpectrum, auxiliarySpectrum_eq]

theorem auxiliaryCentralSpectrum_eq (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ neumannSubspace) (N : ℕ) : auxiliaryCentralSpectrum b hp φ hφ N =
      centralSpectrum b hp (auxiliaryPotential φ) ((auxiliaryPotential_mem_dirichlet_iff φ).mpr hφ) N := by
  ext z
  rw [mem_auxiliaryCentralSpectrum, mem_centralSpectrum, auxiliarySpectrum_eq]

end BoundaryCondition
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Counts and localization for both actual auxiliary restrictions at one cutoff. -/
structure AuxiliaryCountingData (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ neumannSubspace) (N : ℕ) : Prop where
  spectrum_subset : ∀ b : BoundaryCondition,
    b.auxiliarySpectrum hp φ hφ ⊆ centralSpectralBox N ∪ highSpectralDisks N (Real.pi / 4)
  central_multiplicity : ∀ b : BoundaryCondition,
    (∑ z ∈ b.auxiliaryCentralSpectrum hp φ hφ N, b.auxiliaryAlgebraicMultiplicity hp φ hφ z) = 2 * N + 1
  disk_multiplicity : ∀ b : BoundaryCondition, ∀ n : ℤ, N < n.natAbs →
    (∑ z ∈ b.auxiliaryEnclosedSpectrum hp φ hφ ((Real.pi : ℂ) * n) (Real.pi / 4),
      b.auxiliaryAlgebraicMultiplicity hp φ hφ z) = 1
  eigenvalue_spec : ∀ b : BoundaryCondition, ∀ n : ℤ, N < n.natAbs →
    b.auxiliaryEnclosedSpectrum hp φ hφ ((Real.pi : ℂ) * n) (Real.pi / 4) = {auxiliaryEigenvalue hp b φ n} ∧
      b.auxiliaryAlgebraicMultiplicity hp φ hφ (auxiliaryEigenvalue hp b φ n) = 1

/-- Ordinary counts transfer through the proved chain equivalence. -/
theorem auxiliaryCountingData_of_boundary (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ neumannSubspace) {N : ℕ}
    (h : BoundaryCountingData hp (auxiliaryPotential φ) ((auxiliaryPotential_mem_dirichlet_iff φ).mpr hφ) N) :
    AuxiliaryCountingData hp φ hφ N := by
  constructor
  · intro b
    rw [BoundaryCondition.auxiliarySpectrum_eq]
    exact h.spectrum_subset b
  · intro b
    simp only [BoundaryCondition.auxiliaryCentralSpectrum_eq, BoundaryCondition.auxiliaryAlgebraicMultiplicity_eq]
    exact h.central_multiplicity b
  · intro b n hn
    simp only [BoundaryCondition.auxiliaryEnclosedSpectrum_eq, BoundaryCondition.auxiliaryAlgebraicMultiplicity_eq]
    exact h.disk_multiplicity b n hn
  · intro b n hn
    simp only [BoundaryCondition.auxiliaryEnclosedSpectrum_eq, BoundaryCondition.auxiliaryAlgebraicMultiplicity_eq,
      auxiliaryEigenvalue]
    exact h.eigenvalue_spec b n hn

/-- One open convex neighborhood of a reflected potential and zero supports both
auxiliary algebraic counts at every larger cutoff. -/
theorem exists_uniform_auxiliaryCountingData (hp : p ≠ ⊤) (φ : neumannSubspace (p := p)) :
    ∃ N₀ : ℕ, ∃ U : Set (neumannSubspace (p := p)),
      0 < N₀ ∧ IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ N : ℕ, N₀ ≤ N → AuxiliaryCountingData hp ψ.val ψ.property N := by
  let F := auxiliaryPotentialToDirichlet (p := p)
  obtain ⟨N₀, U, hN, ho, hc, hφ, h0, hcount, _⟩ :=
    exists_uniform_analytic_boundaryEigenvalues hp (F φ)
  refine ⟨N₀, F ⁻¹' U, hN, ho.preimage F.continuous,
    hc.linear_preimage (F.restrictScalars ℝ).toLinearMap, hφ, ?_, ?_⟩
  · simpa only [Set.mem_preimage, map_zero] using h0
  · intro ψ hψ N hN'
    exact auxiliaryCountingData_of_boundary hp ψ.val ψ.property (hcount (F ψ) hψ N hN')

/-- The same counted auxiliary conclusions for original period-one coefficient
potentials, using the source Neumann extension for both boundary conditions. -/
theorem exists_uniform_auxiliaryPeriodOneCountingData (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ N₀ : ℕ, ∃ U : Set (CoeffPair p),
      0 < N₀ ∧ IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ N : ℕ, N₀ ≤ N →
        AuxiliaryCountingData hp (auxiliaryPeriodOnePotential hp hp1 ψ).val
          (auxiliaryPeriodOnePotential hp hp1 ψ).property N := by
  let F := auxiliaryPeriodOnePotential hp hp1
  obtain ⟨N₀, U, hN, ho, hc, hφ, h0, hcount⟩ := exists_uniform_auxiliaryCountingData hp (F φ)
  refine ⟨N₀, F ⁻¹' U, hN, ho.preimage F.continuous,
    hc.linear_preimage (F.restrictScalars ℝ).toLinearMap, hφ, ?_, ?_⟩
  · simpa only [Set.mem_preimage, map_zero] using h0
  · intro ψ hψ N hN'
    exact hcount (F ψ) hψ N hN'

end NLS.ZakharovShabat
