import NLS.ZakharovShabat.SourceAuxiliaryRootSpaces
import NLS.ZakharovShabat.SourceAuxiliaryReality
import NLS.ZakharovShabat.AuxiliaryCounting

/-!
# Original auxiliary algebraic counts in admissible central boxes

The finite clusters below consist of actual restricted spectral values. Their
multiplicities are dimensions of the full original Jordan root spaces. One
open convex connected neighborhood of the original interval input and zero
supports both signs and all larger cutoffs: central multiplicity 2N+1, one
simple eigenvalue in each high disk, and no further spectrum.

The central box has height N. This does not assert the norm-dependent height
printed in Proposition 5.2. The proof's final 2N-1 auxiliary N count is refuted.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
open BoundaryCondition
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual original auxiliary spectrum in the central box of height N. -/
def sourceAuxiliaryCentralSpectrum (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .neumann) (N : ℕ) : Finset ℂ :=
  (finite_sourceAuxiliarySpectrum_inter b hp φ hφ (isBounded_centralSpectralBox N)).toFinset

/-- The actual original auxiliary spectrum in a bounded disk. -/
def sourceAuxiliaryEnclosedSpectrum (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .neumann) (c : ℂ) (r : ℝ) : Finset ℂ :=
  (finite_sourceAuxiliarySpectrum_inter b hp φ hφ (Metric.isBounded_ball (x := c) (r := r))).toFinset

theorem mem_sourceAuxiliaryCentralSpectrum (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .neumann) (N : ℕ) (z : ℂ) :
    z ∈ sourceAuxiliaryCentralSpectrum b hp φ hφ N ↔
      z ∈ sourceAuxiliarySpectrum b hp φ hφ ∧ z ∈ centralSpectralBox N := Set.Finite.mem_toFinset _

theorem mem_sourceAuxiliaryEnclosedSpectrum (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .neumann) (c z : ℂ) (r : ℝ) :
    z ∈ sourceAuxiliaryEnclosedSpectrum b hp φ hφ c r ↔
      z ∈ sourceAuxiliarySpectrum b hp φ hφ ∧ z ∈ Metric.ball c r := Set.Finite.mem_toFinset _

theorem sourceAuxiliaryCentralSpectrum_eq (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .neumann) (N : ℕ) :
    sourceAuxiliaryCentralSpectrum b hp φ hφ N = b.auxiliaryCentralSpectrum hp (CoeffPair.toMax p φ) hφ N := by
  ext z
  rw [mem_sourceAuxiliaryCentralSpectrum, sourceAuxiliarySpectrum_eq]
  exact (b.mem_auxiliaryCentralSpectrum hp (CoeffPair.toMax p φ) hφ N z).symm

theorem sourceAuxiliaryEnclosedSpectrum_eq (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .neumann) (c : ℂ) (r : ℝ) :
    sourceAuxiliaryEnclosedSpectrum b hp φ hφ c r = b.auxiliaryEnclosedSpectrum hp (CoeffPair.toMax p φ) hφ c r := by
  ext z
  rw [mem_sourceAuxiliaryEnclosedSpectrum, sourceAuxiliarySpectrum_eq]
  exact (b.mem_auxiliaryEnclosedSpectrum hp (CoeffPair.toMax p φ) hφ c z r).symm

/-- All counts refer to the actual original spectrum and full Jordan multiplicities. -/
structure SourceAuxiliaryCountingData (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hφ : φ ∈ sourceBoundaryBaseSubspace .neumann) (N : ℕ) : Prop where
  spectrum_subset : ∀ b : BoundaryCondition,
    sourceAuxiliarySpectrum b hp φ hφ ⊆ centralSpectralBox N ∪ highSpectralDisks N (Real.pi/4)
  central_multiplicity : ∀ b : BoundaryCondition,
    (∑ z ∈ sourceAuxiliaryCentralSpectrum b hp φ hφ N, sourceAuxiliaryAlgebraicMultiplicity b hp φ hφ z) = 2*N+1
  disk_multiplicity : ∀ b : BoundaryCondition, ∀ n : ℤ, N < n.natAbs →
    (∑ z ∈ sourceAuxiliaryEnclosedSpectrum b hp φ hφ ((Real.pi : ℂ)*n) (Real.pi/4),
      sourceAuxiliaryAlgebraicMultiplicity b hp φ hφ z) = 1
  eigenvalue_spec : ∀ b : BoundaryCondition, ∀ n : ℤ, N < n.natAbs →
    ∃ z : ℂ, sourceAuxiliaryEnclosedSpectrum b hp φ hφ ((Real.pi : ℂ)*n) (Real.pi/4) = {z} ∧
      sourceAuxiliaryAlgebraicMultiplicity b hp φ hφ z = 1

/-- Transfer counts only after proving equality of the actual full root spaces. -/
theorem sourceAuxiliaryCountingData_of_coefficients (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hφ : φ ∈ sourceBoundaryBaseSubspace .neumann) (N : ℕ)
    (h : AuxiliaryCountingData hp (CoeffPair.toMax p φ) hφ N) : SourceAuxiliaryCountingData hp φ hφ N := by
  constructor
  · intro b
    rw [sourceAuxiliarySpectrum_eq]
    exact h.spectrum_subset b
  · intro b
    simp only [sourceAuxiliaryCentralSpectrum_eq, sourceAuxiliaryAlgebraicMultiplicity_eq]
    exact h.central_multiplicity b
  · intro b n hn
    simp only [sourceAuxiliaryEnclosedSpectrum_eq, sourceAuxiliaryAlgebraicMultiplicity_eq]
    exact h.disk_multiplicity b n hn
  · intro b n hn
    simp only [sourceAuxiliaryEnclosedSpectrum_eq, sourceAuxiliaryAlgebraicMultiplicity_eq]
    exact ⟨auxiliaryEigenvalue hp b (CoeffPair.toMax p φ) n, h.eigenvalue_spec b n hn⟩

/-- Every high disk has exactly one spectral point, with original algebraic multiplicity one. -/
theorem SourceAuxiliaryCountingData.disk_unique_simple {hp : p ≠ ⊤} {φ : CoeffPair p}
    {hφ : φ ∈ sourceBoundaryBaseSubspace .neumann} {N : ℕ}
    (h : SourceAuxiliaryCountingData hp φ hφ N) (b : BoundaryCondition) (n : ℤ) (hn : N < n.natAbs) :
    ∃ z : ℂ, z ∈ sourceAuxiliarySpectrum b hp φ hφ ∧ z ∈ Metric.ball ((Real.pi : ℂ)*n) (Real.pi/4) ∧
      sourceAuxiliaryAlgebraicMultiplicity b hp φ hφ z = 1 ∧
      ∀ w ∈ sourceAuxiliarySpectrum b hp φ hφ, w ∈ Metric.ball ((Real.pi : ℂ)*n) (Real.pi/4) → w = z := by
  obtain ⟨z, hz, hm⟩ := h.eigenvalue_spec b n hn
  have hmem : z ∈ sourceAuxiliaryEnclosedSpectrum b hp φ hφ ((Real.pi : ℂ)*n) (Real.pi/4) := by simp [hz]
  obtain ⟨hs, hb⟩ := (mem_sourceAuxiliaryEnclosedSpectrum b hp φ hφ _ z _).mp hmem
  refine ⟨z, hs, hb, hm, ?_⟩
  intro w hws hwb
  have hw := (mem_sourceAuxiliaryEnclosedSpectrum b hp φ hφ _ w _).mpr ⟨hws,hwb⟩
  simpa only [hz, Finset.mem_singleton] using hw

/-- Both auxiliary problems share one original-input neighborhood and all larger cutoffs. -/
theorem exists_uniform_sourceAuxiliaryCountingData (hp1 : 1 < p) (hp : p ≠ ⊤) (φ : CoeffPair p) :
    ∃ N₀ : ℕ, ∃ U : Set (CoeffPair p), 0 < N₀ ∧ IsOpen U ∧ Convex ℝ U ∧ IsConnected U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ N : ℕ, N₀ ≤ N → SourceAuxiliaryCountingData hp
        (sourceAuxiliaryReflectedPotential hp1 hp ψ) (sourceAuxiliaryReflectedPotential_mem hp1 hp ψ) N := by
  obtain ⟨N₀,U,hN,ho,hc,hφ,h0,hcount⟩ := exists_uniform_auxiliaryPeriodOneCountingData hp hp1 φ
  refine ⟨N₀,U,hN,ho,hc,⟨⟨0,h0⟩,hc.isPreconnected⟩,hφ,h0,?_⟩
  intro ψ hψ N hN'
  apply sourceAuxiliaryCountingData_of_coefficients
  have hh := hcount ψ hψ N hN'
  simpa only [toMax_sourceAuxiliaryReflectedPotential] using hh

/-- The final printed 2N-1 auxiliary N count contradicts the proved original count. -/
theorem SourceAuxiliaryCountingData.neumann_count_ne_printed {hp : p ≠ ⊤} {φ : CoeffPair p}
    {hφ : φ ∈ sourceBoundaryBaseSubspace .neumann} {N : ℕ}
    (h : SourceAuxiliaryCountingData hp φ hφ N) :
    (∑ z ∈ sourceAuxiliaryCentralSpectrum .neumann hp φ hφ N,
      sourceAuxiliaryAlgebraicMultiplicity .neumann hp φ hφ z) ≠ 2*N-1 := by
  rw [h.central_multiplicity]
  omega

/-- A zero-input counterexample to the proof's final auxiliary N count, at every large cutoff. -/
theorem exists_sourceAuxiliaryZero_count_ne_printed (hp1 : 1 < p) (hp : p ≠ ⊤) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      (∑ z ∈ sourceAuxiliaryCentralSpectrum .neumann hp
        (sourceAuxiliaryReflectedPotential hp1 hp 0) (sourceAuxiliaryReflectedPotential_mem hp1 hp 0) N,
        sourceAuxiliaryAlgebraicMultiplicity .neumann hp
          (sourceAuxiliaryReflectedPotential hp1 hp 0) (sourceAuxiliaryReflectedPotential_mem hp1 hp 0) z) ≠ 2*N-1 := by
  obtain ⟨N₀,U,hN,_,_,_,_,h0,hcount⟩ := exists_uniform_sourceAuxiliaryCountingData hp1 hp 0
  exact ⟨N₀,hN,fun N h => (hcount 0 h0 N h).neumann_count_ne_printed⟩

end NLS.ZakharovShabat
