import NLS.ZakharovShabat.BoundaryClusters
import NLS.ZakharovShabat.FreeBoundaryMultiplicity
import NLS.ZakharovShabat.PeriodicCounting

/-!
# Uniform Dirichlet and Neumann counts

For already-reflected coefficient potentials, one open convex neighborhood
joining the given potential to zero supports both boundary counts. Every high
disk contains one simple eigenvalue of each boundary restriction, and each
central box has `2N+1` eigenvalues counted algebraically for either condition.
The actual interval-extension maps in Lemmas 4.1–4.3 remain separate from this
coefficient form of the counting argument in Theorem 1.4.
-/

open Complex Metric Topology
open scoped ENNReal
noncomputable section
namespace NLS.ZakharovShabat
namespace BoundaryCondition
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] (b : BoundaryCondition)

/-- The actual boundary spectrum inside an open disk. -/
def enclosedSpectrum (hp : p ≠ ⊤) (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace)
    (c : ℂ) (r : ℝ) : Finset ℂ := by
  classical
  exact (enclosedPeriodicSpectrum hp φ c r).filter (fun z => z ∈ spectrum b hp φ hφ)

theorem mem_enclosedSpectrum (hp : p ≠ ⊤) (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace)
    (c z : ℂ) (r : ℝ) : z ∈ enclosedSpectrum b hp φ hφ c r ↔
      z ∈ spectrum b hp φ hφ ∧ z ∈ ball c r := by
  classical
  simp only [enclosedSpectrum, Finset.mem_filter, mem_enclosedPeriodicSpectrum]
  exact ⟨fun h => ⟨h.2, h.1.2⟩,
    fun h => ⟨⟨spectrum_subset_periodic b hp φ hφ h.1, h.2⟩, h.1⟩⟩

/-- The actual finite boundary spectrum in the central box. -/
def centralSpectrum (hp : p ≠ ⊤) (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace)
    (N : ℕ) : Finset ℂ := by
  classical
  exact (centralPeriodicSpectrum hp φ N).filter (fun z => z ∈ spectrum b hp φ hφ)

theorem mem_centralSpectrum (hp : p ≠ ⊤) (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace)
    (N : ℕ) (z : ℂ) : z ∈ centralSpectrum b hp φ hφ N ↔
      z ∈ spectrum b hp φ hφ ∧ z ∈ centralSpectralBox N := by
  classical
  simp only [centralSpectrum, Finset.mem_filter, mem_centralPeriodicSpectrum]
  exact ⟨fun h => ⟨h.2, h.1.2⟩,
    fun h => ⟨⟨spectrum_subset_periodic b hp φ hφ h.1, h.2⟩, h.1⟩⟩

/-- Removing parameters outside the individual boundary spectrum leaves multiplicity sums unchanged. -/
theorem sum_filter_spectrum (hp : p ≠ ⊤) (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace)
    (s : Finset ℂ) [DecidablePred (fun z => z ∈ spectrum b hp φ hφ)] :
    (∑ z ∈ s.filter (fun z => z ∈ spectrum b hp φ hφ), algebraicMultiplicity b hp φ hφ z) =
      ∑ z ∈ s, algebraicMultiplicity b hp φ hφ z := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z hz
  split_ifs with h
  · rfl
  · symm
    exact (algebraicMultiplicity_eq_zero_iff b hp φ hφ z).mpr (by simpa [spectrum] using h)

/-- The boundary component of the central algebraic projector. -/
def centralProjection (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ) :
    PairSpace p →L[ℂ] PairSpace p := ambientClusterProjection b hp φ (centralPeriodicSpectrum hp φ N)

/-- The central boundary component selects precisely the boundary part of the periodic range. -/
theorem range_centralProjection (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (N : ℕ) :
    (centralProjection b hp φ N).range = (centralSpectralProjection hp φ N).range ⊓ space b := by
  rw [centralProjection, range_ambientClusterProjection b hp φ hφ,
    centralSpectralProjection, range_periodicClusterProjection]

theorem finrank_range_centralProjection (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (N : ℕ) :
    Module.finrank ℂ (centralProjection b hp φ N).range =
      ∑ z ∈ centralSpectrum b hp φ hφ N, algebraicMultiplicity b hp φ hφ z := by
  classical
  rw [centralSpectrum, sum_filter_spectrum]
  exact finrank_range_ambientClusterProjection b hp φ hφ _

theorem finrank_range_centralProjection_zero (hp : p ≠ ⊤) (N : ℕ) :
    Module.finrank ℂ (centralProjection (p := p) b hp 0 N).range = 2 * N + 1 := by
  rw [centralProjection, finrank_range_ambientClusterProjection b hp 0 (by simp)]
  exact sum_central_multiplicity_zero b hp N

theorem analyticAt_centralProjection (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ)
    (ha : AnalyticAt ℂ (fun ψ => centralSpectralProjection hp ψ N) φ) :
    AnalyticAt ℂ (fun ψ => centralProjection b hp ψ N) φ :=
  analyticAt_const.mul ha

/-- Boundary contour rank is constant on a preconnected family of reflected potentials. -/
theorem finrank_contour_eq_on_preconnected (hp : p ≠ ⊤) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    {U : Set (PairSpace p)} (hU : IsPreconnected U) (hDir : U ⊆ (dirichletSubspace (p := p) : Set (PairSpace p)))
    (hc : ∀ ψ ∈ U, sphere c r ⊆ ZakharovShabat.resolventSet hp ψ)
    {φ ψ : PairSpace p} (hφ : φ ∈ U) (hψ : ψ ∈ U) :
    Module.finrank ℂ (contourProjection b hp φ c r).range =
      Module.finrank ℂ (contourProjection b hp ψ c r).range := by
  exact NLS.ProjectionRank.finrank_eq_on_preconnected hU
    (fun a => contourProjection b hp a c r)
    (fun a ha => (analyticAt_contourProjection b hp a c r hr (hc a ha)).continuousAt.continuousWithinAt)
    (fun a ha => contourProjection_idempotent b hp a (hDir ha) c r hr (hc a ha))
    (fun a ha => finiteDimensional_range_contourProjection b hp a c r hr (hc a ha)) hφ hψ

/-- The contour rank counts only the eigenvalues of the selected boundary restriction. -/
theorem finrank_contour_eq_sum_enclosed (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : sphere c r ⊆ ZakharovShabat.resolventSet hp φ) :
    Module.finrank ℂ (contourProjection b hp φ c r).range =
      ∑ z ∈ enclosedSpectrum b hp φ hφ c r, algebraicMultiplicity b hp φ hφ z := by
  classical
  rw [enclosedSpectrum, sum_filter_spectrum]
  exact finrank_range_contourProjection b hp φ hφ c r hr hc

end BoundaryCondition
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Both coefficient boundary counts with the same localization and cutoff. -/
structure BoundaryCountingData (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (N : ℕ) : Prop where
  periodic : PeriodicCountingData hp φ N
  central_rank : ∀ b : BoundaryCondition,
    Module.finrank ℂ (b.centralProjection hp φ N).range = 2 * N + 1
  central_multiplicity : ∀ b : BoundaryCondition,
    (∑ z ∈ b.centralSpectrum hp φ hφ N, b.algebraicMultiplicity hp φ hφ z) = 2 * N + 1
  disk_rank : ∀ b : BoundaryCondition, ∀ n : ℤ, N < n.natAbs →
    Module.finrank ℂ (b.contourProjection hp φ ((Real.pi : ℂ) * n) (Real.pi / 4)).range = 1
  disk_multiplicity : ∀ b : BoundaryCondition, ∀ n : ℤ, N < n.natAbs →
    (∑ z ∈ b.enclosedSpectrum hp φ hφ ((Real.pi : ℂ) * n) (Real.pi / 4),
      b.algebraicMultiplicity hp φ hφ z) = 1

/-- One neighborhood supports the central and high-disk boundary ranks, their analytic
projectors, and the same localization, for every larger cutoff. -/
theorem exists_uniform_boundaryCountingData (hp : p ≠ ⊤) (φ : PairSpace p) :
    ∃ N₀ : ℕ, ∃ U : Set (PairSpace p), 0 < N₀ ∧ IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      (∀ N : ℕ, N₀ ≤ N → ∀ b : BoundaryCondition,
        AnalyticOnNhd ℂ (fun ψ => b.centralProjection hp ψ N) U) ∧
      (∀ n : ℤ, N₀ < n.natAbs → ∀ b : BoundaryCondition,
        AnalyticOnNhd ℂ (fun ψ => b.contourProjection hp ψ ((Real.pi : ℂ) * n) (Real.pi / 4)) U) ∧
      ∀ ψ ∈ U, ∀ hψ : ψ ∈ dirichletSubspace, ∀ N : ℕ, N₀ ≤ N →
        BoundaryCountingData hp ψ hψ N := by
  obtain ⟨N₀, U, hN₀, ho, hconv, hφ, h0, hcentral, hdisk, hdata⟩ :=
    exists_uniform_periodicCountingData hp φ
  let V := U ∩ (dirichletSubspace (p := p) : Set (PairSpace p))
  have hV : Convex ℝ V := hconv.inter ((dirichletSubspace (p := p)).restrictScalars ℝ).convex
  have h0V : (0 : PairSpace p) ∈ V := ⟨h0, Submodule.zero_mem _⟩
  refine ⟨N₀, U, hN₀, ho, hconv, hφ, h0, ?_, ?_, ?_⟩
  · intro N hN b ψ hψ
    exact BoundaryCondition.analyticAt_centralProjection b hp ψ N ((hcentral N hN).1 ψ hψ)
  · intro n hn b ψ hψ
    exact BoundaryCondition.analyticAt_contourProjection b hp ψ _ _ (by positivity)
      ((hdata ψ hψ N₀ le_rfl).disk_resolvent n hn)
  · intro ψ hψ hDir N hN
    have hcentralRank (b : BoundaryCondition) :
        Module.finrank ℂ (b.centralProjection hp ψ N).range = 2 * N + 1 := by
      have heq := NLS.ProjectionRank.finrank_eq_on_preconnected hV.isPreconnected
        (fun a => b.centralProjection hp a N)
        (fun a ha => (BoundaryCondition.analyticAt_centralProjection b hp a N
          ((hcentral N hN).1 a ha.1)).continuousAt.continuousWithinAt)
        (fun a ha => BoundaryCondition.ambientClusterProjection_idempotent b hp a ha.2 _)
        (fun a _ => BoundaryCondition.finiteDimensional_range_ambientClusterProjection b hp a _)
        (show ψ ∈ V from ⟨hψ, hDir⟩) h0V
      exact heq.trans (BoundaryCondition.finrank_range_centralProjection_zero b hp N)
    have hdiskRank (b : BoundaryCondition) (n : ℤ) (hn : N < n.natAbs) :
        Module.finrank ℂ (b.contourProjection hp ψ ((Real.pi : ℂ) * n) (Real.pi / 4)).range = 1 := by
      have hc (a : PairSpace p) (ha : a ∈ U) := (hdata a ha N hN).disk_resolvent n hn
      have heq := BoundaryCondition.finrank_contour_eq_on_preconnected b hp
        ((Real.pi : ℂ) * n) (Real.pi / 4) (by positivity) hV.isPreconnected
        (fun _ ha => ha.2) (fun a ha => hc a ha.1) (show ψ ∈ V from ⟨hψ, hDir⟩) h0V
      rw [BoundaryCondition.range_contourProjection b hp 0 (by simp) _ _ (by positivity) (hc 0 h0),
        BoundaryCondition.finrank_free_contour_boundary] at heq
      exact heq
    refine ⟨hdata ψ hψ N hN, hcentralRank, ?_, hdiskRank, ?_⟩
    · intro b
      rw [← BoundaryCondition.finrank_range_centralProjection]
      exact hcentralRank b
    · intro b n hn
      rw [← BoundaryCondition.finrank_contour_eq_sum_enclosed b hp ψ hDir _ _
        (by positivity) ((hdata ψ hψ N hN).disk_resolvent n hn)]
      exact hdiskRank b n hn

namespace BoundaryCountingData
variable {hp : p ≠ ⊤} {φ : PairSpace p} {hφ : φ ∈ dirichletSubspace} {N : ℕ}

/-- No boundary eigenvalue lies outside the same central box and high disks. -/
theorem spectrum_subset (h : BoundaryCountingData hp φ hφ N) (b : BoundaryCondition) :
    b.spectrum hp φ hφ ⊆ centralSpectralBox N ∪ highSpectralDisks N (Real.pi / 4) :=
  (BoundaryCondition.spectrum_subset_periodic b hp φ hφ).trans h.periodic.spectrum_subset

/-- Each high disk contains exactly one boundary eigenvalue, and its algebraic multiplicity is one. -/
theorem disk_spectrum_eq_singleton (h : BoundaryCountingData hp φ hφ N)
    (b : BoundaryCondition) (n : ℤ) (hn : N < n.natAbs) :
    ∃ z : ℂ, b.enclosedSpectrum hp φ hφ ((Real.pi : ℂ) * n) (Real.pi / 4) = {z} ∧
      b.algebraicMultiplicity hp φ hφ z = 1 := by
  classical
  let s := b.enclosedSpectrum hp φ hφ ((Real.pi : ℂ) * n) (Real.pi / 4)
  have hsum : (∑ z ∈ s, b.algebraicMultiplicity hp φ hφ z) = 1 := h.disk_multiplicity b n hn
  have hcard : s.card ≤ 1 := by
    calc
      s.card = ∑ _z ∈ s, (1 : ℕ) := Finset.card_eq_sum_ones s
      _ ≤ ∑ z ∈ s, b.algebraicMultiplicity hp φ hφ z := by
        apply Finset.sum_le_sum
        intro z hz
        exact (BoundaryCondition.algebraicMultiplicity_pos_iff b hp φ hφ z).mpr
          ((BoundaryCondition.mem_enclosedSpectrum b hp φ hφ _ z _).mp hz).1
      _ = 1 := hsum
  have hpos : 0 < s.card := by
    by_contra hc
    have he : s = ∅ := Finset.card_eq_zero.mp (by omega)
    rw [he, Finset.sum_empty] at hsum
    omega
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp (show s.card = 1 by omega)
  exact ⟨z, hz, by simpa only [hz, Finset.sum_singleton] using hsum⟩

/-- The unique high-disk value is an actual simple eigenvalue of the selected restriction. -/
theorem disk_unique_simple (h : BoundaryCountingData hp φ hφ N)
    (b : BoundaryCondition) (n : ℤ) (hn : N < n.natAbs) :
    ∃! z : ℂ, z ∈ b.spectrum hp φ hφ ∧ z ∈ ball ((Real.pi : ℂ) * n) (Real.pi / 4) ∧
      b.algebraicMultiplicity hp φ hφ z = 1 := by
  obtain ⟨z, hz, hm⟩ := h.disk_spectrum_eq_singleton b n hn
  have hzmem : z ∈ b.enclosedSpectrum hp φ hφ ((Real.pi : ℂ) * n) (Real.pi / 4) := by simp [hz]
  obtain ⟨hspec, hball⟩ := (BoundaryCondition.mem_enclosedSpectrum b hp φ hφ _ z _).mp hzmem
  refine ⟨z, ⟨hspec, hball, hm⟩, ?_⟩
  intro w hw
  have hwmem := (BoundaryCondition.mem_enclosedSpectrum b hp φ hφ _ w _).mpr ⟨hw.1, hw.2.1⟩
  simpa [hz] using hwmem

end BoundaryCountingData
end NLS.ZakharovShabat
