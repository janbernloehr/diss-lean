import NLS.ZakharovShabat.DiskMultiplicity
import NLS.ZakharovShabat.PeriodicParity

/-!
# Parity of the high-frequency periodic eigenvalues

For even-supported potentials, a spectral disk about `π n` has its entire root
space in Fourier parity `n`. We deform the complementary parity projection
from zero, using the norm gap between zero and a nonzero idempotent. This proves
the parity assertion of Proposition 1.1(i), including generalized eigenvectors.
-/

noncomputable section
open Complex Metric Topology
open scoped ENNReal

namespace NLS.ZakharovShabat

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Both resonant free coefficients have the parity of their spectral index. -/
theorem freeModeEmbedding_mem_pairParitySubspace (n : ℤ) (a : ℂ × ℂ) :
    freeModeEmbedding (p := p) n a ∈ pairParitySubspace n := by
  constructor
  · exact Coeff.single_mem_paritySubspace n (-n) a.1 (by omega)
  · exact Coeff.single_mem_paritySubspace n n a.2 rfl

/-- An isolated free disk has its whole contour range in the corresponding parity. -/
theorem range_free_diskContour_le_parity (hp : p ≠ ⊤) (n : ℤ) {r : ℝ}
    (hr : 0 < r) (hrπ : r ≤ Real.pi)
    (hc : sphere ((Real.pi : ℂ) * n) r ⊆ resolventSet (p := p) hp 0) :
    (resolventCircleIntegral hp 0 ((Real.pi : ℂ) * n) r).range ≤ pairParitySubspace n := by
  rw [resolventCircleIntegral_eq_projection_of_singleton hp 0 _ _ r hr.le hc
    (enclosedPeriodicSpectrum_zero hp n hr hrπ), range_periodicSpectralProjection,
    periodicRootSpaceTop_zero_eq_range]
  rintro x ⟨a, rfl⟩
  exact freeModeEmbedding_mem_pairParitySubspace n a

/-- On a preconnected family of even potentials containing zero, a common
isolating circle retains the free parity of its entire range. -/
theorem range_diskContour_le_parity_on_preconnected (hp : p ≠ ⊤) (n : ℤ) {r : ℝ}
    (hr : 0 < r) (hrπ : r ≤ Real.pi) {U : Set (PairSpace p)}
    (hU : IsPreconnected U) (heven : ∀ ψ ∈ U, ψ ∈ pairParitySubspace 0)
    (hc : ∀ ψ ∈ U, sphere ((Real.pi : ℂ) * n) r ⊆ resolventSet hp ψ)
    (h0 : (0 : PairSpace p) ∈ U) {φ : PairSpace p} (hφ : φ ∈ U) :
    (resolventCircleIntegral hp φ ((Real.pi : ℂ) * n) r).range ≤ pairParitySubspace n := by
  let P := fun ψ : PairSpace p => resolventCircleIntegral hp ψ ((Real.pi : ℂ) * n) r
  let A := pairParityProjection (p := p) n
  have hcont : ContinuousOn P U := fun ψ hψ =>
    (analyticAt_resolventCircleIntegral hp ψ _ r hr.le (hc ψ hψ)).continuousAt.continuousWithinAt
  have hbase : A * P 0 = P 0 := by
    apply ContinuousLinearMap.ext
    intro x
    exact (pairParityProjection_eq_self_iff n _).mpr
      (range_free_diskContour_le_parity hp n hr hrπ (hc 0 h0) ⟨x, rfl⟩)
  have he := NLS.ProjectionRank.mul_eq_self_on_preconnected hU P hcont
    (fun ψ hψ => resolventCircleIntegral_idempotent hp ψ _ r hr.le (hc ψ hψ))
    A (pairParityProjection_idempotent n)
    (fun ψ hψ => pairParityProjection_commute_contour hp ψ (heven ψ hψ) n _ r hr.le (hc ψ hψ))
    h0 hbase φ hφ
  rintro x ⟨a, rfl⟩
  exact (pairParityProjection_eq_self_iff n _).mp (DFunLike.congr_fun he a)

/-- Range containment for a contour implies the same containment for every full
root space whose spectral parameter lies inside it. -/
theorem periodicRootSpaceTop_le_parity_of_contour (hp : p ≠ ⊤) (φ : PairSpace p)
    (c z : ℂ) (r : ℝ) (n : ℤ) (hc : sphere c r ⊆ resolventSet hp φ)
    (hz : z ∈ ball c r)
    (hpar : (resolventCircleIntegral hp φ c r).range ≤ pairParitySubspace n) :
    periodicRootSpaceTop hp φ z ≤ pairParitySubspace n := by
  intro x hx
  exact hpar ⟨x, resolventCircleIntegral_apply_root hp φ c z r hc hz x hx⟩

/-- A contour whose range has one parity annihilates inputs of the other parity. -/
theorem resolventCircleIntegral_eq_zero_of_opposite_parity (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : sphere c r ⊆ resolventSet hp φ) (n m : ℤ) (hnm : n % 2 ≠ m % 2)
    (hpar : (resolventCircleIntegral hp φ c r).range ≤ pairParitySubspace n)
    (x : PairSpace p) (hx : x ∈ pairParitySubspace m) :
    resolventCircleIntegral hp φ c r x = 0 := by
  exact Submodule.disjoint_def.mp (disjoint_pairParitySubspaces n m hnm) _
    (hpar ⟨x, rfl⟩)
    (resolventCircleIntegral_mem_pairParitySubspace hp φ hφ m c r hr hc x hx)

/-- Ordinary eigenfunctions inherit root-space parity in the weighted domain. -/
theorem eigenvector_mem_domainParitySubspace_of_root_le (hp : p ≠ ⊤) (φ : PairSpace p)
    (z : ℂ) (n : ℤ) (hpar : periodicRootSpaceTop hp φ z ≤ pairParitySubspace n)
    (f : Domain p) (hf : operator hp φ f = z • domainInclusion f) :
    f ∈ domainParitySubspace n := by
  rw [mem_domainParitySubspace]
  apply hpar
  apply (mem_periodicRootSpaceTop hp φ z _).mpr
  refine ⟨1, (mem_periodicRootSpace_succ hp φ z 0 _).mpr ⟨f, rfl, ?_⟩⟩
  simp [spectralPencil_apply, hf]

/-- Proposition 1.1(i), including parity: one cutoff and an open convex ambient
neighborhood give rank two and total multiplicity two; for its even potentials,
the entire contour range and all enclosed root spaces have Fourier parity `n`. -/
theorem exists_uniform_disk_multiplicity_and_parity (hp : p ≠ ⊤) (φ : PairSpace p)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi / 4) :
    ∃ N : ℕ, ∃ U : Set (PairSpace p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ n : ℤ, N ≤ n.natAbs →
        sphere ((Real.pi : ℂ) * n) r ⊆ resolventSet hp ψ ∧
        Module.finrank ℂ (resolventCircleIntegral hp ψ ((Real.pi : ℂ) * n) r).range = 2 ∧
        (∑ z ∈ enclosedPeriodicSpectrum hp ψ ((Real.pi : ℂ) * n) r,
          periodicAlgebraicMultiplicity hp ψ z) = 2 ∧
        (ψ ∈ pairParitySubspace 0 →
          (resolventCircleIntegral hp ψ ((Real.pi : ℂ) * n) r).range ≤ pairParitySubspace n ∧
          ∀ z ∈ ball ((Real.pi : ℂ) * n) r, periodicRootSpaceTop hp ψ z ≤ pairParitySubspace n) := by
  obtain ⟨N, U, ho, hconv, hφ, h0, hcount⟩ :=
    exists_uniform_disk_multiplicity_two hp φ hr hrπ
  refine ⟨N, U, ho, hconv, hφ, h0, ?_⟩
  intro ψ hψ n hn
  obtain ⟨hc, hrank, hsum⟩ := hcount ψ hψ n hn
  refine ⟨hc, hrank, hsum, ?_⟩
  intro heven
  let V := U ∩ (pairParitySubspace (p := p) 0 : Set (PairSpace p))
  have hV : Convex ℝ V := hconv.inter ((pairParitySubspace (p := p) 0).restrictScalars ℝ).convex
  have hpar := range_diskContour_le_parity_on_preconnected hp n hr
    (by linarith [Real.pi_pos]) hV.isPreconnected (fun _ ha => ha.2)
    (fun a ha => (hcount a ha.1 n hn).1) ⟨h0, Submodule.zero_mem _⟩ ⟨hψ, heven⟩
  exact ⟨hpar, fun z hz => periodicRootSpaceTop_le_parity_of_contour hp ψ _ z r n hc hz hpar⟩

/-- For an even potential, every eigenfunction in a sufficiently far quarter-pi
disk has parity `n`: periodic for even `n`, antiperiodic for odd `n`, in coefficients. -/
theorem exists_highFrequency_eigenvector_parity (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) :
    ∃ N : ℕ, ∀ n : ℤ, N ≤ n.natAbs → ∀ z ∈ ball ((Real.pi : ℂ) * n) (Real.pi / 4),
      ∀ f : Domain p, operator hp φ f = z • domainInclusion f →
        f ∈ domainParitySubspace n := by
  obtain ⟨N, U, _, _, hφU, _, h⟩ :=
    exists_uniform_disk_multiplicity_and_parity hp φ (by positivity) le_rfl
  refine ⟨N, ?_⟩
  intro n hn z hz f hf
  exact eigenvector_mem_domainParitySubspace_of_root_le hp φ z n
    (((h φ hφU n hn).2.2.2 hφ).2 z hz) f hf

end NLS.ZakharovShabat
