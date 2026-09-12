import NLS.ZakharovShabat.CentralRectangle
import NLS.ZakharovShabat.FreeMultiplicity
import NLS.ZakharovShabat.SpectralClusters

/-!
# The finite central spectrum and its free multiplicity

The central box contains a finite set of periodic spectral values. For the free
operator these are exactly `π n` for `-N ≤ n ≤ N`, each of algebraic multiplicity
two. Thus the free central count in Proposition 1.1(ii) is `4N + 2`.
-/

noncomputable section
open Complex Metric Topology
open scoped ENNReal

namespace NLS.ZakharovShabat

/-- The mixed-boundary central box is bounded. -/
theorem isBounded_centralSpectralBox (N : ℕ) : Bornology.IsBounded (centralSpectralBox N) :=
  (isCompact_closedCentralRectangle N).isBounded.subset (fun _ hz => ⟨hz.1.le, hz.2⟩)

/-- A free lattice point lies in the central box exactly when its index is central. -/
theorem free_mem_centralSpectralBox_iff (N : ℕ) (n : ℤ) :
    (Real.pi : ℂ) * n ∈ centralSpectralBox N ↔ n.natAbs ≤ N := by
  have he : |(n : ℝ)| = (n.natAbs : ℝ) := by simp only [Nat.cast_natAbs, Int.cast_abs]
  change |((Real.pi : ℂ) * n).re| < _ ∧ |((Real.pi : ℂ) * n).im| ≤ _ ↔ _
  simp only [mul_re, ofReal_re, intCast_re, ofReal_im, intCast_im, mul_zero, sub_zero,
    mul_im, zero_mul, add_zero, abs_zero, Nat.cast_nonneg, and_true, abs_mul,
    abs_of_pos Real.pi_pos, he]
  constructor
  · intro h
    have hlt : (n.natAbs : ℝ) < (N : ℝ) + 1 := by nlinarith [Real.pi_pos]
    have hnat : n.natAbs < N + 1 := by exact_mod_cast hlt
    omega
  · intro h
    have hle : (n.natAbs : ℝ) ≤ (N : ℝ) := by exact_mod_cast h
    nlinarith [Real.pi_pos]

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The finite set of periodic spectral values in the central box. -/
def centralPeriodicSpectrum (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ) : Finset ℂ :=
  (finite_periodicSpectrum_inter_of_isBounded hp φ (isBounded_centralSpectralBox N)).toFinset

@[simp] theorem mem_centralPeriodicSpectrum (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ) (z : ℂ) :
    z ∈ centralPeriodicSpectrum hp φ N ↔ z ∈ periodicSpectrum hp φ ∧ z ∈ centralSpectralBox N :=
  Set.Finite.mem_toFinset _

/-- Resolvent boundary edges make the finite central spectrum independent of
whether the rectangle is taken open, closed, or with the dissertation's convention. -/
theorem mem_centralPeriodicSpectrum_iff_open (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ)
    (hc : centralRectangleBoundary N ⊆ resolventSet hp φ) (z : ℂ) :
    z ∈ centralPeriodicSpectrum hp φ N ↔ z ∈ periodicSpectrum hp φ ∧ z ∈ openCentralRectangle N := by
  rw [mem_centralPeriodicSpectrum]
  exact Set.ext_iff.mp (periodicSpectrum_inter_openCentralRectangle hp φ N hc).symm z

theorem mem_centralPeriodicSpectrum_iff_closed (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ)
    (hc : centralRectangleBoundary N ⊆ resolventSet hp φ) (z : ℂ) :
    z ∈ centralPeriodicSpectrum hp φ N ↔ z ∈ periodicSpectrum hp φ ∧ z ∈ closedCentralRectangle N := by
  rw [mem_centralPeriodicSpectrum]
  exact Set.ext_iff.mp (periodicSpectrum_inter_closedCentralRectangle hp φ N hc).symm z

/-- The free central spectrum is the image of the integer interval `[-N, N]`. -/
theorem centralPeriodicSpectrum_zero (hp : p ≠ ⊤) (N : ℕ) :
    centralPeriodicSpectrum (p := p) hp 0 N =
      (Finset.Icc (-(N : ℤ)) N).image (fun n : ℤ => (Real.pi : ℂ) * n) := by
  classical
  ext z
  rw [mem_centralPeriodicSpectrum, Finset.mem_image]
  constructor
  · rintro ⟨hz, hbox⟩
    have hlat : z ∈ freeLattice := by
      by_contra hoff
      exact hz (mem_resolventSet_zero_of_notMem hp z hoff)
    obtain ⟨n, rfl⟩ := hlat
    have hn := (free_mem_centralSpectralBox_iff N n).mp hbox
    refine ⟨n, ?_, rfl⟩
    rw [Finset.mem_Icc]
    omega
  · rintro ⟨n, hn, rfl⟩
    refine ⟨?_, (free_mem_centralSpectralBox_iff N n).mpr ?_⟩
    · exact (periodicAlgebraicMultiplicity_pos_iff hp 0 _).mp
        (by rw [periodicAlgebraicMultiplicity_zero]; norm_num)
    · rw [Finset.mem_Icc] at hn
      omega

/-- The free central algebraic multiplicity count in Proposition 1.1(ii). -/
theorem sum_central_multiplicity_zero (hp : p ≠ ⊤) (N : ℕ) :
    (∑ z ∈ centralPeriodicSpectrum (p := p) hp 0 N, periodicAlgebraicMultiplicity hp 0 z) =
      4 * N + 2 := by
  classical
  rw [centralPeriodicSpectrum_zero, Finset.sum_image]
  · simp only [periodicAlgebraicMultiplicity_zero, Finset.sum_const, smul_eq_mul, Int.card_Icc]
    have hcard : ((N : ℤ) + 1 - -(N : ℤ)).toNat = 2 * N + 1 := by omega
    rw [hcard]
    omega
  · intro a _ b _ h
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact_mod_cast mul_left_cancel₀ hπ h

/-- The algebraic projection onto all central full root spaces. Analytic dependence
and identification with the rectangular contour integral are separate results. -/
def centralSpectralProjection (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ) :
    PairSpace p →L[ℂ] PairSpace p :=
  periodicClusterProjection hp φ (centralPeriodicSpectrum hp φ N)

theorem centralSpectralProjection_idempotent (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ) :
    IsIdempotentElem (centralSpectralProjection hp φ N) :=
  periodicClusterProjection_idempotent hp φ _

theorem isCompactOperator_centralSpectralProjection (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ) :
    IsCompactOperator (centralSpectralProjection hp φ N) :=
  isCompactOperator_periodicClusterProjection hp φ _

/-- The central projector counts algebraic multiplicities. -/
theorem finrank_range_centralSpectralProjection (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ) :
    Module.finrank ℂ (centralSpectralProjection hp φ N).range =
      ∑ z ∈ centralPeriodicSpectrum hp φ N, periodicAlgebraicMultiplicity hp φ z :=
  finrank_range_periodicClusterProjection hp φ _

/-- The free central projector has the dimension used to start the deformation. -/
theorem finrank_range_centralSpectralProjection_zero (hp : p ≠ ⊤) (N : ℕ) :
    Module.finrank ℂ (centralSpectralProjection (p := p) hp 0 N).range = 4 * N + 2 := by
  rw [finrank_range_centralSpectralProjection, sum_central_multiplicity_zero]

end NLS.ZakharovShabat
