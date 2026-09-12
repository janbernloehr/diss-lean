import NLS.ZakharovShabat.CentralParity

/-!
# Uniform periodic localization and counting

This assembles the coefficient-space conclusions of Proposition 1.1(i–iii),
using the height-`N` central box of Corollary 3.5. One cutoff and one open convex
neighborhood simultaneously support the exterior resolvent, the central and
high-frequency counts, the parity assertions, and the analytic projections.
The real-type assertion is proved in `RealType`; physical Fourier realization
remains separate.
-/

noncomputable section
open Complex Metric Topology
open scoped ENNReal

namespace NLS.ZakharovShabat

/-- Distinct quarter-pi spectral disks are disjoint. -/
theorem periodicDisks_disjoint (n m : ℤ) (hnm : n ≠ m) :
    Disjoint (ball ((Real.pi : ℂ) * n) (Real.pi / 4))
      (ball ((Real.pi : ℂ) * m) (Real.pi / 4)) := by
  apply Metric.ball_disjoint_ball
  have habs : 1 ≤ |((n - m : ℤ) : ℝ)| := by exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hnm)
  have hd : dist ((Real.pi : ℂ) * n) ((Real.pi : ℂ) * m) =
      Real.pi * |((n - m : ℤ) : ℝ)| := by
    rw [dist_eq_norm, ← mul_sub, ← Int.cast_sub]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
      Complex.norm_intCast]
  rw [hd]
  nlinarith [Real.pi_pos]

/-- None of the high-frequency disks overlaps the central box with the same cutoff. -/
theorem centralBox_disjoint_periodicDisk (N : ℕ) (hN : 0 < N) (n : ℤ) (hn : N < n.natAbs) :
    Disjoint (centralSpectralBox N) (ball ((Real.pi : ℂ) * n) (Real.pi / 4)) := by
  apply Set.disjoint_left.mpr
  intro z hbox hdisk
  have hrN : Real.pi / 4 ≤ (N : ℝ) := by
    have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith [Real.pi_le_four]
  have hindex := (smallDisk_central_selection N n le_rfl hrN hdisk).2.mp hbox
  omega

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The local counting and localization data, with one common positive cutoff.
Parity clauses apply to potentials supported on even raw Fourier frequencies. -/
structure PeriodicCountingData (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ) : Prop where
  cutoff_pos : 0 < N
  central_boundary : centralRectangleBoundary N ⊆ resolventSet hp φ
  exterior_resolvent : spectralExterior N (Real.pi / 4) ⊆ resolventSet hp φ
  central_rank : Module.finrank ℂ (centralSpectralProjection hp φ N).range = 4 * N + 2
  central_multiplicity :
    (∑ z ∈ centralPeriodicSpectrum hp φ N, periodicAlgebraicMultiplicity hp φ z) = 4 * N + 2
  central_parity : φ ∈ pairParitySubspace 0 → ∀ r : ℤ,
    Module.finrank ℂ ↥((centralSpectralProjection hp φ N).range ⊓ pairParitySubspace r) =
      if (N : ℤ) % 2 = r % 2 then 2 * N + 2 else 2 * N
  disk_resolvent : ∀ n : ℤ, N < n.natAbs →
    sphere ((Real.pi : ℂ) * n) (Real.pi / 4) ⊆ resolventSet hp φ
  disk_rank : ∀ n : ℤ, N < n.natAbs →
    Module.finrank ℂ (resolventCircleIntegral hp φ ((Real.pi : ℂ) * n) (Real.pi / 4)).range = 2
  disk_multiplicity : ∀ n : ℤ, N < n.natAbs →
    (∑ z ∈ enclosedPeriodicSpectrum hp φ ((Real.pi : ℂ) * n) (Real.pi / 4),
      periodicAlgebraicMultiplicity hp φ z) = 2
  disk_parity : φ ∈ pairParitySubspace 0 → ∀ n : ℤ, N < n.natAbs →
    (resolventCircleIntegral hp φ ((Real.pi : ℂ) * n) (Real.pi / 4)).range ≤ pairParitySubspace n

namespace PeriodicCountingData

variable {hp : p ≠ ⊤} {φ : PairSpace p} {N : ℕ}

/-- There are no other periodic spectral values. -/
theorem spectrum_subset (h : PeriodicCountingData hp φ N) :
    periodicSpectrum hp φ ⊆ centralSpectralBox N ∪ highSpectralDisks N (Real.pi / 4) :=
  periodicSpectrum_subset_box_union_disks hp φ N (Real.pi / 4) h.exterior_resolvent

/-- The exterior resolvent is analytic on the same region as the counting data. -/
theorem analyticOnNhd_exterior (h : PeriodicCountingData hp φ N) :
    AnalyticOnNhd ℂ (resolvent hp φ) (spectralExterior N (Real.pi / 4)) :=
  (analyticOnNhd_resolvent hp φ).mono h.exterior_resolvent

/-- Every spectral value belongs to the central cluster or to exactly one high disk. -/
theorem mem_spectrum_iff_central_or_disk (h : PeriodicCountingData hp φ N) (z : ℂ) :
    z ∈ periodicSpectrum hp φ ↔ z ∈ centralPeriodicSpectrum hp φ N ∨
      ∃! n : ℤ, N < n.natAbs ∧
        z ∈ enclosedPeriodicSpectrum hp φ ((Real.pi : ℂ) * n) (Real.pi / 4) := by
  constructor
  · intro hz
    rcases h.spectrum_subset hz with hbox | hdisks
    · exact Or.inl ((mem_centralPeriodicSpectrum hp φ N z).mpr ⟨hz, hbox⟩)
    · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hdisks
      obtain ⟨hn, hdisk⟩ := Set.mem_iUnion.mp hn
      refine Or.inr ⟨n, ⟨hn, (mem_enclosedPeriodicSpectrum hp φ _ z _).mpr ⟨hz, hdisk⟩⟩, ?_⟩
      intro m hm
      by_contra hmn
      exact (periodicDisks_disjoint m n hmn).le_bot
        ⟨((mem_enclosedPeriodicSpectrum hp φ _ z _).mp hm.2).2, hdisk⟩
  · rintro (hz | ⟨n, hn, _⟩)
    · exact ((mem_centralPeriodicSpectrum hp φ N z).mp hz).1
    · exact ((mem_enclosedPeriodicSpectrum hp φ _ z _).mp hn.2).1

/-- The central and high-disk alternatives in the classification are exclusive. -/
theorem central_disjoint_disk (h : PeriodicCountingData hp φ N) (n : ℤ) (hn : N < n.natAbs) :
    Disjoint (centralPeriodicSpectrum hp φ N)
      (enclosedPeriodicSpectrum hp φ ((Real.pi : ℂ) * n) (Real.pi / 4)) := by
  apply Finset.disjoint_left.mpr
  intro z hcentral hdisk
  exact (centralBox_disjoint_periodicDisk N h.cutoff_pos n hn).le_bot
    ⟨((mem_centralPeriodicSpectrum hp φ N z).mp hcentral).2,
      ((mem_enclosedPeriodicSpectrum hp φ _ z _).mp hdisk).2⟩

/-- Two counted eigenvalues can be one double value or two distinct values. -/
theorem disk_card_eq_one_or_two (h : PeriodicCountingData hp φ N) (n : ℤ) (hn : N < n.natAbs) :
    (enclosedPeriodicSpectrum hp φ ((Real.pi : ℂ) * n) (Real.pi / 4)).card = 1 ∨
      (enclosedPeriodicSpectrum hp φ ((Real.pi : ℂ) * n) (Real.pi / 4)).card = 2 := by
  let s := enclosedPeriodicSpectrum hp φ ((Real.pi : ℂ) * n) (Real.pi / 4)
  have hsum : (∑ z ∈ s, periodicAlgebraicMultiplicity hp φ z) = 2 := h.disk_multiplicity n hn
  have hpos : 0 < s.card := by
    by_contra hc
    have he : s = ∅ := Finset.card_eq_zero.mp (by omega)
    rw [he, Finset.sum_empty] at hsum
    omega
  have hcard : s.card ≤ 2 := by
    calc
      s.card = ∑ _z ∈ s, (1 : ℕ) := Finset.card_eq_sum_ones s
      _ ≤ ∑ z ∈ s, periodicAlgebraicMultiplicity hp φ z := by
        apply Finset.sum_le_sum
        intro z hz
        exact (periodicAlgebraicMultiplicity_pos_iff hp φ z).mpr
          ((mem_enclosedPeriodicSpectrum hp φ _ z _).mp hz).1
      _ = 2 := hsum
  change s.card = 1 ∨ s.card = 2
  omega

/-- Each high disk has an unordered eigenvalue pair, allowing repetition for a
double value. If the values differ, each has algebraic multiplicity one. -/
theorem disk_eigenvalue_pair (h : PeriodicCountingData hp φ N) (n : ℤ) (hn : N < n.natAbs) :
    ∃ a b : ℂ,
      enclosedPeriodicSpectrum hp φ ((Real.pi : ℂ) * n) (Real.pi / 4) = {a, b} ∧
      (if a = b then periodicAlgebraicMultiplicity hp φ a = 2 else
        periodicAlgebraicMultiplicity hp φ a = 1 ∧ periodicAlgebraicMultiplicity hp φ b = 1) := by
  classical
  rcases h.disk_card_eq_one_or_two n hn with hs | hs
  · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hs
    refine ⟨a, a, by simpa using ha, ?_⟩
    simpa only [ha, Finset.sum_singleton, ite_true] using h.disk_multiplicity n hn
  · obtain ⟨a, b, hab, hs⟩ := Finset.card_eq_two.mp hs
    refine ⟨a, b, hs, ?_⟩
    rw [if_neg hab]
    have ha : a ∈ enclosedPeriodicSpectrum hp φ ((Real.pi : ℂ) * n) (Real.pi / 4) := by rw [hs]; simp
    have hb : b ∈ enclosedPeriodicSpectrum hp φ ((Real.pi : ℂ) * n) (Real.pi / 4) := by rw [hs]; simp
    have hma := (periodicAlgebraicMultiplicity_pos_iff hp φ a).mpr
      ((mem_enclosedPeriodicSpectrum hp φ _ a _).mp ha).1
    have hmb := (periodicAlgebraicMultiplicity_pos_iff hp φ b).mpr
      ((mem_enclosedPeriodicSpectrum hp φ _ b _).mp hb).1
    have hsum := h.disk_multiplicity n hn
    rw [hs, Finset.sum_pair hab] at hsum
    omega

/-- All full root spaces in a high disk have the index's parity for even potentials. -/
theorem disk_rootSpace_parity (h : PeriodicCountingData hp φ N)
    (hφ : φ ∈ pairParitySubspace 0) (n : ℤ) (hn : N < n.natAbs) (z : ℂ)
    (hz : z ∈ ball ((Real.pi : ℂ) * n) (Real.pi / 4)) :
    periodicRootSpaceTop hp φ z ≤ pairParitySubspace n :=
  periodicRootSpaceTop_le_parity_of_contour hp φ _ z _ n (h.disk_resolvent n hn) hz
    (h.disk_parity hφ n hn)

/-- The same statement for eigenfunctions in the weighted operator domain. -/
theorem disk_eigenvector_parity (h : PeriodicCountingData hp φ N)
    (hφ : φ ∈ pairParitySubspace 0) (n : ℤ) (hn : N < n.natAbs) (z : ℂ)
    (hz : z ∈ ball ((Real.pi : ℂ) * n) (Real.pi / 4)) (f : Domain p)
    (hf : operator hp φ f = z • domainInclusion f) : f ∈ domainParitySubspace n :=
  eigenvector_mem_domainParitySubspace_of_root_le hp φ z n (h.disk_rootSpace_parity hφ n hn z hz) f hf

end PeriodicCountingData

/-- One threshold and one open convex neighborhood support all localization,
central and disk counts, parity conclusions, and analytic projections. The
counting data are valid for every larger cutoff on this same neighborhood. -/
theorem exists_uniform_periodicCountingData (hp : p ≠ ⊤) (φ : PairSpace p) :
    ∃ N₀ : ℕ, ∃ U : Set (PairSpace p), 0 < N₀ ∧ IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      (∀ N : ℕ, N₀ ≤ N → AnalyticOnNhd ℂ (fun ψ => centralSpectralProjection hp ψ N) U ∧
        ∀ r : ℤ, AnalyticOnNhd ℂ (fun ψ => centralParityProjection hp ψ N r) U) ∧
      (∀ n : ℤ, N₀ < n.natAbs → AnalyticOnNhd ℂ
        (fun ψ => resolventCircleIntegral hp ψ ((Real.pi : ℂ) * n) (Real.pi / 4)) U) ∧
      ∀ ψ ∈ U, ∀ N : ℕ, N₀ ≤ N → PeriodicCountingData hp ψ N := by
  obtain ⟨Nc, Uc, hNc, hoc, hcc, hφc, h0c, han, hc⟩ := exists_uniform_central_counts hp φ
  obtain ⟨Nd, Ud, hod, hcd, hφd, h0d, hd⟩ :=
    exists_uniform_disk_multiplicity_and_parity hp φ (by positivity) le_rfl
  obtain ⟨Ne, Ue, _, hoe, hce, hφe, h0e, he⟩ :=
    exists_uniform_centralRectangle_resolvent hp φ (r := Real.pi / 4) (by positivity) le_rfl
  let N₀ := max Nc (max Nd Ne)
  let U := Uc ∩ Ud ∩ Ue
  have hNc₀ : Nc ≤ N₀ := le_max_left _ _
  have hNd₀ : Nd ≤ N₀ := (le_max_left Nd Ne).trans (le_max_right Nc _)
  have hNe₀ : Ne ≤ N₀ := (le_max_right Nd Ne).trans (le_max_right Nc _)
  refine ⟨N₀, U, hNc.trans_le hNc₀, (hoc.inter hod).inter hoe, (hcc.inter hcd).inter hce,
    ⟨⟨hφc, hφd⟩, hφe⟩, ⟨⟨h0c, h0d⟩, h0e⟩, ?_, ?_, ?_⟩
  · intro N hN
    exact ⟨(han N (hNc₀.trans hN)).1.mono (fun _ h => h.1.1),
      fun r => ((han N (hNc₀.trans hN)).2 r).mono (fun _ h => h.1.1)⟩
  · intro n hn ψ hψ
    exact analyticAt_resolventCircleIntegral hp ψ _ _ (by positivity)
      (hd ψ hψ.1.2 n (hNd₀.trans hn.le)).1
  · intro ψ hψ N hN
    obtain ⟨hb, hrank, hsum, hpar⟩ := hc ψ hψ.1.1 N (hNc₀.trans hN)
    refine ⟨(hNc.trans_le hNc₀).trans_le hN, hb, (he ψ hψ.2 N (hNe₀.trans hN)).2.1,
      hrank, hsum, hpar, ?_, ?_, ?_, ?_⟩
    · intro n hn
      exact (hd ψ hψ.1.2 n (hNd₀.trans (hN.trans hn.le))).1
    · intro n hn
      exact (hd ψ hψ.1.2 n (hNd₀.trans (hN.trans hn.le))).2.1
    · intro n hn
      exact (hd ψ hψ.1.2 n (hNd₀.trans (hN.trans hn.le))).2.2.1
    · intro hφ n hn
      exact ((hd ψ hψ.1.2 n (hNd₀.trans (hN.trans hn.le))).2.2.2 hφ).1

end NLS.ZakharovShabat
