import NLS.ZakharovShabat.FrequencyLocalization
import NLS.ZakharovShabat.HeightResolvent

/-!
# Localization for arbitrary potentials

Corollary 3.5: outside a central rectangle and the quarter-pi disks about the
remaining free eigenvalues, the resolvent is compact and analytic, uniformly
on a potential neighborhood. The neighborhood can be chosen open and convex
and to contain zero. The central rectangle has exactly the dissertation's
strict real-part boundary and non-strict imaginary-part boundary.
-/

open scoped ENNReal Topology
noncomputable section

namespace NLS.ZakharovShabat

/-- The central region `B_N` of Corollary 3.5. -/
def centralSpectralBox (N : ℕ) : Set ℂ :=
  {z | |z.re| < (N : ℝ) * Real.pi + Real.pi / 2 ∧ |z.im| ≤ (N : ℝ)}

/-- The disks `D_n` with `|n| > N`, with a variable radius for later contour use. -/
def highSpectralDisks (N : ℕ) (r : ℝ) : Set ℂ :=
  ⋃ n : ℤ, ⋃ (_ : N < n.natAbs), Metric.ball ((Real.pi : ℂ) * n) r

/-- The common exterior region on which Corollary 3.5 constructs the resolvent. -/
def spectralExterior (N : ℕ) (r : ℝ) : Set ℂ :=
  (centralSpectralBox N ∪ highSpectralDisks N r)ᶜ

@[simp] theorem mem_spectralExterior (N : ℕ) (r : ℝ) (z : ℂ) :
    z ∈ spectralExterior N r ↔ z ∉ centralSpectralBox N ∧
      ∀ n : ℤ, N < n.natAbs → r ≤ ‖z - (Real.pi : ℂ) * n‖ := by
  simp [spectralExterior, highSpectralDisks, Metric.mem_ball, dist_eq_norm]

/-- Every exterior point is either above the central height or in a sufficiently
far punctured strip. Equality on the vertical edges of `B_N` is included. -/
theorem spectralExterior_height_or_strip (N : ℕ) {r : ℝ} (hrπ : r ≤ Real.pi / 4)
    {z : ℂ} (hz : z ∈ spectralExterior N r) :
    (N : ℝ) < |z.im| ∨ ∃ n : ℤ, N ≤ n.natAbs ∧ z ∈ verticalStrip n r := by
  obtain ⟨hbox, hdisks⟩ := (mem_spectralExterior N r z).mp hz
  by_cases him : (N : ℝ) < |z.im|
  · exact Or.inl him
  · have him' : |z.im| ≤ (N : ℝ) := le_of_not_gt him
    have hre : (N : ℝ) * Real.pi + Real.pi / 2 ≤ |z.re| :=
      le_of_not_gt (fun h => hbox ⟨h, him'⟩)
    obtain ⟨n, hn⟩ := exists_centered_real_part z
    have htri : |z.re| ≤ |z.re - Real.pi * n| + Real.pi * |(n : ℝ)| := by
      calc
        |z.re| = |(z.re - Real.pi * n) + Real.pi * n| := by congr 1; ring
        _ ≤ |z.re - Real.pi * n| + |Real.pi * n| := abs_add_le _ _
        _ = _ := by rw [abs_mul, abs_of_pos Real.pi_pos]
    have he : |(n : ℝ)| = (n.natAbs : ℝ) := by simp only [Nat.cast_natAbs, Int.cast_abs]
    have hNreal : (N : ℝ) ≤ (n.natAbs : ℝ) := by
      rw [← he]
      nlinarith [Real.pi_pos]
    have hN : N ≤ n.natAbs := by exact_mod_cast hNreal
    refine Or.inr ⟨n, hN, hn, ?_⟩
    by_cases hstrict : N < n.natAbs
    · exact hdisks n hstrict
    · have heq : n.natAbs = N := by omega
      have hboundary : Real.pi / 2 ≤ |z.re - Real.pi * n| := by
        rw [he, heq] at htri
        linarith
      have hnorm : |z.re - Real.pi * n| ≤ ‖z - (Real.pi : ℂ) * n‖ := by
        simpa using Complex.abs_re_le_norm (z - (Real.pi : ℂ) * n)
      exact (show r ≤ Real.pi / 2 by linarith [Real.pi_pos]).trans (hboundary.trans hnorm)

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A common positive integer height and frequency cutoff, retaining the bounds
on the horizontal boundary as well as all sufficiently far punctured strips. -/
theorem exists_uniform_height_and_strips (hp : p ≠ ⊤) (φ : PairSpace p)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi / 4) :
    ∃ N : ℕ, ∃ U : Set (PairSpace p), 0 < N ∧ IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U,
        (∀ z : ℂ, (N : ℝ) ≤ |z.im| → z ∈ resolventSet hp ψ) ∧
        (∀ n : ℤ, N ≤ n.natAbs → verticalStrip n r ⊆ resolventSet hp ψ) := by
  obtain ⟨N₀, U, ho, hc, hφ, h0, hnorm, hstrips⟩ :=
    exists_uniform_highFrequency_resolvent hp φ hr hrπ
  obtain ⟨H, hH, hheight⟩ := exists_uniform_heightNeumannRegion hp (‖φ‖ + 1)
  obtain ⟨K, hK⟩ := exists_nat_gt H
  let N := max N₀ K
  have hN₀ : N₀ ≤ N := le_max_left _ _
  have hHN : H ≤ (N : ℝ) := hK.le.trans (by exact_mod_cast (le_max_right N₀ K))
  have hN : 0 < N := by exact_mod_cast (hH.trans_le hHN)
  refine ⟨N, U, hN, ho, hc, hφ, h0, ?_⟩
  intro ψ hψ
  exact ⟨fun z hz => heightNeumannRegion_subset_resolventSet hp ψ
      (hheight ψ (hnorm ψ hψ).le z (hHN.trans hz)),
    fun n hn => hstrips ψ hψ n (hN₀.trans hn)⟩

/-- One central rectangle and one open convex potential neighborhood work
simultaneously for all exterior spectral parameters. -/
theorem exists_uniform_spectralExterior (hp : p ≠ ⊤) (φ : PairSpace p)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi / 4) :
    ∃ N : ℕ, ∃ U : Set (PairSpace p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, spectralExterior N r ⊆ resolventSet hp ψ := by
  obtain ⟨N, U, _, ho, hc, hφ, h0, hbounds⟩ :=
    exists_uniform_height_and_strips hp φ hr hrπ
  refine ⟨N, U, ho, hc, hφ, h0, ?_⟩
  intro ψ hψ z hz
  rcases spectralExterior_height_or_strip N hrπ hz with him | ⟨n, hn, hzstrip⟩
  · exact (hbounds ψ hψ).1 z him.le
  · exact (hbounds ψ hψ).2 n hn hzstrip

/-- Resolvent inclusion gives the precise central-box and disk enclosure of the spectrum. -/
theorem periodicSpectrum_subset_box_union_disks (hp : p ≠ ⊤) (φ : PairSpace p)
    (N : ℕ) (r : ℝ) (h : spectralExterior N r ⊆ resolventSet hp φ) :
    periodicSpectrum hp φ ⊆ centralSpectralBox N ∪ highSpectralDisks N r := by
  intro z hz
  by_contra hout
  exact hz (h hout)

/-- Corollary 3.5, including a connected neighborhood containing the zero potential. -/
theorem exists_spectralLocalization (hp : p ≠ ⊤) (φ : PairSpace p) :
    ∃ N : ℕ, ∃ U : Set (PairSpace p), IsOpen U ∧ IsConnected U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U,
        AnalyticOnNhd ℂ (resolvent hp ψ) (spectralExterior N (Real.pi / 4)) ∧
        (∀ z ∈ spectralExterior N (Real.pi / 4), IsCompactOperator (resolvent hp ψ z)) ∧
        periodicSpectrum hp ψ ⊆ centralSpectralBox N ∪ highSpectralDisks N (Real.pi / 4) := by
  obtain ⟨N, U, ho, hc, hφ, h0, hregion⟩ :=
    exists_uniform_spectralExterior hp φ (r := Real.pi / 4) (by positivity) le_rfl
  refine ⟨N, U, ho, ⟨⟨0, h0⟩, hc.isPreconnected⟩, hφ, h0, ?_⟩
  intro ψ hψ
  exact ⟨(analyticOnNhd_resolvent hp ψ).mono (hregion ψ hψ),
    fun z _ => isCompactOperator_resolvent hp ψ z,
    periodicSpectrum_subset_box_union_disks hp ψ N (Real.pi / 4) (hregion ψ hψ)⟩

end NLS.ZakharovShabat
