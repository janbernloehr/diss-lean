import NLS.ZakharovShabat.ExplicitHeight
import NLS.ZakharovShabat.CentralRectangleProjection

/-!
# Changing the height of the central spectral box

A global spectral strip bound identifies the central spectrum with the same
width box at any sufficient height. In the Hilbert case this transfers the
count `4N+2` to the printed height `(1 + 8 ‖φ‖)^2`, uniformly on a neighborhood.
The coefficient pair norm is used throughout.
-/

noncomputable section
open Complex Set Metric Classical
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The mixed-boundary central box with independently specified height. -/
def heightSpectralBox (N : ℕ) (H : ℝ) : Set ℂ :=
  {z | |z.re| < (N : ℝ) * Real.pi + Real.pi / 2 ∧ |z.im| ≤ H}

/-- A finite-height central box is bounded, even without a sign assumption on the height. -/
theorem isBounded_heightSpectralBox (N : ℕ) (H : ℝ) :
    Bornology.IsBounded (heightSpectralBox N H) := by
  apply (isCompact_closedBall (0 : ℂ)
    ((N : ℝ) * Real.pi + Real.pi / 2 + |H|)).isBounded.subset
  intro z hz
  rw [mem_closedBall, dist_zero_right]
  exact (norm_le_abs_re_add_abs_im z).trans
    (add_le_add hz.1.le (hz.2.trans (le_abs_self H)))

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The finite spectrum in a box of specified height. -/
def heightPeriodicSpectrum (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ) (H : ℝ) : Finset ℂ :=
  (finite_periodicSpectrum_inter_of_isBounded hp φ (isBounded_heightSpectralBox N H)).toFinset

@[simp] theorem mem_heightPeriodicSpectrum (hp : p ≠ ⊤) (φ : PairSpace p)
    (N : ℕ) (H : ℝ) (z : ℂ) :
    z ∈ heightPeriodicSpectrum hp φ N H ↔
      z ∈ periodicSpectrum hp φ ∧ z ∈ heightSpectralBox N H :=
  Set.Finite.mem_toFinset _

/-- A global strip bound makes the central spectral set independent of the larger height. -/
theorem heightPeriodicSpectrum_eq_central (hp : p ≠ ⊤) (φ : PairSpace p)
    (N : ℕ) {H : ℝ} (hHN : H ≤ (N : ℝ))
    (hH : ∀ z ∈ periodicSpectrum hp φ, |z.im| ≤ H) :
    heightPeriodicSpectrum hp φ N H = centralPeriodicSpectrum hp φ N := by
  ext z
  rw [mem_heightPeriodicSpectrum, mem_centralPeriodicSpectrum]
  constructor
  · rintro ⟨hz, hre, him⟩
    exact ⟨hz, hre, him.trans hHN⟩
  · rintro ⟨hz, hre, _⟩
    exact ⟨hz, hre, hH z hz⟩

/-- The explicit all-exponent height selects exactly the same central spectral cluster. -/
theorem explicit_heightPeriodicSpectrum_eq_central (hp : p ≠ ⊤) (φ : PairSpace p)
    (N : ℕ) (hN : (1 + 8 * p.toReal * ‖φ‖) ^ p.toReal ≤ (N : ℝ)) :
    heightPeriodicSpectrum hp φ N ((1 + 8 * p.toReal * ‖φ‖) ^ p.toReal) =
      centralPeriodicSpectrum hp φ N :=
  heightPeriodicSpectrum_eq_central hp φ N hN
    (fun _ hz => (abs_im_lt_explicit_height hp φ le_rfl hz).le)

/-- The printed Hilbert height selects exactly the central spectral cluster. -/
theorem hilbert_heightPeriodicSpectrum_eq_central (φ : PairSpace 2) (N : ℕ)
    (hN : (1 + 8 * ‖φ‖) ^ 2 ≤ (N : ℝ)) :
    heightPeriodicSpectrum (by norm_num) φ N ((1 + 8 * ‖φ‖) ^ 2) =
      centralPeriodicSpectrum (by norm_num) φ N :=
  heightPeriodicSpectrum_eq_central (by norm_num) φ N hN
    (fun _ hz => (abs_im_lt_hilbert_height φ le_rfl hz).le)

/-- On one open convex neighborhood, the printed Hilbert box has count `4N+2`
and its full spectral projection equals the already constructed rectangular integral. -/
theorem exists_uniform_hilbert_height_count (φ : PairSpace 2) :
    ∃ N₀ : ℕ, ∃ U : Set (PairSpace 2), 0 < N₀ ∧ IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ N : ℕ, N₀ ≤ N →
        heightPeriodicSpectrum (by norm_num) ψ N ((1 + 8 * ‖ψ‖) ^ 2) =
          centralPeriodicSpectrum (by norm_num) ψ N ∧
        centralRectangleIntegral (by norm_num) ψ N = periodicClusterProjection (by norm_num) ψ
          (heightPeriodicSpectrum (by norm_num) ψ N ((1 + 8 * ‖ψ‖) ^ 2)) ∧
        (∑ a ∈ heightPeriodicSpectrum (by norm_num) ψ N ((1 + 8 * ‖ψ‖) ^ 2),
          periodicAlgebraicMultiplicity (by norm_num) ψ a) = 4 * N + 2 := by
  obtain ⟨K, U, hK, ho, hc, hφ, h0, _, h⟩ :=
    exists_uniform_central_multiplicity (by norm_num) φ
  obtain ⟨L, hL⟩ := exists_nat_ge ((1 + 8 * (‖φ‖ + 1)) ^ 2)
  refine ⟨max K L, U ∩ ball 0 (‖φ‖ + 1), lt_of_lt_of_le hK (le_max_left _ _),
    ho.inter isOpen_ball, hc.inter (convex_ball _ _), ⟨hφ, ?_⟩, ⟨h0, ?_⟩, ?_⟩
  · simpa only [mem_ball, dist_zero_right] using (lt_add_one ‖φ‖)
  · simp only [mem_ball, dist_self]
    positivity
  · intro ψ hψ N hN
    have hNK : K ≤ N := (le_max_left _ _).trans hN
    have hNL : (L : ℝ) ≤ (N : ℝ) := by exact_mod_cast (le_max_right K L).trans hN
    have hnorm : ‖ψ‖ ≤ ‖φ‖ + 1 := (mem_ball_zero_iff.mp hψ.2).le
    have hheight : (1 + 8 * ‖ψ‖) ^ 2 ≤ (N : ℝ) := by
      apply le_trans _ (hL.trans hNL)
      gcongr
    have he := hilbert_heightPeriodicSpectrum_eq_central ψ N hheight
    refine ⟨he, ?_, ?_⟩
    · rw [he, centralRectangleIntegral_eq_centralSpectralProjection
        (by norm_num) ψ N (h ψ hψ.1 N hNK).1]
      rfl
    · rw [he]
      exact (h ψ hψ.1 N hNK).2.2

end NLS.ZakharovShabat
