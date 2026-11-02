import NLS.ZakharovShabat.SourceAuxiliaryPrintedHeight
import NLS.ZakharovShabat.SourceBoundaryExplicitHeight

/-! # Corrected auxiliary spectral height for every finite exponent above one

The height `(1 + 8 * p * E_p * ‖φ‖)^p` uses the original source norm and
the proved interval-extension bound `E_p`. The auxiliary phase is an
isometry, so the ordinary boundary strip estimate transfers without
another norm factor. Both auxiliary spectra have the exact central count
`2 * N + 1`, simple high roots and exhaustive localization on one common
open convex connected neighborhood, for every larger cutoff.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
open BoundaryCondition
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Both actual auxiliary spectra lie strictly below the corrected norm-ball height. -/
theorem sourceAuxiliarySpectrum_abs_im_lt_explicit_height
    (hp1 : 1 < p) (hp : p ≠ ⊤) (b : BoundaryCondition) (φ : CoeffPair p)
    {M : ℝ} (hφ : ‖φ‖ ≤ M) {z : ℂ}
    (hz : z ∈ sourceAuxiliarySpectrum b hp (sourceAuxiliaryReflectedPotential hp1 hp φ)
      (sourceAuxiliaryReflectedPotential_mem hp1 hp φ)) :
    |z.im| < sourceBoundaryExplicitHeight hp hp1 M := by
  rw [sourceAuxiliarySpectrum_eq_sourcePhaseBoundary] at hz
  exact sourceBoundarySpectrum_abs_im_lt_explicit_height hp hp1 b
    (sourceAuxiliaryPotentialPhase hp φ) (by simpa only [LinearIsometryEquiv.norm_map] using hφ) hz

/-- The corrected Proposition 5.2 height, original Jordan multiplicities and
exhaustion hold for all finite `p > 1`. The neighborhood precedes both
boundary conditions and every larger cutoff. -/
theorem sourceProposition5_2_corrected_height (hp1 : 1 < p) (hp : p ≠ ⊤)
    (φ : CoeffPair p) :
    ∃ N₀ : ℕ, ∃ U : Set (CoeffPair p),
      0 < N₀ ∧ IsOpen U ∧ Convex ℝ U ∧ IsConnected U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ N : ℕ, N₀ ≤ N →
        SourceAuxiliaryCountingData hp (sourceAuxiliaryReflectedPotential hp1 hp ψ)
          (sourceAuxiliaryReflectedPotential_mem hp1 hp ψ) N ∧
        ∀ b : BoundaryCondition,
          sourceAuxiliaryHeightSpectrum b hp (sourceAuxiliaryReflectedPotential hp1 hp ψ)
            (sourceAuxiliaryReflectedPotential_mem hp1 hp ψ) N
            (sourceBoundaryExplicitHeight hp hp1 ‖ψ‖) =
            sourceAuxiliaryCentralSpectrum b hp (sourceAuxiliaryReflectedPotential hp1 hp ψ)
              (sourceAuxiliaryReflectedPotential_mem hp1 hp ψ) N ∧
          (∑ z ∈ sourceAuxiliaryHeightSpectrum b hp (sourceAuxiliaryReflectedPotential hp1 hp ψ)
            (sourceAuxiliaryReflectedPotential_mem hp1 hp ψ) N
            (sourceBoundaryExplicitHeight hp hp1 ‖ψ‖),
            sourceAuxiliaryAlgebraicMultiplicity b hp (sourceAuxiliaryReflectedPotential hp1 hp ψ)
              (sourceAuxiliaryReflectedPotential_mem hp1 hp ψ) z) = 2 * N + 1 ∧
          sourceAuxiliarySpectrum b hp (sourceAuxiliaryReflectedPotential hp1 hp ψ)
            (sourceAuxiliaryReflectedPotential_mem hp1 hp ψ) ⊆
            heightSpectralBox N (sourceBoundaryExplicitHeight hp hp1 ‖ψ‖) ∪
              highSpectralDisks N (Real.pi / 4) := by
  obtain ⟨K, V, hK, ho, hc, _, hφ, h0, hcount⟩ :=
    exists_uniform_sourceAuxiliaryCountingData hp1 hp φ
  obtain ⟨L, hL⟩ := exists_nat_gt (sourceBoundaryExplicitHeight hp hp1 (‖φ‖ + 1))
  let U := V ∩ Metric.ball (0 : CoeffPair p) (‖φ‖ + 1)
  have hUc : Convex ℝ U := hc.inter (convex_ball 0 _)
  have hU0 : (0 : CoeffPair p) ∈ U := ⟨h0, by simp [Metric.mem_ball]; positivity⟩
  refine ⟨max K L, U, hK.trans_le (le_max_left _ _), ho.inter Metric.isOpen_ball,
    hUc, ⟨⟨0, hU0⟩, hUc.isPreconnected⟩, ⟨hφ, by simp [Metric.mem_ball]⟩, hU0, ?_⟩
  intro ψ hψ N hN
  have hd := hcount ψ hψ.1 N ((le_max_left _ _).trans hN)
  have hnorm : ‖ψ‖ ≤ ‖φ‖ + 1 :=
    (show ‖ψ‖ < ‖φ‖ + 1 from by simpa [Metric.mem_ball] using hψ.2).le
  have hheight : sourceBoundaryExplicitHeight hp hp1 ‖ψ‖ ≤ (N : ℝ) := by
    calc
      _ ≤ sourceBoundaryExplicitHeight hp hp1 (‖φ‖ + 1) :=
        sourceBoundaryExplicitHeight_mono hp hp1 (norm_nonneg ψ) hnorm
      _ ≤ (L : ℝ) := hL.le
      _ ≤ (N : ℝ) := by exact_mod_cast ((le_max_right K L).trans hN)
  refine ⟨hd, ?_⟩
  intro b
  have hb (z : ℂ) (hz : z ∈ sourceAuxiliarySpectrum b hp
      (sourceAuxiliaryReflectedPotential hp1 hp ψ)
      (sourceAuxiliaryReflectedPotential_mem hp1 hp ψ)) :
      |z.im| ≤ sourceBoundaryExplicitHeight hp hp1 ‖ψ‖ :=
    (sourceAuxiliarySpectrum_abs_im_lt_explicit_height hp1 hp b ψ le_rfl hz).le
  have heq := sourceAuxiliaryHeightSpectrum_eq_central_of_bound b hp _ _ N hheight hb
  refine ⟨heq, ?_, ?_⟩
  · rw [heq]
    exact hd.central_multiplicity b
  · intro z hz
    rcases hd.spectrum_subset b hz with hcentral | hdisk
    · exact Or.inl ⟨hcentral.1, hb z hz⟩
    · exact Or.inr hdisk

end NLS.ZakharovShabat
