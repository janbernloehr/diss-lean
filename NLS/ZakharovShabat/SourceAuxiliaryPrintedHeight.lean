import NLS.ZakharovShabat.SourceAuxiliaryPotentialPhase
import NLS.ZakharovShabat.SourceAuxiliaryHeightClusters
import NLS.ZakharovShabat.SourceBoundaryPrintedHeight

/-!
# The printed auxiliary height and counts at p=2

Both actual original auxiliary spectra satisfy the unchanged printed Hilbert
height. One original-input open convex connected neighborhood supports that
height, full algebraic counts, high-disk simplicity, and exhaustive localization
for every larger cutoff. This is a p=2 result, not an all-exponent assertion.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
open BoundaryCondition NLS.Fourier
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The printed Hilbert height remains valid in the actual original auxiliary spectrum. -/
theorem sourceAuxiliarySpectrum_abs_im_lt_printed_height_two (b : BoundaryCondition)
    (φ : CoeffPair 2) {z : ℂ}
    (hz : z ∈ sourceAuxiliarySpectrum b (by simp)
      (sourceAuxiliaryReflectedPotential (by norm_num) (by simp) φ)
      (sourceAuxiliaryReflectedPotential_mem (by norm_num) (by simp) φ)) :
    |z.im| < (1+8*‖φ‖)^2 := by
  rw [sourceAuxiliarySpectrum_eq_sourcePhaseBoundary] at hz
  simpa only [LinearIsometryEquiv.norm_map] using
    sourceBoundarySpectrum_abs_im_lt_printed_height_two b (sourceAuxiliaryPotentialPhase (by simp) φ) hz

/-- A spectral height bound identifies the actual prescribed-height and central clusters. -/
theorem sourceAuxiliaryHeightSpectrum_eq_central_of_bound (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .neumann) (N : ℕ) {H : ℝ}
    (hHN : H ≤ (N : ℝ)) (hH : ∀ z ∈ sourceAuxiliarySpectrum b hp φ hφ, |z.im| ≤ H) :
    sourceAuxiliaryHeightSpectrum b hp φ hφ N H = sourceAuxiliaryCentralSpectrum b hp φ hφ N := by
  ext z
  rw [mem_sourceAuxiliaryHeightSpectrum, mem_sourceAuxiliaryCentralSpectrum]
  constructor
  · rintro ⟨hz,hre,him⟩
    exact ⟨hz,hre,him.trans hHN⟩
  · rintro ⟨hz,hre,_⟩
    exact ⟨hz,hre,hH z hz⟩

/-- The printed height, full algebraic counts, and exhaustive localization at p=2. -/
theorem sourceProposition5_2_two (φ : CoeffPair 2) :
    ∃ N₀ : ℕ, ∃ U : Set (CoeffPair 2), 0 < N₀ ∧ IsOpen U ∧ Convex ℝ U ∧ IsConnected U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ N : ℕ, N₀ ≤ N →
        SourceAuxiliaryCountingData (by simp) (sourceAuxiliaryReflectedPotential (by norm_num) (by simp) ψ)
          (sourceAuxiliaryReflectedPotential_mem (by norm_num) (by simp) ψ) N ∧
        ∀ b : BoundaryCondition,
          (∑ z ∈ sourceAuxiliaryHeightSpectrum b (by simp)
            (sourceAuxiliaryReflectedPotential (by norm_num) (by simp) ψ)
            (sourceAuxiliaryReflectedPotential_mem (by norm_num) (by simp) ψ) N ((1+8*‖ψ‖)^2),
            sourceAuxiliaryAlgebraicMultiplicity b (by simp)
              (sourceAuxiliaryReflectedPotential (by norm_num) (by simp) ψ)
              (sourceAuxiliaryReflectedPotential_mem (by norm_num) (by simp) ψ) z) = 2*N+1 ∧
          sourceAuxiliarySpectrum b (by simp)
            (sourceAuxiliaryReflectedPotential (by norm_num) (by simp) ψ)
            (sourceAuxiliaryReflectedPotential_mem (by norm_num) (by simp) ψ) ⊆
              heightSpectralBox N ((1+8*‖ψ‖)^2) ∪ highSpectralDisks N (Real.pi/4) := by
  obtain ⟨K,V,hK,ho,hc,_,hφ,h0,hcount⟩ := exists_uniform_sourceAuxiliaryCountingData (by norm_num) (by simp) φ
  obtain ⟨L,hL⟩ := exists_nat_gt ((1+8*(‖φ‖+1))^2)
  let U := V ∩ Metric.ball (0 : CoeffPair 2) (‖φ‖+1)
  have hUc : Convex ℝ U := hc.inter (convex_ball 0 _)
  have hU0 : (0 : CoeffPair 2) ∈ U := ⟨h0, by simp [Metric.mem_ball]; positivity⟩
  refine ⟨max K L,U,hK.trans_le (le_max_left _ _),ho.inter Metric.isOpen_ball,hUc,
    ⟨⟨0,hU0⟩,hUc.isPreconnected⟩,⟨hφ,by simp [Metric.mem_ball]⟩,hU0,?_⟩
  intro ψ hψ N hN
  have hd := hcount ψ hψ.1 N ((le_max_left _ _).trans hN)
  have hnorm : ‖ψ‖ ≤ ‖φ‖+1 := (show ‖ψ‖ < ‖φ‖+1 from by simpa [Metric.mem_ball] using hψ.2).le
  have hheight : (1+8*‖ψ‖)^2 ≤ (N : ℝ) := by
    calc
      _ ≤ (1+8*(‖φ‖+1))^2 := by gcongr
      _ ≤ (L : ℝ) := hL.le
      _ ≤ (N : ℝ) := by exact_mod_cast ((le_max_right K L).trans hN)
  refine ⟨hd,?_⟩
  intro b
  have hb (z : ℂ) (hz : z ∈ sourceAuxiliarySpectrum b (by simp)
      (sourceAuxiliaryReflectedPotential (by norm_num) (by simp) ψ)
      (sourceAuxiliaryReflectedPotential_mem (by norm_num) (by simp) ψ)) : |z.im| ≤ (1+8*‖ψ‖)^2 :=
    (sourceAuxiliarySpectrum_abs_im_lt_printed_height_two b ψ hz).le
  constructor
  · rw [sourceAuxiliaryHeightSpectrum_eq_central_of_bound b (by simp) _ _ N hheight hb]
    exact hd.central_multiplicity b
  · intro z hz
    rcases hd.spectrum_subset b hz with hc | hdisk
    · exact Or.inl ⟨hc.1,hb z hz⟩
    · exact Or.inr hdisk

end NLS.ZakharovShabat
