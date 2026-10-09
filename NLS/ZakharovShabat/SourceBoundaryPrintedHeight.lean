import NLS.ZakharovShabat.SourceBoundaryOverview
import NLS.ZakharovShabat.HeightSpectralBox

/-! # Boundary counts in the printed source-height box

A source spectral-height estimate transfers the common boundary counting
neighborhood to the literal box of Theorem 1.4. At p=2 the completed
interval extension is contractive, so the existing Hilbert height estimate
proves the required input in the original source norm. Other exponents
remain a separate obligation; height-N boxes do not discharge it.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace BoundaryCondition
variable (b : BoundaryCondition)

/-- The actual boundary spectrum in a box of prescribed height. -/
def heightSpectrum (hp : p ≠ ⊤) (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace)
    (N : ℕ) (H : ℝ) : Finset ℂ :=
  (finite_spectrum_inter_of_isBounded b hp φ hφ (isBounded_heightSpectralBox N H)).toFinset

@[simp] theorem mem_heightSpectrum (hp : p ≠ ⊤) (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace)
    (N : ℕ) (H : ℝ) (z : ℂ) :
    z ∈ heightSpectrum b hp φ hφ N H ↔ z ∈ spectrum b hp φ hφ ∧ z ∈ heightSpectralBox N H :=
  Set.Finite.mem_toFinset _

/-- A height bound on this boundary spectrum identifies its central cluster. -/
theorem heightSpectrum_eq_central (hp : p ≠ ⊤) (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace)
    (N : ℕ) {H : ℝ} (hHN : H ≤ (N : ℝ))
    (hH : ∀ z ∈ spectrum b hp φ hφ, |z.im| ≤ H) :
    heightSpectrum b hp φ hφ N H = centralSpectrum b hp φ hφ N := by
  ext z
  rw [mem_heightSpectrum,mem_centralSpectrum]
  constructor
  · rintro ⟨hz,hre,him⟩
    exact ⟨hz,hre,him.trans hHN⟩
  · rintro ⟨hz,hre,_⟩
    exact ⟨hz,hre,hH z hz⟩

end BoundaryCondition

/-- Transfer both boundary counts to the exact printed box whenever the
original source-height estimate is available. Every larger cutoff works
on one open convex source neighborhood. -/
theorem exists_source_boundaryCounting_printed_height_of_bound (hp : p ≠ ⊤) (hp1 : 1 < p)
    (hheight : ∀ ψ : CoeffPair p, ∀ b : BoundaryCondition, ∀ z ∈ b.spectrum hp
      (periodOneBoundaryPotential hp hp1 ψ).val (periodOneBoundaryPotential hp hp1 ψ).property,
      |z.im| ≤ (1+8*‖ψ‖)^p.toReal) (φ : CoeffPair p) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∃ U : Set (CoeffPair p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ N : ℕ, N₀ ≤ N →
        BoundaryCountingData hp (periodOneBoundaryPotential hp hp1 ψ).val
          (periodOneBoundaryPotential hp hp1 ψ).property N ∧
        ∀ b : BoundaryCondition,
          b.heightSpectrum hp (periodOneBoundaryPotential hp hp1 ψ).val
            (periodOneBoundaryPotential hp hp1 ψ).property N ((1+8*‖ψ‖)^p.toReal) =
            b.centralSpectrum hp (periodOneBoundaryPotential hp hp1 ψ).val
              (periodOneBoundaryPotential hp hp1 ψ).property N ∧
          (∑ z ∈ b.heightSpectrum hp (periodOneBoundaryPotential hp hp1 ψ).val
            (periodOneBoundaryPotential hp hp1 ψ).property N ((1+8*‖ψ‖)^p.toReal),
            b.algebraicMultiplicity hp (periodOneBoundaryPotential hp hp1 ψ).val
              (periodOneBoundaryPotential hp hp1 ψ).property z) = 2*N+1 ∧
          b.spectrum hp (periodOneBoundaryPotential hp hp1 ψ).val
            (periodOneBoundaryPotential hp hp1 ψ).property ⊆
            heightSpectralBox N ((1+8*‖ψ‖)^p.toReal) ∪ highSpectralDisks N (Real.pi/4) := by
  obtain ⟨K,hK,V,hV,hconv,hφ,h0,_,_,hlabels⟩ := exists_uniform_sourceBoundaryLabels hp hp1 φ
  obtain ⟨L,hL⟩ := exists_nat_ge ((1+8*(‖φ‖+1))^p.toReal)
  let U := V ∩ ball (0 : CoeffPair p) (‖φ‖+1)
  refine ⟨max K L,hK.trans_le (le_max_left _ _),U,hV.inter isOpen_ball,
    hconv.inter (convex_ball _ _),⟨hφ,?_⟩,⟨h0,?_⟩,?_⟩
  · simpa only [mem_ball_zero_iff] using lt_add_one ‖φ‖
  · simp only [mem_ball_zero_iff,norm_zero]; positivity
  · intro ψ hψ N hN
    have hc := ((hlabels ψ hψ.1 .dirichlet).1 N ((le_max_left _ _).trans hN)).counting
    have hHN : (1+8*‖ψ‖)^p.toReal ≤ (N : ℝ) := by
      have hn := (mem_ball_zero_iff.mp hψ.2).le
      apply le_trans _ (hL.trans (by exact_mod_cast (le_max_right K L).trans hN))
      gcongr
    refine ⟨hc,fun b => ?_⟩
    have he := b.heightSpectrum_eq_central hp _ _ N hHN (hheight ψ b)
    refine ⟨he,?_,?_⟩
    · rw [he]
      exact hc.central_multiplicity b
    · intro z hz
      rcases hc.spectrum_subset b hz with hbox | hdisc
      · exact Or.inl ⟨hbox.1,hheight ψ b z hz⟩
      · exact Or.inr hdisc

/-- At p=2 the completed ordinary extension is contractive in the original source norm. -/
theorem norm_periodOneBoundaryPotential_two_le (φ : CoeffPair 2) :
    ‖(periodOneBoundaryPotential (by norm_num) (by norm_num) φ).val‖ ≤ ‖φ‖ := by
  change ‖BoundaryCondition.intervalExtensionCLM .dirichlet (by norm_num) (by norm_num)
    (CoeffPair.toMax 2 φ)‖ ≤ ‖φ‖
  rw [BoundaryCondition.intervalExtensionCLM_two]
  exact (BoundaryCondition.norm_hilbertIntervalExtension_apply_le .dirichlet _).trans
    (CoeffPair.norm_toMax_le φ)

/-- Both ordinary boundary spectra satisfy the unchanged printed Hilbert height. -/
theorem sourceBoundarySpectrum_abs_im_lt_printed_height_two (b : BoundaryCondition)
    (φ : CoeffPair 2) {z : ℂ} (hz : z ∈ b.spectrum (by norm_num)
      (periodOneBoundaryPotential (by norm_num) (by norm_num) φ).val
      (periodOneBoundaryPotential (by norm_num) (by norm_num) φ).property) :
    |z.im| < (1+8*‖φ‖)^2 :=
  abs_im_lt_hilbert_height _ (norm_periodOneBoundaryPotential_two_le φ)
    (b.spectrum_subset_periodic (by norm_num) _ _ hz)

/-- Theorem 1.4's printed box, both boundary counts, and exhaustion at p=2.
The common counting data also gives exactly one simple root in every high disk. -/
theorem sourceTheorem1_4_two (φ : CoeffPair 2) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∃ U : Set (CoeffPair 2),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ N : ℕ, N₀ ≤ N →
        BoundaryCountingData (by norm_num) (periodOneBoundaryPotential (by norm_num) (by norm_num) ψ).val
          (periodOneBoundaryPotential (by norm_num) (by norm_num) ψ).property N ∧
        ∀ b : BoundaryCondition,
          b.heightSpectrum (by norm_num) (periodOneBoundaryPotential (by norm_num) (by norm_num) ψ).val
            (periodOneBoundaryPotential (by norm_num) (by norm_num) ψ).property N ((1+8*‖ψ‖)^2) =
            b.centralSpectrum (by norm_num) (periodOneBoundaryPotential (by norm_num) (by norm_num) ψ).val
              (periodOneBoundaryPotential (by norm_num) (by norm_num) ψ).property N ∧
          (∑ z ∈ b.heightSpectrum (by norm_num) (periodOneBoundaryPotential (by norm_num) (by norm_num) ψ).val
            (periodOneBoundaryPotential (by norm_num) (by norm_num) ψ).property N ((1+8*‖ψ‖)^2),
            b.algebraicMultiplicity (by norm_num) (periodOneBoundaryPotential (by norm_num) (by norm_num) ψ).val
              (periodOneBoundaryPotential (by norm_num) (by norm_num) ψ).property z) = 2*N+1 ∧
          b.spectrum (by norm_num) (periodOneBoundaryPotential (by norm_num) (by norm_num) ψ).val
            (periodOneBoundaryPotential (by norm_num) (by norm_num) ψ).property ⊆
            heightSpectralBox N ((1+8*‖ψ‖)^2) ∪ highSpectralDisks N (Real.pi/4) := by
  simpa only [ENNReal.toReal_ofNat,Real.rpow_ofNat] using
    exists_source_boundaryCounting_printed_height_of_bound (by norm_num) (by norm_num)
      (fun ψ b z hz => by
        simpa only [ENNReal.toReal_ofNat,Real.rpow_ofNat] using
          (sourceBoundarySpectrum_abs_im_lt_printed_height_two b ψ hz).le) φ

end NLS.ZakharovShabat
