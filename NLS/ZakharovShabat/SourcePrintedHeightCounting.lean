import NLS.ZakharovShabat.PrintedHeight
import NLS.ZakharovShabat.HeightRectangleContour
import NLS.ZakharovShabat.PeriodicCounting
import NLS.ZakharovShabat.PeriodOneEmbedding

/-! # Theorem 1.1: counting in the printed height box for 1 < p ≤ 2

One source neighborhood supports the printed norm-dependent height, full
algebraic counting and parity, exclusion of other spectral points, and analytic
moving rectangular projections. The same construction also works at p = 1.
The unchanged height is proved through p=4 in SourcePrintedHeightFourCounting.
SourcePeriodicHeightCounterexample refutes its all-exponent assertion.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Actual period-one source spectra satisfy the printed height bound for 1 ≤ p ≤ 2. -/
theorem sourceSpectrum_abs_im_lt_printed_height (hp : p ≠ ⊤) (hp2 : p ≤ 2)
    (φ : CoeffPair p) {z : ℂ} (hz : z ∈ periodicSpectrum hp (periodOnePotential φ)) :
    |z.im| < (1+8*‖φ‖)^p.toReal :=
  abs_im_lt_printed_height hp hp2 _ (norm_periodOnePotential_le φ) hz

/-- A resolvent estimate with a nonnegative coefficient supplies all source
counting and projection conclusions on one common neighborhood. -/
theorem exists_source_periodicCounting_coefficient_height_of_resolvent (hp : p ≠ ⊤)
    (C : ℝ) (hC : 0 ≤ C)
    (hres : ∀ ψ : CoeffPair p, ∀ z : ℂ, (1+C*‖ψ‖)^p.toReal ≤ |z.im| →
      z ∈ resolventSet hp (periodOnePotential ψ))
    (φ : CoeffPair p) :
    ∃ N₀ : ℕ, ∃ V : Set (CoeffPair p), 0 < N₀ ∧ IsOpen V ∧ Convex ℝ V ∧ φ ∈ V ∧ 0 ∈ V ∧
      ∀ N : ℕ, N₀ ≤ N →
        AnalyticOnNhd ℂ (fun ψ => heightRectangleIntegral hp (periodOnePotential ψ) N
          ((1+C*‖ψ‖)^p.toReal)) V ∧
        ∀ ψ ∈ V, PeriodicCountingData hp (periodOnePotential ψ) N ∧
          heightPeriodicSpectrum hp (periodOnePotential ψ) N ((1+C*‖ψ‖)^p.toReal) =
            centralPeriodicSpectrum hp (periodOnePotential ψ) N ∧
          (∑ z ∈ heightPeriodicSpectrum hp (periodOnePotential ψ) N ((1+C*‖ψ‖)^p.toReal),
            periodicAlgebraicMultiplicity hp (periodOnePotential ψ) z) = 4*N+2 ∧
          heightRectangleIntegral hp (periodOnePotential ψ) N ((1+C*‖ψ‖)^p.toReal) =
            centralSpectralProjection hp (periodOnePotential ψ) N ∧
          periodicSpectrum hp (periodOnePotential ψ) ⊆
            heightSpectralBox N ((1+C*‖ψ‖)^p.toReal) ∪ highSpectralDisks N (Real.pi/4) := by
  have hspec (ψ : CoeffPair p) {z : ℂ} (hz : z ∈ periodicSpectrum hp (periodOnePotential ψ)) :
      |z.im| < (1+C*‖ψ‖)^p.toReal := by
    by_contra h
    exact hz (hres ψ z (le_of_not_gt h))
  obtain ⟨K,U,hK,hU,hconv,hφ,h0,han,_,hcount⟩ :=
    exists_uniform_periodicCountingData hp (periodOnePotential φ)
  obtain ⟨L,hL⟩ := exists_nat_ge ((1+C*(‖φ‖+1))^p.toReal)
  let V : Set (CoeffPair p) := (periodOnePotential ⁻¹' U) ∩ ball 0 (‖φ‖+1)
  have ho : IsOpen V := (hU.preimage (periodOnePotential (p := p)).continuous).inter isOpen_ball
  have hheight (ψ : CoeffPair p) (hψ : ψ ∈ V) (N : ℕ) (hN : max K L ≤ N) :
      (1+C*‖ψ‖)^p.toReal ≤ (N:ℝ) := by
    have hn : ‖ψ‖ ≤ ‖φ‖+1 := (mem_ball_zero_iff.mp hψ.2).le
    apply le_trans _ (hL.trans (by exact_mod_cast (le_max_right K L).trans hN))
    gcongr
  have he (ψ : CoeffPair p) (hψ : ψ ∈ V) (N : ℕ) (hN : max K L ≤ N) :
      heightRectangleIntegral hp (periodOnePotential ψ) N ((1+C*‖ψ‖)^p.toReal) =
        centralSpectralProjection hp (periodOnePotential ψ) N := by
    apply heightRectangleIntegral_eq_centralSpectralProjection hp _ N (by positivity) (hheight ψ hψ N hN)
      (hcount _ hψ.1 N ((le_max_left _ _).trans hN)).central_boundary
    intro z hz
    exact hres ψ z hz
  refine ⟨max K L,V,hK.trans_le (le_max_left _ _),ho,
    (hconv.linear_preimage ((periodOnePotential (p := p)).restrictScalars ℝ).toLinearMap).inter
      (convex_ball _ _),⟨hφ,?_⟩,⟨?_,?_⟩,?_⟩
  · simpa only [mem_ball_zero_iff] using lt_add_one ‖φ‖
  · simpa only [mem_preimage,map_zero] using h0
  · simp only [mem_ball_zero_iff,norm_zero]; positivity
  · intro N hN
    refine ⟨?_,?_⟩
    · intro ψ hψ
      have hc := ((han N ((le_max_left _ _).trans hN)).1 _ hψ.1).comp
        (f := periodOnePotential) ((periodOnePotential (p := p)).analyticAt ψ)
      apply hc.congr
      filter_upwards [ho.mem_nhds hψ] with a ha
      exact (he a ha N hN).symm
    · intro ψ hψ
      have hd := hcount _ hψ.1 N ((le_max_left _ _).trans hN)
      have hs := heightPeriodicSpectrum_eq_central hp (periodOnePotential ψ) N (hheight ψ hψ N hN)
        (fun z hz => (hspec ψ hz).le)
      refine ⟨hd,hs,?_,he ψ hψ N hN,?_⟩
      · rw [hs]
        exact hd.central_multiplicity
      · intro z hz
        rcases hd.spectrum_subset hz with hb | hb
        · exact Or.inl ⟨hb.1,(hspec ψ hz).le⟩
        · exact Or.inr hb

/-- The unchanged printed coefficient specializes the general counting-height theorem. -/
theorem exists_source_periodicCounting_printed_height_of_resolvent (hp : p ≠ ⊤)
    (hres : ∀ ψ : CoeffPair p, ∀ z : ℂ, (1+8*‖ψ‖)^p.toReal ≤ |z.im| →
      z ∈ resolventSet hp (periodOnePotential ψ))
    (φ : CoeffPair p) :
    ∃ N₀ : ℕ, ∃ V : Set (CoeffPair p), 0 < N₀ ∧ IsOpen V ∧ Convex ℝ V ∧ φ ∈ V ∧ 0 ∈ V ∧
      ∀ N : ℕ, N₀ ≤ N →
        AnalyticOnNhd ℂ (fun ψ => heightRectangleIntegral hp (periodOnePotential ψ) N
          ((1+8*‖ψ‖)^p.toReal)) V ∧
        ∀ ψ ∈ V, PeriodicCountingData hp (periodOnePotential ψ) N ∧
          heightPeriodicSpectrum hp (periodOnePotential ψ) N ((1+8*‖ψ‖)^p.toReal) =
            centralPeriodicSpectrum hp (periodOnePotential ψ) N ∧
          (∑ z ∈ heightPeriodicSpectrum hp (periodOnePotential ψ) N ((1+8*‖ψ‖)^p.toReal),
            periodicAlgebraicMultiplicity hp (periodOnePotential ψ) z) = 4*N+2 ∧
          heightRectangleIntegral hp (periodOnePotential ψ) N ((1+8*‖ψ‖)^p.toReal) =
            centralSpectralProjection hp (periodOnePotential ψ) N ∧
          periodicSpectrum hp (periodOnePotential ψ) ⊆
            heightSpectralBox N ((1+8*‖ψ‖)^p.toReal) ∪ highSpectralDisks N (Real.pi/4) :=
  exists_source_periodicCounting_coefficient_height_of_resolvent hp 8 (by norm_num) hres φ

/-- The printed boxes have the full central count and actual analytic projections
on one neighborhood, simultaneously with every larger frequency cutoff. -/
theorem exists_source_periodicCounting_printed_height (hp : p ≠ ⊤) (hp2 : p ≤ 2)
    (φ : CoeffPair p) :
    ∃ N₀ : ℕ, ∃ V : Set (CoeffPair p), 0 < N₀ ∧ IsOpen V ∧ Convex ℝ V ∧ φ ∈ V ∧ 0 ∈ V ∧
      ∀ N : ℕ, N₀ ≤ N →
        AnalyticOnNhd ℂ (fun ψ => heightRectangleIntegral hp (periodOnePotential ψ) N
          ((1+8*‖ψ‖)^p.toReal)) V ∧
        ∀ ψ ∈ V, PeriodicCountingData hp (periodOnePotential ψ) N ∧
          heightPeriodicSpectrum hp (periodOnePotential ψ) N ((1+8*‖ψ‖)^p.toReal) =
            centralPeriodicSpectrum hp (periodOnePotential ψ) N ∧
          (∑ z ∈ heightPeriodicSpectrum hp (periodOnePotential ψ) N ((1+8*‖ψ‖)^p.toReal),
            periodicAlgebraicMultiplicity hp (periodOnePotential ψ) z) = 4*N+2 ∧
          heightRectangleIntegral hp (periodOnePotential ψ) N ((1+8*‖ψ‖)^p.toReal) =
            centralSpectralProjection hp (periodOnePotential ψ) N ∧
          periodicSpectrum hp (periodOnePotential ψ) ⊆
            heightSpectralBox N ((1+8*‖ψ‖)^p.toReal) ∪ highSpectralDisks N (Real.pi/4) :=
  exists_source_periodicCounting_printed_height_of_resolvent hp
    (fun ψ _z hz => mem_resolventSet_of_printed_height hp hp2 _ (norm_periodOnePotential_le ψ) hz) φ

end NLS.ZakharovShabat
