import NLS.ZakharovShabat.SourcePrintedHeightCounting
import NLS.ZakharovShabat.PrintedHeightFour

/-! # Proposition 3.1 on the entire period-two potential space

The parameter has the original finite-exponent component-sum norm. No even
support or period-one embedding is assumed. The unchanged printed height
is proved through exponent four; its unrestricted assertion is false.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The qualitative counting theorem on the original period-two source space at every
finite exponent. This uses the established height-N box, not the printed norm-dependent height. -/
theorem exists_periodTwo_periodicCountingData (hp : p ≠ ⊤) (φ : CoeffPair p) :
    ∃ N₀ : ℕ, ∃ U : Set (CoeffPair p), 0 < N₀ ∧ IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ N : ℕ, N₀ ≤ N → PeriodicCountingData hp (CoeffPair.toMax p ψ) N := by
  obtain ⟨N₀,V,hN₀,hV,hconv,hφ,h0,_,_,hc⟩ :=
    exists_uniform_periodicCountingData hp (CoeffPair.toMax p φ)
  refine ⟨N₀, (CoeffPair.toMax p) ⁻¹' V, hN₀,
    hV.preimage (CoeffPair.toMax p).continuous,
    hconv.linear_preimage ((CoeffPair.toMax p).toContinuousLinearMap.restrictScalars ℝ).toLinearMap,
    hφ, ?_, fun ψ hψ N hN => hc _ hψ N hN⟩
  simpa only [mem_preimage, map_zero] using h0

/-- A resolvent estimate with a nonnegative coefficient supplies all source
counting and projection conclusions on one common neighborhood. -/
theorem exists_periodTwo_periodicCounting_coefficient_height_of_resolvent (hp : p ≠ ⊤)
    (C : ℝ) (hC : 0 ≤ C)
    (hres : ∀ ψ : CoeffPair p, ∀ z : ℂ, (1+C*‖ψ‖)^p.toReal ≤ |z.im| →
      z ∈ resolventSet hp (CoeffPair.toMax p ψ))
    (φ : CoeffPair p) :
    ∃ N₀ : ℕ, ∃ V : Set (CoeffPair p), 0 < N₀ ∧ IsOpen V ∧ Convex ℝ V ∧ φ ∈ V ∧ 0 ∈ V ∧
      ∀ N : ℕ, N₀ ≤ N →
        AnalyticOnNhd ℂ (fun ψ => heightRectangleIntegral hp (CoeffPair.toMax p ψ) N
          ((1+C*‖ψ‖)^p.toReal)) V ∧
        ∀ ψ ∈ V, PeriodicCountingData hp (CoeffPair.toMax p ψ) N ∧
          heightPeriodicSpectrum hp (CoeffPair.toMax p ψ) N ((1+C*‖ψ‖)^p.toReal) =
            centralPeriodicSpectrum hp (CoeffPair.toMax p ψ) N ∧
          (∑ z ∈ heightPeriodicSpectrum hp (CoeffPair.toMax p ψ) N ((1+C*‖ψ‖)^p.toReal),
            periodicAlgebraicMultiplicity hp (CoeffPair.toMax p ψ) z) = 4*N+2 ∧
          heightRectangleIntegral hp (CoeffPair.toMax p ψ) N ((1+C*‖ψ‖)^p.toReal) =
            centralSpectralProjection hp (CoeffPair.toMax p ψ) N ∧
          periodicSpectrum hp (CoeffPair.toMax p ψ) ⊆
            heightSpectralBox N ((1+C*‖ψ‖)^p.toReal) ∪ highSpectralDisks N (Real.pi/4) := by
  have hspec (ψ : CoeffPair p) {z : ℂ} (hz : z ∈ periodicSpectrum hp (CoeffPair.toMax p ψ)) :
      |z.im| < (1+C*‖ψ‖)^p.toReal := by
    by_contra h
    exact hz (hres ψ z (le_of_not_gt h))
  obtain ⟨K,U,hK,hU,hconv,hφ,h0,han,_,hcount⟩ :=
    exists_uniform_periodicCountingData hp (CoeffPair.toMax p φ)
  obtain ⟨L,hL⟩ := exists_nat_ge ((1+C*(‖φ‖+1))^p.toReal)
  let V : Set (CoeffPair p) := ((CoeffPair.toMax p) ⁻¹' U) ∩ ball 0 (‖φ‖+1)
  have ho : IsOpen V := (hU.preimage (CoeffPair.toMax p).continuous).inter isOpen_ball
  have hheight (ψ : CoeffPair p) (hψ : ψ ∈ V) (N : ℕ) (hN : max K L ≤ N) :
      (1+C*‖ψ‖)^p.toReal ≤ (N:ℝ) := by
    have hn : ‖ψ‖ ≤ ‖φ‖+1 := (mem_ball_zero_iff.mp hψ.2).le
    apply le_trans _ (hL.trans (by exact_mod_cast (le_max_right K L).trans hN))
    gcongr
  have he (ψ : CoeffPair p) (hψ : ψ ∈ V) (N : ℕ) (hN : max K L ≤ N) :
      heightRectangleIntegral hp (CoeffPair.toMax p ψ) N ((1+C*‖ψ‖)^p.toReal) =
        centralSpectralProjection hp (CoeffPair.toMax p ψ) N := by
    apply heightRectangleIntegral_eq_centralSpectralProjection hp _ N (by positivity) (hheight ψ hψ N hN)
      (hcount _ hψ.1 N ((le_max_left _ _).trans hN)).central_boundary
    intro z hz
    exact hres ψ z hz
  refine ⟨max K L,V,hK.trans_le (le_max_left _ _),ho,
    (hconv.linear_preimage ((CoeffPair.toMax p).toContinuousLinearMap.restrictScalars ℝ).toLinearMap).inter
      (convex_ball _ _),⟨hφ,?_⟩,⟨?_,?_⟩,?_⟩
  · simpa only [mem_ball_zero_iff] using lt_add_one ‖φ‖
  · simpa only [mem_preimage,map_zero] using h0
  · simp only [mem_ball_zero_iff,norm_zero]; positivity
  · intro N hN
    refine ⟨?_,?_⟩
    · intro ψ hψ
      have hc := ((han N ((le_max_left _ _).trans hN)).1 _ hψ.1).comp
        (f := CoeffPair.toMax p) ((CoeffPair.toMax p).analyticAt ψ)
      apply hc.congr
      filter_upwards [ho.mem_nhds hψ] with a ha
      exact (he a ha N hN).symm
    · intro ψ hψ
      have hd := hcount _ hψ.1 N ((le_max_left _ _).trans hN)
      have hs := heightPeriodicSpectrum_eq_central hp (CoeffPair.toMax p ψ) N (hheight ψ hψ N hN)
        (fun z hz => (hspec ψ hz).le)
      refine ⟨hd,hs,?_,he ψ hψ N hN,?_⟩
      · rw [hs]
        exact hd.central_multiplicity
      · intro z hz
        rcases hd.spectrum_subset hz with hb | hb
        · exact Or.inl ⟨hb.1,(hspec ψ hz).le⟩
        · exact Or.inr hb

/-- The full period-two version of the unchanged printed-height counting theorem.
The same neighborhood works for every larger cutoff and for the actual moving projections. -/
theorem exists_periodTwo_periodicCounting_printed_height_up_to_four (hp : p ≠ ⊤) (hp4 : p ≤ 4)
    (φ : CoeffPair p) :
    ∃ N₀ : ℕ, ∃ V : Set (CoeffPair p), 0 < N₀ ∧ IsOpen V ∧ Convex ℝ V ∧ φ ∈ V ∧ 0 ∈ V ∧
      ∀ N : ℕ, N₀ ≤ N →
        AnalyticOnNhd ℂ (fun ψ => heightRectangleIntegral hp (CoeffPair.toMax p ψ) N
          ((1+8*‖ψ‖)^p.toReal)) V ∧
        ∀ ψ ∈ V, PeriodicCountingData hp (CoeffPair.toMax p ψ) N ∧
          heightPeriodicSpectrum hp (CoeffPair.toMax p ψ) N ((1+8*‖ψ‖)^p.toReal) =
            centralPeriodicSpectrum hp (CoeffPair.toMax p ψ) N ∧
          (∑ z ∈ heightPeriodicSpectrum hp (CoeffPair.toMax p ψ) N ((1+8*‖ψ‖)^p.toReal),
            periodicAlgebraicMultiplicity hp (CoeffPair.toMax p ψ) z) = 4*N+2 ∧
          heightRectangleIntegral hp (CoeffPair.toMax p ψ) N ((1+8*‖ψ‖)^p.toReal) =
            centralSpectralProjection hp (CoeffPair.toMax p ψ) N ∧
          periodicSpectrum hp (CoeffPair.toMax p ψ) ⊆
            heightSpectralBox N ((1+8*‖ψ‖)^p.toReal) ∪ highSpectralDisks N (Real.pi/4) :=
  exists_periodTwo_periodicCounting_coefficient_height_of_resolvent hp 8 (by norm_num)
    (fun ψ _z hz => mem_resolventSet_of_printed_height_up_to_four hp hp4 _
      (CoeffPair.norm_toMax_le ψ) hz) φ

end NLS.ZakharovShabat
