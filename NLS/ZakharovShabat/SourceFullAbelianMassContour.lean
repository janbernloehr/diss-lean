import NLS.ComplexAnalysis.SquareOverFrequencyContour
import NLS.ZakharovShabat.SourceFullAbelianMassCoefficient

/-! # The physical mass as the squared canonical primitive divided by frequency

The original mass-calibrated inversion germ fixes the exact coefficient.
The identity holds on every positive circle enclosing the actual open
gaps, independently of the chosen ambient Abelian neighborhood.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

theorem exists_sourceFullAbelian_finiteGap_mass_contour
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (φ : realTypeSourceSubmodule p)
    (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ T : ℝ, 0 < T ∧ ∀ R : ℝ, T ≤ R →
      (∮ z in C(0,R), (sourceFullAbelianPrimitive hp hp1 W 0 (z,φ.val))^2/z) =
        (2*Real.pi*I : ℂ)*(∑' k : ℤ, φ.val.fst k*φ.val.snd (-k)) := by
  obtain ⟨S,_hS,r,hr,_hrS,A,hA,hA0,hd,hval⟩ :=
    exists_sourceFullAbelian_finiteGap_mass_inversion C φ hφ hf
  obtain ⟨T,hT,hcontour⟩ := exists_phase_square_over_frequency_contour A
    (hA 0 (mem_ball_self hr)) hA0 _ hd
  refine ⟨max (S+1) T,hT.trans_le (le_max_right _ _),?_⟩
  intro R hR
  rw [←hcontour R ((le_max_right _ _).trans hR)]
  apply circleIntegral.integral_congr (hT.trans_le ((le_max_right _ _).trans hR)).le
  intro z hz
  have hn : ‖z‖ = R := by simpa only [mem_sphere,dist_zero_right] using hz
  dsimp only
  rw [hval 0 z (by rw [hn]; linarith [le_max_left (S+1) T])]
  simp only [Int.cast_zero,mul_zero,add_zero]

/-- The physical mass contour is independent of the actual chosen chart. -/
theorem exists_sourceFullAbelian_mass_contour_of_chart
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1)
    (D : SourceAbelianSpectralChart hp hp1 W φ.val) :
    ∃ T : ℝ, 0 < T ∧ ∀ R : ℝ, T ≤ R →
      (∮ z in C(0,R), (sourceFullAbelianPrimitive hp hp1 W 0 (z,φ.val))^2/z) =
        (2*Real.pi*I : ℂ)*(∑' k : ℤ, φ.val.fst k*φ.val.snd (-k)) := by
  obtain ⟨V,_,_,hfamilies⟩ := exists_sourceFullAbelianUniformCauchyFamilies hp hp1
  obtain ⟨C,hC⟩ := hfamilies φ
  have hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius := by
    rw [hC]
    exact mem_ball_self C.discs.sourceRadius_pos
  obtain ⟨E⟩ := C.charts φ.val hφ
  obtain ⟨T,hT,hcontour⟩ := exists_sourceFullAbelian_finiteGap_mass_contour C φ hφ hf
  obtain ⟨S,_,hS⟩ := exists_exterior_subset_sourceOpenGapComplement_finiteGap hp hp1 φ hf
  refine ⟨max T (S+1),hT.trans_le (le_max_left _ _),?_⟩
  intro R hR
  rw [←hcontour R ((le_max_left _ _).trans hR)]
  apply circleIntegral.integral_congr (hT.trans_le ((le_max_left _ _).trans hR)).le
  intro z hz
  have hn : ‖z‖ = R := by simpa only [mem_sphere,dist_zero_right] using hz
  dsimp only
  rw [sourceFullAbelianPrimitive_independent_neighborhood D E 0 z (hS (by
    change S < ‖z‖
    rw [hn]
    linarith [le_max_right T (S+1)]))]

/-- Every positive circle enclosing all actual open gaps has this mass
value. No information at the excluded interior frequency zero is used. -/
theorem sourceFullAbelian_mass_contour_eq_of_enclosing
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1)
    (D : SourceAbelianSpectralChart hp hp1 W φ.val) (R : ℝ) (hR : 0 < R)
    (hgap : ∀ k : ℤ, canonicalPeriodicGap hp hp1 (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) k ≠ 0 → sourcePeriodicSegment hp hp1 φ.val k ⊆ ball 0 R) :
    (∮ z in C(0,R), (sourceFullAbelianPrimitive hp hp1 W 0 (z,φ.val))^2/z) =
      (2*Real.pi*I : ℂ)*(∑' k : ℤ, φ.val.fst k*φ.val.snd (-k)) := by
  obtain ⟨T,_,hphysical⟩ := exists_sourceFullAbelian_mass_contour_of_chart φ hf D
  let S := max R T
  have ha : AnalyticOnNhd ℂ (fun z => (sourceFullAbelianPrimitive hp hp1 W 0 (z,φ.val))^2/z)
      (closedBall 0 S \ ball 0 R) := by
    intro z hz
    have hz0 : z ≠ 0 := by rintro rfl; exact hz.2 (mem_ball_self hR)
    exact ((sourceFullAbelianPrimitive_spectral_analytic D 0 z (by
      intro k hk hzk
      exact hz.2 (hgap k hk hzk))).pow 2).div analyticAt_id hz0
  have he := circleIntegral_eq_of_differentiable_on_annulus_off_countable hR (le_max_left R T)
    countable_empty ha.continuousOn (by
      intro z hz
      exact (ha z ⟨ball_subset_closedBall hz.1.1,
        fun h => hz.1.2 (ball_subset_closedBall h)⟩).differentiableAt)
  exact he.symm.trans (hphysical S (le_max_right R T))

end NLS.ZakharovShabat
