import NLS.KdV.HillHighAbelianContourDecay
import NLS.KdV.HillAbelianCosineDifferential

/-! # Uniform deflated numerator bounds inside high spectral discs -/
noncomputable section
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

include h0q h0r

theorem exists_hillHighGap_deflatedHilbertPsi_sq_decay
    (B : ℝ) (hB : 0 ≤ B) (n : ℕ) (hn : 1 ≤ n) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ K : ℝ, 0 < K ∧
      ∀ q : RealPeriodOneHillPotential, ‖SpectralWeight.one.toCoeff q.val‖ ≤ B →
      ∀ a : Coeff 2, ∀ k : ℕ, N ≤ k → ∀ θ : ℝ,
        ‖hillAbelianHilbertPsi n
          (cosineGapPoint (hillRealGapCenter q.val q.property.1 q.property.2 k)
            (hillRealGapHalfLength q.val q.property.1 q.property.2 k) (θ : ℂ),a)/
          hillDeflatedEnergyCanonicalRoot q.val q.property.1 q.property.2 k
            (cosineGapPoint (hillRealGapCenter q.val q.property.1 q.property.2 k)
              (hillRealGapHalfLength q.val q.property.1 q.property.2 k) (θ : ℂ))‖ ≤
            K*(n : ℝ)*Real.exp ((8/Real.pi^2)*‖a‖)/(k : ℝ)^2 := by
  obtain ⟨N₀,hN₀,K,hK,hbound⟩ := exists_hillHighContour_deflatedHilbertPsi_sq_decay h0q h0r B hB n hn
  obtain ⟨L,hL,D,hD,hcontrol⟩ := exists_hillComplexTailPeriodControl h0q h0r B
  refine ⟨max N₀ L,by omega,K,hK,?_⟩
  intro q hq a k hk θ
  have hk₀ : N₀ ≤ k := (le_max_left _ _).trans hk
  have hkL : L ≤ k := (le_max_right _ _).trans hk
  have hk1 : 1 ≤ k := hL.trans hkL
  let E := cosineGapPoint (hillRealGapCenter q.val q.property.1 q.property.2 k)
    (hillRealGapHalfLength q.val q.property.1 q.property.2 k) (θ : ℂ)
  have hE : E ∈ closedBall (hillRealGapCenter 0 h0q h0r k : ℂ)
      (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k) :=
    ball_subset_closedBall (hillRealGap_mem_high_free_contour_ball_of_control h0q h0r L hL B D hcontrol
      q.val q.property.1 q.property.2 hq k hkL
      (hillCosineGapPoint_mem_real_gap q.val q.property.1 q.property.2 k hk1 θ))
  apply norm_le_of_analytic_closedDisc_sphere_bound _ _
    (add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k hk1).1
      (hillRealGapContour_geometry 0 h0q h0r k hk1).2.1) ?_ _ (hbound q hq a k hk₀) hE
  intro z hz
  have hzfilled := hillHighFreeContour_closedBall_subset_filledDomain h0q h0r L hL B D hcontrol q hq k hkL hz
  have hnum : AnalyticAt ℂ (fun w : ℂ => hillAbelianHilbertPsi n (w,a)) z :=
    (analyticOnNhd_hillAbelianHilbertPsi n (z,a) (mem_univ _)).comp
      (f := fun w : ℂ => (w,a)) (analyticAt_id.prod analyticAt_const)
  exact hnum.div (analyticOnNhd_hillDeflatedEnergyCanonicalRoot q.val q.property.1 q.property.2 k z hzfilled)
    (hillDeflatedEnergyCanonicalRoot_ne_zero q.val q.property.1 q.property.2 k hk1 z hzfilled)

end NLS.KdV
