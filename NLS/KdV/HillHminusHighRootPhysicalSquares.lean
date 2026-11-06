import NLS.KdV.HillHminusHighRootNormalization
import NLS.KdV.HillDeflatedLocalPhysicalMatching

/-! # Actual high deflated root squares on an original physical neighborhood -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillHminus_high_root_physical_square_neighborhood
    (n : ℕ+) (hn : 2 ≤ (n : ℕ)) (r : ℝ) (hr : 0 < r)
    (V : Set PeriodOneHminusOne) (hV : IsOpen V) (h0V : (0 : PeriodOneHminusOne) ∈ V)
    (hpairs : ∀ a ∈ V, ∃ l u : ℂ, HillHminusHighGapPair a n r l u)
    (U : ℂ × PeriodOneHminusOne → ℂ)
    (hUa : AnalyticOnNhd ℂ U
      (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) ×ˢ V))
    (hfac : ∀ t ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) ×ˢ V,
      hillHminusRadicand t.2 t.1=hillHminusGapPolynomial n r t*(U t/(n : ℂ))^2) :
    ∃ s : ℝ, ∃ W : Set RealPeriodOneHillPotential, 0 < s ∧ IsOpen W ∧
      (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential) ∈ W ∧
      ∀ p ∈ W, ∀ z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) s,
        (z,hillOriginalHminusSource p.val) ∈
          ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) ×ˢ V ∧
        z ∈ hillGapFilledDomain p.val p.property.1 p.property.2 (n : ℕ) ∧
        hillLocalDeflatedComplexRoot 0 h0q h0r (n : ℕ) (z,SpectralWeight.one.toCoeff p.val)=
          hillDeflatedEnergyCanonicalRoot p.val p.property.1 p.property.2 (n : ℕ) z ∧
        (U (z,hillOriginalHminusSource p.val)/(n : ℂ))^2=
          hillDeflatedEnergyCanonicalRoot p.val p.property.1 p.property.2 (n : ℕ) z^2 := by
  let c : ℂ := ((Real.pi : ℂ)*(n : ℕ))^2
  have hc : (hillRealGapCenter 0 h0q h0r (n : ℕ) : ℂ)=c := by
    rw [hillFreeGapCenter h0q h0r (n : ℕ) n.property]
    simp only [freeHillValue,Int.cast_natCast,ofReal_mul,ofReal_pow,ofReal_natCast]
    dsimp only [c]
    ring
  have hR : 0 < Real.pi*(n : ℕ)*r := by positivity
  have hR0 : 0 < hillRealGapHalfLength 0 h0q h0r (n : ℕ)+hillRealGapCollar 0 h0q h0r (n : ℕ) :=
    add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r (n : ℕ) n.property).1
      (hillRealGapContour_geometry 0 h0q h0r (n : ℕ) n.property).2.1
  have hcb : c ∈ ball (hillRealGapCenter 0 h0q h0r (n : ℕ) : ℂ)
      (hillRealGapHalfLength 0 h0q h0r (n : ℕ)+hillRealGapCollar 0 h0q h0r (n : ℕ)) := by
    rw [hc]
    exact mem_ball_self hR0
  obtain ⟨s,hs,W0,hW0,h0W0,hmatch⟩ := exists_hillLocalDeflatedComplexRoot_local_physical_matching
    0 h0q h0r (n : ℕ) n.property c hcb
  obtain ⟨Y,hYsub,hY,h0Y⟩ := _root_.mem_nhds_iff.mp
    (hillHminusGapPolynomial_original_label_germ h0q h0r n hn r hr V hV h0V hpairs)
  let W : Set RealPeriodOneHillPotential :=
    (W0 ∩ (fun p : RealPeriodOneHillPotential => hillOriginalHminusSource p.val) ⁻¹' V) ∩ Y
  have hW : IsOpen W :=
    (hW0.inter (hV.preimage (hillOriginalHminusSource.continuous.comp continuous_subtype_val))).inter hY
  have h0W : (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential) ∈ W := by
    refine ⟨⟨h0W0,?_⟩,h0Y⟩
    change hillOriginalHminusSource (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ V
    simpa only [map_zero] using h0V
  let ρ : ℝ := min s (Real.pi*(n : ℕ)*r)
  have hρ : 0 < ρ := lt_min hs hR
  have hdom (p : RealPeriodOneHillPotential) (hp : p ∈ W) (z : ℂ) (hz : z ∈ ball c ρ) :
      (z,hillOriginalHminusSource p.val) ∈ ball c (Real.pi*(n : ℕ)*r) ×ˢ V ∧
      z ∈ hillGapFilledDomain p.val p.property.1 p.property.2 (n : ℕ) ∧
      hillLocalDeflatedComplexRoot 0 h0q h0r (n : ℕ) (z,SpectralWeight.one.toCoeff p.val)=
        hillDeflatedEnergyCanonicalRoot p.val p.property.1 p.property.2 (n : ℕ) z := by
    have hh := hmatch p hp.1.1 z (ball_subset_ball (min_le_left s _) hz)
    exact ⟨⟨ball_subset_ball (min_le_right s _) hz,hp.1.2⟩,hh.2.1,hh.2.2⟩
  have hsq (p : RealPeriodOneHillPotential) (hp : p ∈ W) :
      EqOn (fun z => (U (z,hillOriginalHminusSource p.val)/(n : ℂ))^2)
        (fun z => hillDeflatedEnergyCanonicalRoot p.val p.property.1 p.property.2 (n : ℕ) z^2) (ball c ρ) := by
    have hleft : ContinuousOn (fun z => U (z,hillOriginalHminusSource p.val)/(n : ℂ)) (ball c ρ) := by
      intro z hz
      exact (((hUa (z,hillOriginalHminusSource p.val) (hdom p hp z hz).1).comp
        (f := fun z : ℂ => (z,hillOriginalHminusSource p.val))
        (analyticAt_id.prod analyticAt_const)).div_const).continuousAt.continuousWithinAt
    have hright : ContinuousOn (hillDeflatedEnergyCanonicalRoot p.val p.property.1 p.property.2 (n : ℕ)) (ball c ρ) :=
      (analyticOnNhd_hillDeflatedEnergyCanonicalRoot p.val p.property.1 p.property.2 (n : ℕ)).continuousOn.mono
        (fun z hz => (hdom p hp z hz).2.1)
    apply continuous_sq_eq_of_real_quadratic_products (ball c ρ) isOpen_ball _ _ hleft hright
      (hillRealLabels p.val p.property.1 p.property.2 (2*(n : ℕ)-1))
      (hillRealLabels p.val p.property.1 p.property.2 (2*(n : ℕ)))
    intro z hz
    have hnew := hfac (z,hillOriginalHminusSource p.val) (hdom p hp z hz).1
    calc
      _ = hillHminusGapPolynomial n r (z,hillOriginalHminusSource p.val)*
          (U (z,hillOriginalHminusSource p.val)/(n : ℂ))^2 :=
        congrArg (fun w : ℂ => w*(U (z,hillOriginalHminusSource p.val)/(n : ℂ))^2) (hYsub hp.2 z).symm
      _ = hillHminusRadicand (hillOriginalHminusSource p.val) z := hnew.symm
      _ = hillL2Radicand (SpectralWeight.one.toCoeff p.val) z :=
        hillHminusRadicand_original_source_agreement p.val p.property.1 z
      _ = _ := hillL2Radicand_eq_gap_polynomial_mul_deflated_sq p.val p.property.1 p.property.2
        (n : ℕ) n.property z (hdom p hp z hz).2.1
  refine ⟨ρ,W,hρ,hW,h0W,?_⟩
  intro p hp z hz
  obtain ⟨ht,hf,he⟩ := hdom p hp z hz
  exact ⟨ht,hf,he,hsq p hp hz⟩

end NLS.KdV
