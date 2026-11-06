import NLS.KdV.HillAllDirichletCharts
import NLS.KdV.HillAllFilledGapRoots
import NLS.KdV.HillScaledComplexDirichletTerminal

/-! # Actual analytic Dirichlet terminal factors for every positive gap -/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillDirichlet_all_terminal_data :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∀ k : ℕ+,
      AnalyticOnNhd ℂ (hillScaledDirichletRoot h0q h0r (1/128) (k : ℕ)) (ball (0 : Coeff 2) η) ∧
      AnalyticOnNhd ℂ (hillScaledComplexDirichletGapTerminal h0q h0r (1/128) (k : ℕ)) (ball (0 : Coeff 2) η) ∧
      ∀ p ∈ ball (0 : Coeff 2) η,
        ‖hillScaledDirichletRoot h0q h0r (1/128) (k : ℕ) p-freeHillEnergy k‖ < (k : ℝ)/16 ∧
        hillScaledComplexDirichletGapTerminal h0q h0r (1/128) (k : ℕ) p^2 =
          hillLocalGapPolynomial 0 h0q h0r (k : ℕ) p (hillScaledDirichletRoot h0q h0r (1/128) (k : ℕ) p) ∧
        ‖hillScaledComplexDirichletGapTerminal h0q h0r (1/128) (k : ℕ) p‖ ≤ (k : ℝ)/8 := by
  obtain ⟨ηm,hηm,hηm1,hmu⟩ := exists_hillScaledDirichletRoot_all_analytic_chart h0q h0r (1/128) (by norm_num) (by norm_num)
  obtain ⟨ηu,hηu,_,hU⟩ := exists_hillFilledFreeGapRoot_all_radius_data h0q h0r
  obtain ⟨ηp,hηp,_,hpairs⟩ := exists_hillFreeGap_all_localized_pairs h0q h0r (1/128) (by norm_num) (by norm_num)
  let η := min ηm (min ηu ηp)
  have hm : ball (0 : Coeff 2) η ⊆ ball 0 ηm := ball_subset_ball (min_le_left _ _)
  have hu : ball (0 : Coeff 2) η ⊆ ball 0 ηu := ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _))
  have hp : ball (0 : Coeff 2) η ⊆ ball 0 ηp := ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨η,lt_min hηm (lt_min hηu hηp),(min_le_left _ _).trans hηm1,?_⟩
  intro k
  let μ := hillScaledDirichletRoot h0q h0r (1/128) (k : ℕ)
  obtain ⟨hc,_,hRhi⟩ := hillFreeGap_energy_radius_geometry h0q h0r k
  let R := hillRealGapHalfLength 0 h0q h0r (k : ℕ)+hillRealGapCollar 0 h0q h0r (k : ℕ)
  have hR : 0 < R := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r (k : ℕ) k.property).1
    (hillRealGapContour_geometry 0 h0q h0r (k : ℕ) k.property).2.1
  have hsmall (p : Coeff 2) (h : p ∈ ball 0 η) : ‖μ p-freeHillEnergy k‖ < (k : ℝ)/16 := by
    have hh := ((hmu k).2 p (hm h)).1
    rw [hc,mem_ball_iff_norm] at hh
    change ‖μ p-freeHillEnergy k‖ < _ at hh
    linarith
  have hμK (p : Coeff 2) (h : p ∈ ball 0 η) : μ p ∈ closedBall (freeHillEnergy k) (k : ℝ) :=
    mem_closedBall_iff_norm.mpr (by linarith [hsmall p h,show (0 : ℝ) < k by positivity])
  have hUn (p : Coeff 2) (h : p ∈ ball 0 η) : hillFilledFreeGapRoot h0q h0r (k : ℕ) (μ p,p) ≠ 0 :=
    ((hU k).2 p (hu h) (μ p) (hμK p h)).1
  refine ⟨(hmu k).1.mono hm,?_,?_⟩
  · intro p h
    have hpair := ((hmu k).1 p (hm h)).prod analyticAt_id
    have hs := (analyticOnNhd_hillDirichletSheetRoot_joint (μ p,p) (mem_univ _)).comp
      (f := fun p : Coeff 2 => (μ p,p)) hpair
    have hr := ((hU k).1 (μ p,p) ⟨hμK p h,hu h⟩).comp
      (f := fun p : Coeff 2 => (μ p,p)) hpair
    exact hs.div hr (hUn p h)
  · intro p h
    have hsquare : hillScaledComplexDirichletGapTerminal h0q h0r (1/128) (k : ℕ) p^2 =
        hillLocalGapPolynomial 0 h0q h0r (k : ℕ) p (μ p) := by
      rw [hillScaledComplexDirichletGapTerminal,div_pow,
        hillDirichletSheetRoot_sq_of_characteristic_zero p (μ p) ((hmu k).2 p (hm h)).2.1,
        ((hU k).2 p (hu h) (μ p) (hμK p h)).2]
      exact mul_div_cancel_right₀ _ (pow_ne_zero 2 (hUn p h))
    refine ⟨hsmall p h,hsquare,?_⟩
    obtain ⟨hb,a,ha,b,hb',_,_,horders⟩ := hpairs k p (hp h)
    have haOld := ball_subset_ball (show (1/128)*R ≤ R by linarith) ha
    have hbOld := ball_subset_ball (show (1/128)*R ≤ R by linarith) hb'
    have haSmall : ‖a-freeHillEnergy k‖ ≤ (k : ℝ)/16 := by
      have hh := mem_ball_iff_norm.mp ha
      rw [hc] at hh
      linarith
    have hbSmall : ‖b-freeHillEnergy k‖ ≤ (k : ℝ)/16 := by
      have hh := mem_ball_iff_norm.mp hb'
      rw [hc] at hh
      linarith
    have hma : ‖μ p-a‖ ≤ (k : ℝ)/8 := by
      have hh := norm_sub_le_norm_sub_add_norm_sub (μ p) (freeHillEnergy k) a
      rw [norm_sub_rev (freeHillEnergy k) a] at hh
      linarith [hsmall p h]
    have hmb : ‖μ p-b‖ ≤ (k : ℝ)/8 := by
      have hh := norm_sub_le_norm_sub_add_norm_sub (μ p) (freeHillEnergy k) b
      rw [norm_sub_rev (freeHillEnergy k) b] at hh
      linarith [hsmall p h]
    have he : ‖hillScaledComplexDirichletGapTerminal h0q h0r (1/128) (k : ℕ) p‖^2 = ‖μ p-a‖*‖μ p-b‖ := by
      rw [← norm_pow,hsquare,hillLocalGapPolynomial_eq_of_pair 0 h0q h0r (k : ℕ) k.property p hb haOld hbOld horders,norm_mul]
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ (k : ℝ)/8)).mp
    rw [he]
    simpa only [pow_two] using mul_le_mul hma hmb (norm_nonneg _) (by positivity : 0 ≤ (k : ℝ)/8)

end NLS.KdV
