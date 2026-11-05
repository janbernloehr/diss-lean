import NLS.KdV.HillAllDirichletCharts
import NLS.KdV.HillRadiusQuadraticData
import NLS.ComplexAnalysis.TwoRootSymmetricBounds

/-! # Uniform analytic symmetric gap charts and complete complex localization -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillLocalGap_all_symmetric_charts :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∀ k : ℕ+,
      AnalyticOnNhd ℂ (hillLocalGapMidpoint 0 h0q h0r (k : ℕ)) (ball (0 : Coeff 2) η) ∧
      AnalyticOnNhd ℂ (hillLocalGapSquare 0 h0q h0r (k : ℕ)) (ball (0 : Coeff 2) η) ∧
      ∀ p ∈ ball (0 : Coeff 2) η,
        ‖hillLocalGapMidpoint 0 h0q h0r (k : ℕ) p-freeHillEnergy k‖ ≤ (k : ℝ)/16 ∧
        ‖sqrt (hillLocalGapSquare 0 h0q h0r (k : ℕ) p/4)‖ ≤ (k : ℝ)/16 := by
  let P := fun (k : ℕ+) (p : Coeff 2) =>
    AnalyticAt ℂ (hillLocalGapMidpoint 0 h0q h0r (k : ℕ)) p ∧
    AnalyticAt ℂ (hillLocalGapSquare 0 h0q h0r (k : ℕ)) p
  have hlocal (k : ℕ+) : ∀ᶠ p in 𝓝 (0 : Coeff 2), P k p := by
    obtain ⟨V,hV,h0V,hM,hS,_⟩ := exists_hillLocalGapSymmetricData_analytic_neighborhood 0 h0q h0r (k : ℕ) k.property
    filter_upwards [hV.mem_nhds (by simpa only [map_zero] using h0V)] with p hp
    exact ⟨hM p hp,hS p hp⟩
  obtain ⟨N,_,htail⟩ := exists_hillFreeGap_bounded_complex_analytic_symmetric_data h0q h0r 1
  obtain ⟨ηa,hηa,hηa1,ha⟩ := exists_ball_forall_pos_index_of_local_and_uniform_tail
    P (0 : Coeff 2) hlocal N 1 (by norm_num)
    (fun k hk p hp => ⟨(htail (k : ℕ) hk).1 p hp,(htail (k : ℕ) hk).2.1 p hp⟩)
  obtain ⟨ηp,hηp,_,hpairs⟩ := exists_hillFreeGap_all_localized_pairs h0q h0r (1/128) (by norm_num) (by norm_num)
  let η := min ηa ηp
  have hη : 0 < η := lt_min hηa hηp
  have hsuba : ball (0 : Coeff 2) η ⊆ ball 0 ηa := ball_subset_ball (min_le_left _ _)
  have hsubp : ball (0 : Coeff 2) η ⊆ ball 0 ηp := ball_subset_ball (min_le_right _ _)
  refine ⟨η,hη,(min_le_left _ _).trans hηa1,?_⟩
  intro k
  refine ⟨fun p hp => (ha k p (hsuba hp)).1,fun p hp => (ha k p (hsuba hp)).2,?_⟩
  intro p hp
  obtain ⟨hb,a,ha,b,hb',_,_,hm⟩ := hpairs k p (hsubp hp)
  obtain ⟨hc,hRlo,hRhi⟩ := hillFreeGap_energy_radius_geometry h0q h0r k
  let R := hillRealGapHalfLength 0 h0q h0r (k : ℕ)+hillRealGapCollar 0 h0q h0r (k : ℕ)
  have hR : 0 < R := lt_of_lt_of_le (by positivity : (0 : ℝ) < k) hRlo
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
  obtain ⟨hM,hS⟩ := hillLocalGapSymmetricData_eq_of_pair 0 h0q h0r (k : ℕ) k.property p hb haOld hbOld hm
  rw [hM,hS]
  exact ⟨norm_two_root_midpoint_sub_le a b _ haSmall hbSmall,
    norm_two_root_halfGap_sqrt_le a b _ (by positivity) haSmall hbSmall⟩

end NLS.KdV
