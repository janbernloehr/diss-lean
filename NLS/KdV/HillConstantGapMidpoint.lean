import NLS.KdV.HillAllDirichletCharts
import NLS.KdV.HillRadiusQuadraticData
import NLS.KdV.HillL2ConstantShift

/-! # The actual complex constant-potential midpoint in every positive gap -/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillFreeGap_all_constant_midpoint :
    ∃ η : ℝ, 0 < η ∧ ∀ m : ℂ, ‖m‖ < η → ∀ k : ℕ+,
      hillLocalGapMidpoint 0 h0q h0r (k : ℕ) (lp.single 2 0 m) = freeHillEnergy k+m := by
  obtain ⟨ηp,hηp,_,hpairs⟩ := exists_hillFreeGap_all_localized_pairs h0q h0r (1/128) (by norm_num) (by norm_num)
  let η := min ηp (1/16)
  refine ⟨η,lt_min hηp (by norm_num),?_⟩
  intro m hm k
  have hp : lp.single 2 0 m ∈ ball (0 : Coeff 2) ηp := by
    rw [mem_ball_zero_iff,lp.norm_single (by norm_num : (0 : ENNReal) < 2)]
    exact hm.trans_le (min_le_left _ _)
  obtain ⟨hb,a,ha,b,hb',haz,hbz,horders⟩ := hpairs k _ hp
  obtain ⟨hc,hRlo,hRhi⟩ := hillFreeGap_energy_radius_geometry h0q h0r k
  let R := hillRealGapHalfLength 0 h0q h0r (k : ℕ)+hillRealGapCollar 0 h0q h0r (k : ℕ)
  have hR : 0 < R := lt_of_lt_of_le (by positivity : (0 : ℝ) < k) hRlo
  have hmle : ‖m‖ ≤ 1/16 := hm.le.trans (min_le_right _ _)
  have hroot (x : ℂ)
      (hx : x ∈ ball (hillRealGapCenter 0 h0q h0r (k : ℕ) : ℂ) ((1/128)*R))
      (hx0 : hillL2Radicand (lp.single 2 0 m) x = 0) : x = freeHillEnergy k+m := by
    have hsmall : ‖x-freeHillEnergy k‖ < (k : ℝ)/16 := by
      have h := mem_ball_iff_norm.mp hx
      rw [hc] at h
      linarith
    have hshift : x-m ∈ closedBall (hillRealGapCenter 0 h0q h0r (k : ℕ) : ℂ) R := by
      rw [hc,mem_closedBall_iff_norm]
      calc
        ‖x-m-freeHillEnergy k‖ = ‖(x-freeHillEnergy k)-m‖ := by congr 1; ring
        _ ≤ ‖x-freeHillEnergy k‖+‖m‖ := norm_sub_le _ _
        _ ≤ (k : ℝ) := by
          have hk : (1 : ℝ) ≤ k := by exact_mod_cast k.property
          linarith
        _ ≤ R := hRlo
    have ht : hillL2Discriminant (lp.single 2 0 m) x = hillL2Discriminant 0 (x-m) := by
      simpa only [zero_add,sub_add_cancel] using hillL2Discriminant_add_const (0 : Coeff 2) m (x-m)
    have hz : hillL2Radicand 0 (x-m) = 0 := by
      rw [hillL2Radicand,← ht]
      exact hx0
    have he := hillScaledFreeGapContour_zero_unique h0q h0r 1 le_rfl (k : ℕ) k.property (x-m)
      (by simpa only [one_mul] using hshift) hz
    rw [hc] at he
    linear_combination he
  have haOld := ball_subset_ball (show (1/128)*R ≤ R by linarith) ha
  have hbOld := ball_subset_ball (show (1/128)*R ≤ R by linarith) hb'
  have htau := (hillLocalGapSymmetricData_eq_of_pair 0 h0q h0r (k : ℕ) k.property _ hb haOld hbOld horders).1
  rw [htau,hroot a ha haz,hroot b hb' hbz]
  ring

end NLS.KdV
