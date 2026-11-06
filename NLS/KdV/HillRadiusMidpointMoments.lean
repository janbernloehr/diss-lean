import NLS.KdV.HillAllDirichletCharts
import NLS.KdV.HillLocalFilledGapRoot

/-! # The literal symmetric midpoint from the radius-k logarithmic moments -/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillFreeGap_all_radius_moment_identification :
    ∃ η : ℝ, 0 < η ∧ ∀ k : ℕ+, ∀ p ∈ ball (0 : Coeff 2) η,
      (∀ E ∈ sphere (freeHillEnergy k) (k : ℝ), hillL2Radicand p E ≠ 0) →
      logarithmicCircleMoment (fun t : ℂ × Coeff 2 => hillL2Radicand t.2 t.1)
        (freeHillEnergy k) (k : ℝ) 0 p = 2 ∧
      logarithmicCircleMoment (fun t : ℂ × Coeff 2 => hillL2Radicand t.2 t.1)
        (freeHillEnergy k) (k : ℝ) 1 p = 2*hillLocalGapMidpoint 0 h0q h0r (k : ℕ) p := by
  obtain ⟨η,hη,_,hpairs⟩ := exists_hillFreeGap_all_localized_pairs h0q h0r (1/128) (by norm_num) (by norm_num)
  refine ⟨η,hη,?_⟩
  intro k p hp hbnew
  obtain ⟨hb,a,ha,b,hb',_,_,hm⟩ := hpairs k p hp
  obtain ⟨hc,hRlo,hRhi⟩ := hillFreeGap_energy_radius_geometry h0q h0r k
  let R := hillRealGapHalfLength 0 h0q h0r (k : ℕ)+hillRealGapCollar 0 h0q h0r (k : ℕ)
  have hR : 0 < R := lt_of_lt_of_le (by positivity : (0 : ℝ) < k) hRlo
  have haOld := ball_subset_ball (show (1/128)*R ≤ R by linarith) ha
  have hbOld := ball_subset_ball (show (1/128)*R ≤ R by linarith) hb'
  have haNew : a ∈ ball (freeHillEnergy k) (k : ℝ) := by
    rw [mem_ball_iff_norm]
    have h := mem_ball_iff_norm.mp ha
    rw [hc] at h
    linarith
  have hbNew : b ∈ ball (freeHillEnergy k) (k : ℝ) := by
    rw [mem_ball_iff_norm]
    have h := mem_ball_iff_norm.mp hb'
    rw [hc] at h
    linarith
  have hmNew (E : ℂ) (hE : E ∈ closedBall (freeHillEnergy k) (k : ℝ)) :
      analyticOrderNatAt (hillL2Radicand p) E = ({a,b} : Multiset ℂ).count E := by
    apply hm
    rw [hc]
    exact closedBall_subset_closedBall hRlo hE
  have hF := (analyticOnNhd_hillL2Radicand p).mono (subset_univ (closedBall (freeHillEnergy k) (k : ℝ)))
  have h0 := logarithmicCircleMoment_eq_two_root_powers
    (fun t : ℂ × Coeff 2 => hillL2Radicand t.2 t.1) p (by positivity : (0 : ℝ) < k) 0 hF hbnew haNew hbNew hmNew
  have h1 := logarithmicCircleMoment_eq_two_root_powers
    (fun t : ℂ × Coeff 2 => hillL2Radicand t.2 t.1) p (by positivity : (0 : ℝ) < k) 1 hF hbnew haNew hbNew hmNew
  have htau := (hillLocalGapSymmetricData_eq_of_pair 0 h0q h0r (k : ℕ) k.property p hb haOld hbOld hm).1
  refine ⟨by simpa only [pow_zero,one_add_one_eq_two] using h0,?_⟩
  rw [h1,htau]
  simp only [pow_one]
  ring

end NLS.KdV
