import NLS.KdV.HillHilbertRootCoordinates
import NLS.KdV.HillFreeEnergySeparation

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate

namespace NLS.KdV

variable
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillAbelianHilbertRootEnergy_mem_free_contour_ball
    (a : Coeff 2) (ha : ‖a‖ < Real.pi^2/4) (m : ℕ) (hm : 1 ≤ m) :
    hillAbelianHilbertRootEnergy a m ∈ ball (hillRealGapCenter 0 hq hr m : ℂ)
      (hillRealGapHalfLength 0 hq hr m+hillRealGapCollar 0 hq hr m) := by
  rw [mem_ball,dist_eq_norm,hillFreeGapCenter hq hr m hm,
    hillFreeGapHalfLength hq hr m hm,hillFreeGapCollar hq hr m hm,zero_add]
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hb := norm_hillAbelianHilbertRootEnergy_sub_free_le a m
  have hs := mul_lt_mul_of_pos_left ha (show 0 < (m : ℝ) by positivity)
  nlinarith [sq_pos_of_pos Real.pi_pos]

theorem hillAbelianHilbertRootEnergy_not_mem_other_free_closedBall
    (a : Coeff 2) (ha : ‖a‖ < Real.pi^2/4) (m k : ℕ)
    (hm : 1 ≤ m) (hk : 1 ≤ k) (hmk : m ≠ k) :
    hillAbelianHilbertRootEnergy a m ∉ closedBall (hillRealGapCenter 0 hq hr k : ℂ)
      (hillRealGapHalfLength 0 hq hr k+hillRealGapCollar 0 hq hr k) := by
  rw [mem_closedBall,dist_eq_norm,hillFreeGapCenter hq hr k hk,
    hillFreeGapHalfLength hq hr k hk,hillFreeGapCollar hq hr k hk,zero_add]
  intro hmem
  have hsep := freeHillValue_nat_separation m k hmk
  have htri := norm_sub_le ((freeHillValue m : ℂ)-hillAbelianHilbertRootEnergy a m)
    ((freeHillValue k : ℂ)-hillAbelianHilbertRootEnergy a m)
  have he : (freeHillValue m : ℂ)-hillAbelianHilbertRootEnergy a m-
      ((freeHillValue k : ℂ)-hillAbelianHilbertRootEnergy a m) =
      (freeHillValue m : ℂ)-(freeHillValue k : ℂ) := by ring
  rw [he,norm_sub_rev (freeHillValue m : ℂ) (hillAbelianHilbertRootEnergy a m),
    norm_sub_rev (freeHillValue k : ℂ) (hillAbelianHilbertRootEnergy a m)] at htri
  have hb := norm_hillAbelianHilbertRootEnergy_sub_free_le a m
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hs := mul_lt_mul_of_pos_left ha (show 0 < (m : ℝ) by positivity)
  have hmargin : 0 < (3*(m : ℝ)+2*(k : ℝ)+1)*Real.pi^2 :=
    mul_pos (by positivity) (sq_pos_of_pos Real.pi_pos)
  nlinarith

theorem hillAbelianHilbertPsi_zero_iff_on_free_closedBall
    (a : Coeff 2) (ha : ‖a‖ < Real.pi^2/4) (n k : ℕ)
    (hn : 1 ≤ n) (hk : 1 ≤ k) (hkn : k ≠ n) (E : ℂ)
    (hE : E ∈ closedBall (hillRealGapCenter 0 hq hr k : ℂ)
      (hillRealGapHalfLength 0 hq hr k+hillRealGapCollar 0 hq hr k)) :
    hillAbelianHilbertPsi n (E,a) = 0 ↔ E = hillAbelianHilbertRootEnergy a k := by
  rw [hillAbelianHilbertPsi_zero_iff n hn E a]
  constructor
  · rintro ⟨j,_,hj⟩
    have hjE : hillAbelianHilbertRootEnergy a (j+1) = E := hj
    have hjk : j+1 = k := by
      by_contra hne
      exact hillAbelianHilbertRootEnergy_not_mem_other_free_closedBall hq hr a ha
        (j+1) k (by omega) hk hne (hjE.symm ▸ hE)
    simpa only [hjk] using hjE.symm
  · intro he
    refine ⟨k-1,by simpa only [Nat.sub_add_cancel hk] using hkn,?_⟩
    simpa only [Nat.sub_add_cancel hk,hillAbelianHilbertRootEnergy] using he.symm

theorem hillAbelianHilbertPsi_ne_zero_on_own_free_closedBall
    (a : Coeff 2) (ha : ‖a‖ < Real.pi^2/4) (n : ℕ) (hn : 1 ≤ n) (E : ℂ)
    (hE : E ∈ closedBall (hillRealGapCenter 0 hq hr n : ℂ)
      (hillRealGapHalfLength 0 hq hr n+hillRealGapCollar 0 hq hr n)) :
    hillAbelianHilbertPsi n (E,a) ≠ 0 := by
  intro hzero
  obtain ⟨j,hj,hjE⟩ := (hillAbelianHilbertPsi_zero_iff n hn E a).mp hzero
  have he : hillAbelianHilbertRootEnergy a (j+1) = E := hjE
  exact hillAbelianHilbertRootEnergy_not_mem_other_free_closedBall hq hr a ha
    (j+1) n (by omega) hn hj (he.symm ▸ hE)

theorem hillAbelianHilbertPsi_ne_zero_on_free_contour
    (a : Coeff 2) (ha : ‖a‖ < Real.pi^2/4) (n k : ℕ)
    (hn : 1 ≤ n) (hk : 1 ≤ k) (E : ℂ)
    (hE : E ∈ sphere (hillRealGapCenter 0 hq hr k : ℂ)
      (hillRealGapHalfLength 0 hq hr k+hillRealGapCollar 0 hq hr k)) :
    hillAbelianHilbertPsi n (E,a) ≠ 0 := by
  by_cases hkn : k = n
  · subst k
    exact hillAbelianHilbertPsi_ne_zero_on_own_free_closedBall hq hr a ha n hn E
      (sphere_subset_closedBall hE)
  · intro hzero
    have he := (hillAbelianHilbertPsi_zero_iff_on_free_closedBall hq hr a ha n k hn hk hkn E
      (sphere_subset_closedBall hE)).mp hzero
    exact sphere_disjoint_ball.le_bot ⟨he ▸ hE,
      hillAbelianHilbertRootEnergy_mem_free_contour_ball hq hr a ha k hk⟩

end NLS.KdV
