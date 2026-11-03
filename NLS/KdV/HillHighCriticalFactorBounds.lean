import NLS.KdV.HillCriticalEnergyZeros
import NLS.ComplexAnalysis.EndpointCriticalRatioBounds
import NLS.SequenceSpaces.NaturalSquareSeparation

/-! # Explicit high-gap midpoint separation and critical-factor estimates at the norm-dependent cutoff. -/

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
open NLS.ZakharovShabat
open NLS.ComplexAnalysis
open NLS.SequenceSpaces
namespace NLS.KdV
theorem hillRealLabels_high_endpoint_bounds
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 2 ≤ n)
    (hcut : 8*‖q‖ ≤ (n : ℝ)) :
    |hillRealLabels q hq hr (2*n-1)-freeHillValue n| ≤ 4*‖q‖ ∧
    |hillRealLabels q hq hr (2*n)-freeHillValue n| ≤ 4*‖q‖ := by
  obtain ⟨p,hl,hu⟩ := hillRealLabels_high_pair q hq hr n hn hcut
  rw [hl,hu]
  exact p.localization q hq n (by omega) hcut

theorem hillRealGap_point_high_bound
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 2 ≤ n)
    (hcut : 8*‖q‖ ≤ (n : ℝ)) (x : ℝ)
    (hx : x ∈ Icc (hillRealLabels q hq hr (2*n-1)) (hillRealLabels q hq hr (2*n))) :
    |x-freeHillValue n| ≤ 4*‖q‖ := by
  obtain ⟨hl,hu⟩ := hillRealLabels_high_endpoint_bounds q hq hr n hn hcut
  rcases abs_le.mp hl with ⟨hl0,hl1⟩
  rcases abs_le.mp hu with ⟨hu0,hu1⟩
  exact abs_le.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩

def hillEnergyGapMidpoint
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) : ℝ :=
  (hillRealLabels q hq hr (2*n-1)+hillRealLabels q hq hr (2*n))/2

theorem hillEnergyGapMidpoint_mem_gap
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) :
    hillEnergyGapMidpoint q hq hr n ∈ Icc (hillRealLabels q hq hr (2*n-1)) (hillRealLabels q hq hr (2*n)) := by
  have h := monotone_hillRealLabels q hq hr (show 2*n-1 ≤ 2*n by omega)
  constructor <;> dsimp only [hillEnergyGapMidpoint] <;> linarith

theorem hillHighGap_midpoint_distance_lower
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n m : ℕ)
    (hn : 2 ≤ n) (hm : 2 ≤ m) (hcn : 8*‖q‖ ≤ (n : ℝ)) (hcm : 8*‖q‖ ≤ (m : ℝ)) (hmn : m ≠ n)
    (x : ℝ) (hx : x ∈ Icc (hillRealLabels q hq hr (2*n-1)) (hillRealLabels q hq hr (2*n))) :
    8*|(m : ℝ)^2-(n : ℝ)^2| ≤ |hillEnergyGapMidpoint q hq hr m-x| := by
  have hxloc := hillRealGap_point_high_bound q hq hr n hn hcn x hx
  have hmloc := hillRealGap_point_high_bound q hq hr m hm hcm _ (hillEnergyGapMidpoint_mem_gap q hq hr m)
  have hsep := nat_square_separation_ge_sum m n hmn
  have hD : 0 < |(m : ℝ)^2-(n : ℝ)^2| := by
    have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hfree : |freeHillValue m-freeHillValue n| = Real.pi^2*|(m : ℝ)^2-(n : ℝ)^2| := by
    rw [show freeHillValue m-freeHillValue n = Real.pi^2*((m : ℝ)^2-(n : ℝ)^2) by
      simp only [freeHillValue,Int.cast_natCast]; ring,abs_mul,abs_of_nonneg (sq_nonneg Real.pi)]
  have ht : |freeHillValue m-freeHillValue n| ≤
      4*‖q‖+|hillEnergyGapMidpoint q hq hr m-x|+4*‖q‖ := by
    calc
      _ ≤ |freeHillValue m-hillEnergyGapMidpoint q hq hr m|+|hillEnergyGapMidpoint q hq hr m-freeHillValue n| := abs_sub_le _ _ _
      _ ≤ |freeHillValue m-hillEnergyGapMidpoint q hq hr m|+(|hillEnergyGapMidpoint q hq hr m-x|+|x-freeHillValue n|) :=
        add_le_add le_rfl (abs_sub_le _ _ _)
      _ ≤ _ := by rw [abs_sub_comm (freeHillValue m)]; linarith
  rw [hfree] at ht
  have hp := mul_nonneg (show (0 : ℝ) ≤ Real.pi^2-9 by nlinarith [Real.pi_gt_three]) hD.le
  nlinarith

theorem hillHighGap_critical_root_ratio_le
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n m : ℕ)
    (hn : 2 ≤ n) (hm : 2 ≤ m) (hcn : 8*‖q‖ ≤ (n : ℝ)) (hcm : 8*‖q‖ ≤ (m : ℝ)) (hmn : m ≠ n)
    (x : ℝ) (hx : x ∈ Icc (hillRealLabels q hq hr (2*n-1)) (hillRealLabels q hq hr (2*n))) :
    ‖((hillGapCriticalPoint q hq hr m : ℂ)-(x : ℂ))/
      endpointRoot (hillRealLabels q hq hr (2*m-1)) (hillRealLabels q hq hr (2*m)) x‖ ≤
      1+(hillRealLabels q hq hr (2*m)-hillRealLabels q hq hr (2*m-1))/(4*|(m : ℝ)^2-(n : ℝ)^2|) := by
  let γ := hillRealLabels q hq hr (2*m)-hillRealLabels q hq hr (2*m-1)
  let d := |hillEnergyGapMidpoint q hq hr m-x|
  let D := |(m : ℝ)^2-(n : ℝ)^2|
  have hγ : 0 ≤ γ := sub_nonneg.mpr (monotone_hillRealLabels q hq hr (by omega : 2*m-1 ≤ 2*m))
  obtain ⟨hl,hu⟩ := hillRealLabels_high_endpoint_bounds q hq hr m hm hcm
  have hγup : γ/2 ≤ 4*‖q‖ := by
    have hl' := (abs_le.mp hl).1
    have hu' := (abs_le.mp hu).2
    dsimp only [γ]
    linarith
  have hsep := hillHighGap_midpoint_distance_lower q hq hr n m hn hm hcn hcm hmn x hx
  have hDsum := nat_square_separation_ge_sum m n hmn
  have hD : 0 < D := by
    have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    dsimp only [D]
    linarith
  have hden : 4*D ≤ d-γ/2 := by dsimp only [d,D]; linarith
  have hdpos : 0 < d-γ/2 := (mul_pos (by norm_num : (0 : ℝ) < 4) hD).trans_le hden
  have hnorm : ‖(((hillRealLabels q hq hr (2*m-1)+hillRealLabels q hq hr (2*m))/2 : ℝ) : ℂ)-(x : ℂ)‖ = d := by
    rw [← ofReal_sub,norm_real,Real.norm_eq_abs]
    rfl
  have hratio := norm_critical_endpoint_ratio_le (hillRealLabels q hq hr (2*m-1))
    (hillRealLabels q hq hr (2*m)) (hillGapCriticalPoint q hq hr m)
    (monotone_hillRealLabels q hq hr (by omega : 2*m-1 ≤ 2*m))
    (hillGapCriticalPoint_spec q hq hr m (by omega)).1 (x : ℂ)
    (by rw [hnorm]; exact sub_pos.mp hdpos)
  rw [hnorm] at hratio
  apply hratio.trans
  exact add_le_add le_rfl (div_le_div_of_nonneg_left hγ (by positivity) hden)


end NLS.KdV
