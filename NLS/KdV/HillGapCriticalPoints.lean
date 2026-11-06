import NLS.KdV.HillEnergyPolynomialLimits
import NLS.ComplexAnalysis.RealAxisCalculus
import NLS.KdV.HillRealTraceParity

/-! # Reality, existence, strict order and explicit localization of selected Hill gap critical points, including closed gaps. -/

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
open NLS.ZakharovShabat NLS.ComplexAnalysis
namespace NLS.KdV
theorem hillL2Discriminant_critical_im_eq_zero
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (z : ℂ)
    (hz : deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q)) z = 0) : z.im = 0 := by
  by_contra hi
  apply deriv_hillL2Radicand_ne_zero_of_im_ne_zero q hq hr z hi
  have hd := (analyticOnNhd_hillL2Discriminant (SpectralWeight.one.toCoeff q) z (mem_univ z)).differentiableAt
  change deriv (fun w => hillL2Discriminant (SpectralWeight.one.toCoeff q) w ^ 2-4) z = 0
  rw [deriv_sub_const,deriv_fun_pow hd,hz]
  simp only [mul_zero]


theorem exists_hillL2Discriminant_critical_in_open_gap
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n)
    (hopen : hillRealLabels q hq hr (2*n-1) < hillRealLabels q hq hr (2*n)) :
    ∃ x ∈ Ioo (hillRealLabels q hq hr (2*n-1)) (hillRealLabels q hq hr (2*n)),
      deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q)) (x : ℂ) = 0 := by
  obtain ⟨hl,hu⟩ := hillRealLabels_pair_trace q hq hr n hn
  exact exists_deriv_eq_zero_between_real (hillL2Discriminant (SpectralWeight.one.toCoeff q))
    (fun z => (analyticOnNhd_hillL2Discriminant (SpectralWeight.one.toCoeff q) z (mem_univ z)).differentiableAt)
    (hillL2Discriminant_real _ hr) hopen (hl.trans hu.symm)


theorem hillEnergyLabel_closed_gap_multiplicity_ge_two
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n)
    (hc : hillRealLabels q hq hr (2*n-1) = hillRealLabels q hq hr (2*n)) :
    2 ≤ analyticOrderNatAt (hillL2Radicand (SpectralWeight.one.toCoeff q))
      (hillRealLabels q hq hr (2*n-1) : ℂ) := by
  classical
  let x := hillRealLabels q hq hr (2*n-1)
  let f : ℕ → ℕ := fun j => if hillRealLabels q hq hr j = x then 1 else 0
  have hmem : ({2*n-1,2*n} : Finset ℕ) ⊆ Finset.range (2*n+1) := by
    intro j hj
    rcases (by simpa only [Finset.mem_insert,Finset.mem_singleton] using hj : j = 2*n-1 ∨ j = 2*n) with rfl | rfl <;>
      simp only [Finset.mem_range] <;> omega
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg (f := f) hmem (fun _ _ _ => Nat.zero_le _)
  have htwo : 2 ≤ ∑ j ∈ Finset.range (2*n+1), f j := by
    simpa only [Finset.sum_pair (by omega : 2*n-1 ≠ 2*n),f,x,if_pos rfl,if_pos hc.symm,
      if_true,Nat.reduceAdd] using hsum
  have hfull := hillEnergy_occurrence_sum_le_full q hq hr n x
  change (∑ j ∈ Finset.range (2*n+1), f j) ≤ ∑ᶠ j : ℕ, f j at hfull
  have h := htwo.trans hfull
  simpa only [f,(hillRealLabels_global_multiplicity q hq hr x).2] using h

theorem hillL2Discriminant_critical_of_closed_gap
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n)
    (hc : hillRealLabels q hq hr (2*n-1) = hillRealLabels q hq hr (2*n)) :
    deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q)) (hillRealLabels q hq hr (2*n-1) : ℂ) = 0 := by
  let x := (hillRealLabels q hq hr (2*n-1) : ℂ)
  have hroot : hillL2Radicand (SpectralWeight.one.toCoeff q) x = 0 := (hillRealLabels_spec q hq hr).root _
  have htwo := hillEnergyLabel_closed_gap_multiplicity_ge_two q hq hr n hn hc
  have hR' : deriv (hillL2Radicand (SpectralWeight.one.toCoeff q)) x = 0 := by
    by_contra hne
    have horder := (analyticOnNhd_hillL2Radicand (SpectralWeight.one.toCoeff q) x (mem_univ x)).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hroot hne
    have hone : analyticOrderNatAt (hillL2Radicand (SpectralWeight.one.toCoeff q)) x = 1 := by
      unfold analyticOrderNatAt
      rw [horder]
      rfl
    change 2 ≤ analyticOrderNatAt (hillL2Radicand (SpectralWeight.one.toCoeff q)) x at htwo
    omega
  have htrace := (hillRealLabels_pair_trace q hq hr n hn).1
  have hD : hillL2Discriminant (SpectralWeight.one.toCoeff q) x ≠ 0 := by
    rw [htrace]
    exact mul_ne_zero (by norm_num) (pow_ne_zero n (by norm_num))
  have hd := (analyticOnNhd_hillL2Discriminant (SpectralWeight.one.toCoeff q) x (mem_univ x)).differentiableAt
  change deriv (fun w => hillL2Discriminant (SpectralWeight.one.toCoeff q) w^2-4) x = 0 at hR'
  rw [deriv_sub_const,deriv_fun_pow hd] at hR'
  norm_num only [Nat.cast_ofNat,pow_one] at hR'
  exact (mul_eq_zero.mp hR').resolve_left (mul_ne_zero (by norm_num) hD)

theorem exists_hillL2Discriminant_critical_in_gap
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n) :
    ∃ x ∈ Icc (hillRealLabels q hq hr (2*n-1)) (hillRealLabels q hq hr (2*n)),
      deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q)) (x : ℂ) = 0 := by
  rcases (monotone_hillRealLabels q hq hr (by omega : 2*n-1 ≤ 2*n)).eq_or_lt with hc | ho
  · exact ⟨hillRealLabels q hq hr (2*n-1),⟨le_rfl,hc.le⟩,
      hillL2Discriminant_critical_of_closed_gap q hq hr n hn hc⟩
  · obtain ⟨x,hx,hcrit⟩ := exists_hillL2Discriminant_critical_in_open_gap q hq hr n hn ho
    exact ⟨x,Ioo_subset_Icc_self hx,hcrit⟩


def hillGapCriticalPoint
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) : ℝ :=
  if hn : 1 ≤ n then (exists_hillL2Discriminant_critical_in_gap q hq hr n hn).choose else 0

theorem hillGapCriticalPoint_spec
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n) :
    hillGapCriticalPoint q hq hr n ∈ Icc (hillRealLabels q hq hr (2*n-1)) (hillRealLabels q hq hr (2*n)) ∧
      deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q)) (hillGapCriticalPoint q hq hr n : ℂ) = 0 := by
  simpa only [hillGapCriticalPoint,dif_pos hn] using
    (exists_hillL2Discriminant_critical_in_gap q hq hr n hn).choose_spec

theorem hillGapCriticalPoint_strictMono_positive
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) :
    StrictMono (fun k : ℕ => hillGapCriticalPoint q hq hr (k+1)) := by
  intro i j hij
  calc
    _ ≤ hillRealLabels q hq hr (2*(i+1)) := (hillGapCriticalPoint_spec q hq hr (i+1) (by omega)).1.2
    _ < hillRealLabels q hq hr (2*(i+1)+1) := hillRealLabels_band_strict q hq hr (i+1)
    _ ≤ hillRealLabels q hq hr (2*(j+1)-1) := monotone_hillRealLabels q hq hr (by omega)
    _ ≤ _ := (hillGapCriticalPoint_spec q hq hr (j+1) (by omega)).1.1

theorem hillGapCriticalPoint_high_localization
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 2 ≤ n)
    (hcut : 8*‖q‖ ≤ (n : ℝ)) : |hillGapCriticalPoint q hq hr n-freeHillValue n| ≤ 4*‖q‖ := by
  obtain ⟨p,hl,hu⟩ := hillRealLabels_high_pair q hq hr n hn hcut
  obtain ⟨hpl,hpu⟩ := p.localization q hq n (by omega) hcut
  have hc := (hillGapCriticalPoint_spec q hq hr n (by omega)).1
  rw [hl,hu] at hc
  rcases abs_le.mp hpl with ⟨hpl0,hpl1⟩
  rcases abs_le.mp hpu with ⟨hpu0,hpu1⟩
  exact abs_le.mpr ⟨by linarith [hc.1],by linarith [hc.2]⟩

theorem hillGapCriticalPoint_sqrt_frequency_bound
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 2 ≤ n)
    (hcut : 8*‖q‖ ≤ (n : ℝ)) :
    ‖Complex.sqrt (hillGapCriticalPoint q hq hr n)-(Real.pi : ℂ)*n‖ ≤ 4*‖q‖/(Real.pi*n) := by
  have hloc := hillGapCriticalPoint_high_localization q hq hr n hn hcut
  have hc : 0 < Real.pi*(n : ℝ) := mul_pos Real.pi_pos (by exact_mod_cast (show 0 < n by omega))
  have hlo : ‖(hillGapCriticalPoint q hq hr n : ℂ)-((Real.pi*(n : ℝ) : ℝ) : ℂ)^2‖ ≤ 4*‖q‖ := by
    rw [← ofReal_pow,← ofReal_sub,norm_real,Real.norm_eq_abs]
    simpa only [freeHillValue,Int.cast_natCast,mul_pow] using hloc
  simpa only [ofReal_mul,ofReal_natCast] using norm_complexSqrt_sub_positive_le
    (hillGapCriticalPoint q hq hr n) (Real.pi*n) (4*‖q‖) hc hlo



end NLS.KdV
