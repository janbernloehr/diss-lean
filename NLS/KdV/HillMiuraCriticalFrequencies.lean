import NLS.KdV.HillMiuraPositiveEnumeration
import NLS.KdV.HillMiuraZeroGap

/-! # The nonnegative enumeration at a normalized Miura factor

The central zero occurs once in the one-sided frequency enumeration.
Every other slot is strictly positive, including repeated closed gaps.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal Classical
namespace NLS.KdV
open NLS.ZakharovShabat

theorem hillMiuraPositiveFrequencies_zero_of_meanZero
    (u : PeriodOneRealL2) (hm : u.val 0 = 0) :
    hillMiuraPositiveFrequencies u.val 0 = 0 := by
  rw [hillMiuraPositiveFrequencies_initial]
  change (canonicalPeriodicRight (by simp) (by norm_num)
    (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _) 0).re = 0
  rw [(hillMiura_central_endpoints_eq_zero u hm).2,zero_re]

theorem hillMiuraPositiveFrequencies_pos_of_pos
    (u : PeriodOneRealL2) (j : ℕ) (hj : 0 < j) :
    0 < hillMiuraPositiveFrequencies u.val j := by
  obtain ⟨n,hn,hslot⟩ := singletonPairedEnumeration_slot j (by omega)
  have hl := hillMiura_positive_gap_left_pos u (n : ℤ) (by exact_mod_cast hn)
  change 0 < (hillMiuraDiracLeft u.val (n : ℤ)).re at hl
  rcases hslot with rfl | rfl
  · rwa [hillMiuraPositiveFrequencies_left u.val n hn]
  · rw [hillMiuraPositiveFrequencies_right u.val n hn]
    exact hl.trans_le (hillMiuraDiracPair_ordered u.val (n : ℤ))

theorem hillMiuraPositiveFrequencies_eq_zero_iff
    (u : PeriodOneRealL2) (hm : u.val 0 = 0) (j : ℕ) :
    hillMiuraPositiveFrequencies u.val j = 0 ↔ j = 0 := by
  constructor
  · intro h
    by_contra hj
    exact (hillMiuraPositiveFrequencies_pos_of_pos u j (by omega)).ne' h
  · rintro rfl
    exact hillMiuraPositiveFrequencies_zero_of_meanZero u hm

theorem hillMiuraPositiveFrequencies_zero_count
    (u : PeriodOneRealL2) (hm : u.val 0 = 0) :
    (∑ᶠ j : ℕ, if hillMiuraPositiveFrequencies u.val j = 0 then (1 : ℕ) else 0) = 1 := by
  simp only [hillMiuraPositiveFrequencies_eq_zero_iff u hm]
  rw [finsum_eq_single _ 0]
  · simp
  · intro j hj
    simp only [if_neg hj]

end NLS.KdV
