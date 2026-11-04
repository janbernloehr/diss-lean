import NLS.KdV.HillHminusOneOriginalContourBands
import NLS.ZakharovShabat.EvenPositivePeriodCircle

/-! # Actual real energy bands of the canonical rough Hill root

The even source has nonnegative right endpoints at nonnegative indices.
Positive squared-frequency order identifies the real energy bands and
proves their membership in the actual canonical energy-root domain.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ComplexOrder
namespace NLS.KdV

/-- The actual canonical real energy band after a nonnegative frequency gap. -/
def hillHminusCanonicalEnergyBand (C : HillHminusMiuraChart) (q : PeriodOneHminusOne) (n : ℤ) : Set ℝ :=
  Ioo ((canonicalPeriodicRight (by simp) (by norm_num) (periodOnePotential (C.criticalSource q))
    (periodOnePotential_mem _) n).re^2-C.energyShift.re)
    ((canonicalPeriodicLeft (by simp) (by norm_num) (periodOnePotential (C.criticalSource q))
    (periodOnePotential_mem _) (n+1)).re^2-C.energyShift.re)

/-- Every nonnegative-index canonical right frequency endpoint is nonnegative for the even Miura trace. -/
theorem hillHminusCanonicalPeriodicRight_re_nonneg (C : HillHminusMiuraChart) (q : PeriodOneHminusOne)
    (n : ℤ) (hn : 0 ≤ n) :
    0 ≤ (canonicalPeriodicRight (by simp) (by norm_num) (periodOnePotential (C.criticalSource q))
      (periodOnePotential_mem _) n).re := by
  have hz := zero_mem_sourcePeriodicSegment_of_discriminant_even (by simp) (by norm_num)
    (C.criticalSource q) (hillMiuraFrequencyTrace_even (C.lift q))
  have h0 := (sourcePeriodicSegment_re_mem_Icc (by simp) (by norm_num) (C.criticalSource q) 0 0 hz).2
  simp only [zero_re] at h0
  by_cases he : n = 0
  · simpa only [he] using h0
  have hnpos : 0 < n := lt_of_le_of_ne hn (Ne.symm he)
  have hspec := canonicalPeriodicEndpoints_spec (by simp) (by norm_num)
    (periodOnePotential (C.criticalSource q)) (periodOnePotential_mem _)
  exact h0.trans ((re_le_of_complexLexLE (hspec.2.2 0 n hnpos)).trans
    (re_le_of_complexLexLE (hspec.2.1 n)))

/-- Every real energy in an actual canonical band belongs to the canonical energy-root domain. -/
theorem hillHminusCanonicalEnergyBand_mem_energyRootDomain (C : HillHminusMiuraChart) (q : PeriodOneHminusOne)
    (hr : IsRealType (CoeffPair.toMax 2 (C.criticalSource q))) (hc : C.energyShift.im = 0)
    (n : ℤ) (hn : 0 ≤ n) (energy : ℂ) (hi : energy.im = 0)
    (he : energy.re ∈ hillHminusCanonicalEnergyBand C q n) : energy ∈ C.energyRootDomain q := by
  let r := (canonicalPeriodicRight (by simp) (by norm_num) (periodOnePotential (C.criticalSource q))
    (periodOnePotential_mem _) n).re
  let l := (canonicalPeriodicLeft (by simp) (by norm_num) (periodOnePotential (C.criticalSource q))
    (periodOnePotential_mem _) (n+1)).re
  have hr0 : 0 ≤ r := hillHminusCanonicalPeriodicRight_re_nonneg C q n hn
  have hrl : r < l := canonicalPeriodicRight_re_lt_next_left (by simp) (by norm_num)
    (periodOnePotential (C.criticalSource q)) (periodOnePotential_mem _)
    (isRealType_periodOnePotential _ hr) n
  have he' : r^2-C.energyShift.re < energy.re ∧ energy.re < l^2-C.energyShift.re := he
  have hp : 0 < energy.re+C.energyShift.re := by nlinarith [sq_nonneg r]
  have hsum : energy+C.energyShift = ((energy.re+C.energyShift.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [hi,hc]
  have hsqrt : sqrt (energy+C.energyShift) = (Real.sqrt (energy.re+C.energyShift.re) : ℂ) := by
    rw [hsum,Complex.sqrt_of_nonneg (by exact_mod_cast hp.le)]
    rfl
  have hxp : 0 < Real.sqrt (energy.re+C.energyShift.re) := Real.sqrt_pos.mpr hp
  have hxs := Real.sq_sqrt hp.le
  have hx : Real.sqrt (energy.re+C.energyShift.re) ∈ sourceRealBand (by simp) (by norm_num)
      (C.criticalSource q) n := by
    change r < _ ∧ _ < l
    constructor <;> nlinarith
  refine ⟨Or.inl (by simpa only [add_re] using hp),?_⟩
  rw [hsqrt]
  exact sourceRealBand_subset_rootDomain (by simp) (by norm_num) (C.criticalSource q) hr n _ hx

/-- Squaring maps a nonnegative-index real source band into its actual energy band. -/
theorem hillHminus_sourceBand_square_mem_energyBand (C : HillHminusMiuraChart) (q : PeriodOneHminusOne)
    (n : ℤ) (hn : 0 ≤ n) (x : ℝ)
    (hx : x ∈ sourceRealBand (by simp) (by norm_num) (C.criticalSource q) n) :
    x^2-C.energyShift.re ∈ hillHminusCanonicalEnergyBand C q n := by
  have hr0 := hillHminusCanonicalPeriodicRight_re_nonneg C q n hn
  change _ < x ∧ x < _ at hx
  change _ < x^2-C.energyShift.re ∧ x^2-C.energyShift.re < _
  constructor <;> nlinarith

/-- A shifted-square-root crossing in a source band gives the corresponding original energy-band membership. -/
theorem hillHminus_shifted_sourceBand_mem_energyBand (C : HillHminusMiuraChart) (q : PeriodOneHminusOne)
    (hr : IsRealType (CoeffPair.toMax 2 (C.criticalSource q)))
    (hcpos : 0 < C.energyShift.re) (hc : C.energyShift.im = 0)
    (n : ℤ) (hn : 0 ≤ n) (x : ℝ)
    (hx : (sqrt (((x^2 : ℝ) : ℂ)+C.energyShift)).re ∈
      sourceRealBand (by simp) (by norm_num) (C.criticalSource q) n) :
    x^2 ∈ hillHminusCanonicalEnergyBand C q n := by
  have horder := hillHminus_shifted_frequency_order C q hr hcpos hc x 1
  have hs := congrArg Complex.re (sq_sqrt (((x^2 : ℝ) : ℂ)+C.energyShift))
  rw [pow_two (sqrt (((x^2 : ℝ) : ℂ)+C.energyShift))] at hs
  simp only [mul_re,add_re,ofReal_re] at hs
  rw [horder.2.1,mul_zero,sub_zero] at hs
  have hband := hillHminus_sourceBand_square_mem_energyBand C q n hn _ hx
  have he : (sqrt (((x^2 : ℝ) : ℂ)+C.energyShift)).re^2-C.energyShift.re = x^2 := by
    nlinarith
  rwa [he] at hband

end NLS.KdV
