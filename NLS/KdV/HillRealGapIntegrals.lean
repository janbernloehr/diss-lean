import NLS.KdV.HillRealGapSigns
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.MeanValue

/-! # Intrinsic real gap integrals of the actual Hill trace

These are the literal real integrals in source formula (7), with factor
`2/pi` and the signed arcosh profile. They are integrable at every level,
nonnegative at even levels, and strictly positive at level zero exactly
when the actual gap is open. Their identification with canonical contour
actions and the Hamiltonian trace identities remain separate obligations.
-/

noncomputable section
open Set Complex MeasureTheory
namespace NLS.KdV

def hillRealGapProfile (q : Coeff 2) (n : ℕ) (x : ℝ) : ℝ :=
  Real.arcosh (((-1 : ℝ)^n*(hillL2Discriminant q x).re)/2)

def hillRealGapIntegral
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n m : ℕ) : ℝ :=
  (2/Real.pi) * ∫ x in (hillRealLabels q hq hr (2*n-1))..(hillRealLabels q hq hr (2*n)),
    x^m*hillRealGapProfile (SpectralWeight.one.toCoeff q) n x

theorem hillRealGapProfile_nonneg
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n) (x : ℝ)
    (hx : x ∈ Icc (hillRealLabels q hq hr (2*n-1)) (hillRealLabels q hq hr (2*n))) :
    0 ≤ hillRealGapProfile (SpectralWeight.one.toCoeff q) n x := by
  apply Real.arcosh_nonneg
  have h := hillL2Discriminant_signed_gap_ge_two q hq hr n hn x hx
  linarith

theorem hillRealGapProfile_pos
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n) (x : ℝ)
    (hx : x ∈ Ioo (hillRealLabels q hq hr (2*n-1)) (hillRealLabels q hq hr (2*n))) :
    0 < hillRealGapProfile (SpectralWeight.one.toCoeff q) n x := by
  apply Real.arcosh_pos
  have h := hillL2Discriminant_signed_gap_gt_two q hq hr n hn x hx
  linarith

theorem hillRealGapProfile_endpoints
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n) :
    hillRealGapProfile (SpectralWeight.one.toCoeff q) n (hillRealLabels q hq hr (2*n-1)) = 0 ∧
      hillRealGapProfile (SpectralWeight.one.toCoeff q) n (hillRealLabels q hq hr (2*n)) = 0 := by
  dsimp only [hillRealGapProfile]
  rw [(hillRealLabels_signed_pair_trace q hq hr n hn).1,
    (hillRealLabels_signed_pair_trace q hq hr n hn).2]
  norm_num

theorem continuousOn_hillRealGapProfile
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n) :
    ContinuousOn (hillRealGapProfile (SpectralWeight.one.toCoeff q) n)
      (Icc (hillRealLabels q hq hr (2*n-1)) (hillRealLabels q hq hr (2*n))) := by
  have hD : Continuous (fun x : ℝ => hillL2Discriminant (SpectralWeight.one.toCoeff q) x) :=
    (analyticOnNhd_hillL2Discriminant _).continuous.comp Complex.continuous_ofReal
  have ha : Continuous (fun x : ℝ => ((-1 : ℝ)^n*
      (hillL2Discriminant (SpectralWeight.one.toCoeff q) x).re)/2) :=
    ((Complex.continuous_re.comp hD).const_mul _).div_const _
  apply Real.continuousOn_arcosh.comp ha.continuousOn
  intro x hx
  have h := hillL2Discriminant_signed_gap_ge_two q hq hr n hn x hx
  change (1 : ℝ) ≤ ((-1 : ℝ)^n*(hillL2Discriminant (SpectralWeight.one.toCoeff q) x).re)/2
  linarith

theorem intervalIntegrable_hillRealGapProfile_weight
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n) (m : ℕ) :
    IntervalIntegrable (fun x => x^m*hillRealGapProfile (SpectralWeight.one.toCoeff q) n x)
      volume (hillRealLabels q hq hr (2*n-1)) (hillRealLabels q hq hr (2*n)) := by
  apply ContinuousOn.intervalIntegrable_of_Icc
    (monotone_hillRealLabels q hq hr (show 2*n-1 ≤ 2*n by omega))
  exact (continuousOn_id.pow m).mul (continuousOn_hillRealGapProfile q hq hr n hn)

theorem hillRealGapIntegral_nonneg_even
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n) (m : ℕ) :
    0 ≤ hillRealGapIntegral q hq hr n (2*m) := by
  apply mul_nonneg (by positivity)
  apply intervalIntegral.integral_nonneg
    (monotone_hillRealLabels q hq hr (show 2*n-1 ≤ 2*n by omega))
  intro x hx
  exact mul_nonneg (by rw [pow_mul]; exact pow_nonneg (sq_nonneg x) m)
    (hillRealGapProfile_nonneg q hq hr n hn x hx)

theorem hillRealGapIntegral_closed
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n m : ℕ)
    (hc : hillRealLabels q hq hr (2*n-1) = hillRealLabels q hq hr (2*n)) :
    hillRealGapIntegral q hq hr n m = 0 := by
  simp only [hillRealGapIntegral,hc,intervalIntegral.integral_same,mul_zero]

theorem hillRealGapIntegral_pos_iff
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n) :
    0 < hillRealGapIntegral q hq hr n 0 ↔
      hillRealLabels q hq hr (2*n-1) < hillRealLabels q hq hr (2*n) := by
  constructor
  · intro hp
    apply lt_of_le_of_ne (monotone_hillRealLabels q hq hr (show 2*n-1 ≤ 2*n by omega))
    intro hc
    rw [hillRealGapIntegral_closed q hq hr n 0 hc] at hp
    exact lt_irrefl _ hp
  · intro hopen
    unfold hillRealGapIntegral
    simp only [pow_zero,one_mul]
    apply mul_pos (by positivity)
    apply intervalIntegral.integral_pos hopen (continuousOn_hillRealGapProfile q hq hr n hn)
    · intro x hx
      exact hillRealGapProfile_nonneg q hq hr n hn x ⟨hx.1.le,hx.2⟩
    · let c := (hillRealLabels q hq hr (2*n-1)+hillRealLabels q hq hr (2*n))/2
      have hc : c ∈ Ioo (hillRealLabels q hq hr (2*n-1)) (hillRealLabels q hq hr (2*n)) :=
        ⟨by dsimp [c]; linarith,by dsimp [c]; linarith⟩
      exact ⟨c,⟨hc.1.le,hc.2.le⟩,hillRealGapProfile_pos q hq hr n hn c hc⟩

/-- The exact mean-value relation of source formula (8), for the actual
real gap integrals, including collapsed gaps and every integer level. -/
theorem hillRealGapIntegral_mean_value
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n) (m : ℕ) :
    ∃ c ∈ Icc (hillRealLabels q hq hr (2*n-1)) (hillRealLabels q hq hr (2*n)),
      hillRealGapIntegral q hq hr n m = c^m*hillRealGapIntegral q hq hr n 0 := by
  have hle := monotone_hillRealLabels q hq hr (show 2*n-1 ≤ 2*n by omega)
  have hi : IntervalIntegrable (hillRealGapProfile (SpectralWeight.one.toCoeff q) n) volume
      (hillRealLabels q hq hr (2*n-1)) (hillRealLabels q hq hr (2*n)) := by
    simpa only [pow_zero,one_mul] using intervalIntegrable_hillRealGapProfile_weight q hq hr n hn 0
  obtain ⟨c,hc,he⟩ := exists_eq_const_mul_intervalIntegral_of_nonneg
    (f := fun x : ℝ => x^m) (continuous_id.pow m).continuousOn hi (by
      intro x hx
      rw [uIoc_of_le hle] at hx
      exact hillRealGapProfile_nonneg q hq hr n hn x ⟨hx.1.le,hx.2⟩)
  refine ⟨c,?_,?_⟩
  · simpa only [uIcc_of_le hle] using hc
  · dsimp only [hillRealGapIntegral]
    simp only [pow_zero,one_mul]
    rw [he]
    ring

theorem hillRealGapIntegral_bounds_of_nonneg_left
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n) (m : ℕ)
    (hleft : 0 ≤ hillRealLabels q hq hr (2*n-1)) :
    (hillRealLabels q hq hr (2*n-1))^m*hillRealGapIntegral q hq hr n 0 ≤
      hillRealGapIntegral q hq hr n m ∧
    hillRealGapIntegral q hq hr n m ≤
      (hillRealLabels q hq hr (2*n))^m*hillRealGapIntegral q hq hr n 0 := by
  obtain ⟨c,hc,he⟩ := hillRealGapIntegral_mean_value q hq hr n hn m
  have hI : 0 ≤ hillRealGapIntegral q hq hr n 0 := by
    simpa only [mul_zero] using hillRealGapIntegral_nonneg_even q hq hr n hn 0
  rw [he]
  exact ⟨mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hleft hc.1 m) hI,
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hleft.trans hc.1) hc.2 m) hI⟩

end NLS.KdV
