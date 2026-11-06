import NLS.KdV.HillGlobalMomentBounds

/-! # Actual homogeneous action terms and pointwise corrected moment comparisons. -/

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.Fourier NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.KdV
def hillGapActionTerm
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (m n : ℕ) : ℝ :=
  (2*Real.pi*(n : ℝ))^(2*m+1)*hillRealGapIntegral q hq hr n 0

def hillGapMomentTerm
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (m n : ℕ) : ℝ :=
  (2*Real.pi*(n : ℝ))*hillRealGapIntegral q hq hr n m

@[simp] theorem hillGapActionTerm_zero_index
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (m : ℕ) :
    hillGapActionTerm q hq hr m 0 = 0 := by simp [hillGapActionTerm]

@[simp] theorem hillGapMomentTerm_zero_index
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (m : ℕ) :
    hillGapMomentTerm q hq hr m 0 = 0 := by simp [hillGapMomentTerm]

theorem hillGapActionTerm_nonneg
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (m n : ℕ) :
    0 ≤ hillGapActionTerm q hq hr m n := by
  by_cases hn : n = 0
  · subst n; simp
  · have hI : 0 ≤ hillRealGapIntegral q hq hr n 0 := by
      simpa only [mul_zero] using hillRealGapIntegral_nonneg_even q hq hr n (by omega) 0
    exact mul_nonneg (by positivity) hI

theorem hillGapActionTerm_factor
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (m n : ℕ) :
    hillGapActionTerm q hq hr m n =
      (2*Real.pi*(n : ℝ))^(2*m)*hillGapActionTerm q hq hr 0 n := by
  simp only [hillGapActionTerm, mul_zero, zero_add, pow_succ]
  ring

theorem hillGapActionTerm_high_le_moment
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (n : ℕ) (hn : 2 ≤ n) (hcut : 8*‖q‖ ≤ (n : ℝ)) (m : ℕ) :
    hillGapActionTerm q hq hr m n ≤ (2*Real.pi)^(2*m)*hillGapMomentTerm q hq hr m n := by
  have hlo := hillRealGapIntegral_high_power_lower q hq hr n hn hcut m
  have hI : 0 ≤ hillRealGapIntegral q hq hr n 0 := by
    simpa only [mul_zero] using hillRealGapIntegral_nonneg_even q hq hr n (by omega) 0
  have hpow : 1 ≤ (Real.pi^2-1)^m := one_le_pow₀ (by nlinarith [Real.pi_gt_three])
  have hweak : (n : ℝ)^(2*m)*hillRealGapIntegral q hq hr n 0 ≤ hillRealGapIntegral q hq hr n m :=
    (le_mul_of_one_le_left (mul_nonneg (by positivity) hI) hpow).trans (by simpa only [mul_assoc] using hlo)
  have h := mul_le_mul_of_nonneg_left hweak (show 0 ≤ (2*Real.pi)^(2*m)*(2*Real.pi*(n : ℝ)) by positivity)
  calc
    _ = ((2*Real.pi)^(2*m)*(2*Real.pi*(n : ℝ)))*
        ((n : ℝ)^(2*m)*hillRealGapIntegral q hq hr n 0) := by
      rw [hillGapActionTerm, pow_succ, mul_pow]
      ring
    _ ≤ ((2*Real.pi)^(2*m)*(2*Real.pi*(n : ℝ)))*hillRealGapIntegral q hq hr n m := h
    _ = _ := by unfold hillGapMomentTerm; ring

theorem hillGapMomentTerm_high_le_action
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (n : ℕ) (hn : 2 ≤ n) (hcut : 8*‖q‖ ≤ (n : ℝ)) (m : ℕ) :
    0 ≤ hillGapMomentTerm q hq hr m n ∧
      hillGapMomentTerm q hq hr m n ≤ (Real.pi^2+1)^m*hillGapActionTerm q hq hr m n := by
  have hI : 0 ≤ hillRealGapIntegral q hq hr n 0 := by
    simpa only [mul_zero] using hillRealGapIntegral_nonneg_even q hq hr n (by omega) 0
  have hsign := hillRealGapIntegral_high_nonneg q hq hr n hn hcut m
  have hb := hillRealGapIntegral_high_power_bound q hq hr n hn hcut m
  have hfreq : (n : ℝ)^(2*m) ≤ (2*Real.pi*(n : ℝ))^(2*m) :=
    pow_le_pow_left₀ (Nat.cast_nonneg n) (by nlinarith [Real.pi_gt_three, Nat.cast_nonneg (α := ℝ) n]) _
  refine ⟨mul_nonneg (by positivity) hsign,?_⟩
  have h := mul_le_mul_of_nonneg_left
    (hb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfreq (by positivity)) hI))
    (show 0 ≤ 2*Real.pi*(n : ℝ) by positivity)
  unfold hillGapMomentTerm
  rw [hillGapActionTerm_factor]
  simp only [hillGapActionTerm, mul_zero, zero_add, pow_one]
  simpa only [mul_assoc, mul_left_comm, mul_comm] using h

theorem hillGapMomentTerm_central_abs_bound
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (N : ℕ) (hN : 2 ≤ N) (hcut : 8*‖q‖ ≤ (N : ℝ))
    (n : ℕ) (hnN : n ≤ N) (m : ℕ) :
    |hillGapMomentTerm q hq hr m n| ≤
      ((Real.pi^2+1)*(N : ℝ)^2)^m*hillGapActionTerm q hq hr 0 n := by
  by_cases hn : n = 0
  · subst n; simp
  · have hb := hillRealGapIntegral_central_abs_bound q hq hr N hN hcut n (by omega) hnN m
    rw [hillGapMomentTerm, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2*Real.pi*(n : ℝ))]
    have h := mul_le_mul_of_nonneg_left hb (show 0 ≤ 2*Real.pi*(n : ℝ) by positivity)
    simp only [hillGapActionTerm, mul_zero, zero_add, pow_one]
    simpa only [mul_assoc, mul_left_comm, mul_comm] using h

theorem hillGapActionTerm_central_bound
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (N n : ℕ) (hnN : n ≤ N) (m : ℕ) :
    hillGapActionTerm q hq hr m n ≤ (2*Real.pi*(N : ℝ))^(2*m)*hillGapActionTerm q hq hr 0 n := by
  rw [hillGapActionTerm_factor]
  apply mul_le_mul_of_nonneg_right _ (hillGapActionTerm_nonneg q hq hr 0 n)
  apply pow_le_pow_left₀ (by positivity)
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hnN) (by positivity)


theorem hillRealLabelCutoff_le_norm
    (q : WeightedCoeff SpectralWeight.one.toWeight 2) :
    (hillRealLabelCutoff q : ℝ) ≤ 8*(1+‖q‖) := by
  have hc : (⌈8*‖q‖⌉₊ : ℝ) < 8*‖q‖+1 := Nat.ceil_lt_add_one (by positivity)
  unfold hillRealLabelCutoff
  rw [Nat.cast_max]
  norm_num only [Nat.cast_ofNat]
  exact max_le (by nlinarith [norm_nonneg q]) (by linarith)

theorem hillGapActionTerm_global_corrected
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (m n : ℕ) :
    let N := hillRealLabelCutoff q
    hillGapActionTerm q hq hr m n ≤ (2*Real.pi)^(2*m)*hillGapMomentTerm q hq hr m n+
      ((2*Real.pi*(N : ℝ))^(2*m)+(2*Real.pi)^(2*m)*((Real.pi^2+1)*(N : ℝ)^2)^m)*
        hillGapActionTerm q hq hr 0 n := by
  dsimp only
  let N := hillRealLabelCutoff q
  have hN : 2 ≤ N := hillRealLabelCutoff_ge_two q
  have hcut : 8*‖q‖ ≤ (N : ℝ) := hillRealLabelCutoff_bound q
  have ha := hillGapActionTerm_nonneg q hq hr 0 n
  have hK : 0 ≤ (2*Real.pi)^(2*m) := by positivity
  by_cases hn : N ≤ n
  · have hh := hillGapActionTerm_high_le_moment q hq hr n (by omega)
      (hcut.trans (by exact_mod_cast hn)) m
    have he : 0 ≤ ((2*Real.pi*(N : ℝ))^(2*m)+
        (2*Real.pi)^(2*m)*((Real.pi^2+1)*(N : ℝ)^2)^m)*hillGapActionTerm q hq hr 0 n := by positivity
    linarith
  · have hA := hillGapActionTerm_central_bound q hq hr N n (by omega) m
    have hB := (abs_le.mp (hillGapMomentTerm_central_abs_bound q hq hr N hN hcut n (by omega) m)).1
    have h := mul_le_mul_of_nonneg_left hB hK
    nlinarith

theorem hillGapMomentTerm_global_abs_bound
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (m n : ℕ) :
    let N := hillRealLabelCutoff q
    |hillGapMomentTerm q hq hr m n| ≤ (Real.pi^2+1)^m*hillGapActionTerm q hq hr m n+
      ((Real.pi^2+1)*(N : ℝ)^2)^m*hillGapActionTerm q hq hr 0 n := by
  dsimp only
  let N := hillRealLabelCutoff q
  have hN : 2 ≤ N := hillRealLabelCutoff_ge_two q
  have hcut : 8*‖q‖ ≤ (N : ℝ) := hillRealLabelCutoff_bound q
  by_cases hn : N ≤ n
  · have hh := hillGapMomentTerm_high_le_action q hq hr n (by omega)
      (hcut.trans (by exact_mod_cast hn)) m
    rw [abs_of_nonneg hh.1]
    have hp : 0 ≤ ((Real.pi^2+1)*(N : ℝ)^2)^m*hillGapActionTerm q hq hr 0 n :=
      mul_nonneg (by positivity) (hillGapActionTerm_nonneg q hq hr 0 n)
    linarith [hh.2]
  · have hh := hillGapMomentTerm_central_abs_bound q hq hr N hN hcut n (by omega) m
    have hp : 0 ≤ (Real.pi^2+1)^m*hillGapActionTerm q hq hr m n :=
      mul_nonneg (by positivity) (hillGapActionTerm_nonneg q hq hr m n)
    linarith


end NLS.KdV
