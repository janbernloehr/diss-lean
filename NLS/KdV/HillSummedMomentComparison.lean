import NLS.KdV.HillIntegerActionMoments
import NLS.KdV.HillIntegerSobolev

/-! # Complete actual action and moment series with global corrected comparisons. -/

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.Fourier NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.KdV
theorem tsum_hillGapActions_le_moments_corrected
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (m : ℕ)
    (hA : Summable (hillGapActionTerm q hq hr m))
    (hB : Summable (hillGapMomentTerm q hq hr m))
    (h0 : Summable (hillGapActionTerm q hq hr 0)) :
    let N := hillRealLabelCutoff q
    (∑' n, hillGapActionTerm q hq hr m n) ≤ (2*Real.pi)^(2*m)*(∑' n, hillGapMomentTerm q hq hr m n)+
      ((2*Real.pi*(N : ℝ))^(2*m)+(2*Real.pi)^(2*m)*((Real.pi^2+1)*(N : ℝ)^2)^m)*
        (∑' n, hillGapActionTerm q hq hr 0 n) := by
  dsimp only
  let D := (2*Real.pi*(hillRealLabelCutoff q : ℝ))^(2*m)+
    (2*Real.pi)^(2*m)*((Real.pi^2+1)*(hillRealLabelCutoff q : ℝ)^2)^m
  have hs := (hB.mul_left ((2*Real.pi)^(2*m))).add (h0.mul_left D)
  have h := hA.tsum_le_tsum (hillGapActionTerm_global_corrected q hq hr m) hs
  rw [Summable.tsum_add (hB.mul_left _) (h0.mul_left _), tsum_mul_left, tsum_mul_left] at h
  exact h

theorem tsum_abs_hillGapMoments_le_actions_corrected
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (m : ℕ)
    (hA : Summable (hillGapActionTerm q hq hr m))
    (hB : Summable (hillGapMomentTerm q hq hr m))
    (h0 : Summable (hillGapActionTerm q hq hr 0)) :
    let N := hillRealLabelCutoff q
    (∑' n, |hillGapMomentTerm q hq hr m n|) ≤ (Real.pi^2+1)^m*(∑' n, hillGapActionTerm q hq hr m n)+
      ((Real.pi^2+1)*(N : ℝ)^2)^m*(∑' n, hillGapActionTerm q hq hr 0 n) := by
  dsimp only
  have habs : Summable (fun n => |hillGapMomentTerm q hq hr m n|) := by
    simpa only [Real.norm_eq_abs] using hB.norm
  let D := ((Real.pi^2+1)*(hillRealLabelCutoff q : ℝ)^2)^m
  have hs := (hA.mul_left ((Real.pi^2+1)^m)).add (h0.mul_left D)
  have h := habs.tsum_le_tsum (hillGapMomentTerm_global_abs_bound q hq hr m) hs
  rw [Summable.tsum_add (hA.mul_left _) (h0.mul_left _), tsum_mul_left, tsum_mul_left] at h
  exact h


theorem hillGapActionTerm_native_weight_bound (w : SpectralWeight) (p : RealHillWeightedPotential w)
    (m : ℕ) (hGrowth : ∀ n : ℕ, 1 ≤ n → (n : ℝ)^m ≤ w (2*(n : ℤ))) (n : ℕ) :
    hillGapActionTerm (hillPeriodOneUnitPotential w p.val) (hillPeriodOneUnitPotential_even w p.val)
      (hillPeriodOneUnitPotential_real w p.val p.property) m n ≤
      (2*Real.pi)^(2*m)*hillWeightedActionTerm w p n := by
  by_cases hn : n = 0
  · subst n
    simp [hillWeightedActionTerm]
  · have hI := hillPeriodOneAction_nonneg w p.val p.property n (by omega)
    have hpow : (n : ℝ)^(2*m) ≤ w (2*(n : ℤ))^2 := by
      rw [Nat.mul_comm 2 m, pow_mul]
      exact pow_le_pow_left₀ (pow_nonneg (Nat.cast_nonneg n) m) (hGrowth n (by omega)) 2
    have h := mul_le_mul_of_nonneg_left hpow
      (show 0 ≤ (2*Real.pi)^(2*m)*(2*Real.pi*(n : ℝ))*hillPeriodOneAction w p.val p.property n by positivity)
    have he : hillGapActionTerm (hillPeriodOneUnitPotential w p.val)
        (hillPeriodOneUnitPotential_even w p.val) (hillPeriodOneUnitPotential_real w p.val p.property) m n =
      (2*Real.pi)^(2*m)*(n : ℝ)^(2*m)*(2*Real.pi*(n : ℝ))*hillPeriodOneAction w p.val p.property n := by
      unfold hillGapActionTerm hillPeriodOneAction
      rw [pow_succ, mul_pow]
    rw [he, hillWeightedActionTerm]
    convert! h using 1 <;> ring


theorem hillIntegerWeight_growth_of_le (M m : ℕ) (hm : m ≤ M) (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ)^m ≤ hillIntegerWeight M (2*(n : ℤ)) :=
  (pow_le_pow_right₀ (by exact_mod_cast hn) hm).trans (hillIntegerWeight_growth M n)

theorem summable_hillNativeGapActions (M m : ℕ) (hm : m ≤ M)
    (p : RealHillWeightedPotential (hillIntegerWeight M)) :
    Summable (hillGapActionTerm (hillPeriodOneUnitPotential (hillIntegerWeight M) p.val)
      (hillPeriodOneUnitPotential_even (hillIntegerWeight M) p.val)
      (hillPeriodOneUnitPotential_real (hillIntegerWeight M) p.val p.property) m) := by
  apply Summable.of_nonneg_of_le
    (fun n => hillGapActionTerm_nonneg _ _ _ m n)
    (fun n => hillGapActionTerm_native_weight_bound (hillIntegerWeight M) p m
      (fun n hn => hillIntegerWeight_growth_of_le M m hm n hn) n)
  exact (summable_hillWeightedActionTerm (hillIntegerWeight M) p).mul_left _

theorem summable_hillNativeGapMoments (M m : ℕ) (hm : m ≤ M)
    (p : RealHillWeightedPotential (hillIntegerWeight M)) :
    Summable (hillGapMomentTerm (hillPeriodOneUnitPotential (hillIntegerWeight M) p.val)
      (hillPeriodOneUnitPotential_even (hillIntegerWeight M) p.val)
      (hillPeriodOneUnitPotential_real (hillIntegerWeight M) p.val p.property) m) :=
  summable_hillHierarchyMomentTerm (hillIntegerWeight M) p m
    (fun n hn => hillIntegerWeight_growth_of_le M m hm n hn)

theorem hillNativeGlobalMomentComparisons (M m : ℕ) (hm : m ≤ M)
    (p : RealHillWeightedPotential (hillIntegerWeight M)) :
    let q := hillPeriodOneUnitPotential (hillIntegerWeight M) p.val
    let hq := hillPeriodOneUnitPotential_even (hillIntegerWeight M) p.val
    let hr := hillPeriodOneUnitPotential_real (hillIntegerWeight M) p.val p.property
    let N := hillRealLabelCutoff q
    ((∑' n, hillGapActionTerm q hq hr m n) ≤ (2*Real.pi)^(2*m)*(∑' n, hillGapMomentTerm q hq hr m n)+
      ((2*Real.pi*(N : ℝ))^(2*m)+(2*Real.pi)^(2*m)*((Real.pi^2+1)*(N : ℝ)^2)^m)*
        (∑' n, hillGapActionTerm q hq hr 0 n)) ∧
    ((∑' n, |hillGapMomentTerm q hq hr m n|) ≤ (Real.pi^2+1)^m*(∑' n, hillGapActionTerm q hq hr m n)+
      ((Real.pi^2+1)*(N : ℝ)^2)^m*(∑' n, hillGapActionTerm q hq hr 0 n)) := by
  dsimp only
  have hA := summable_hillNativeGapActions M m hm p
  have hB := summable_hillNativeGapMoments M m hm p
  have h0 := summable_hillNativeGapActions M 0 (Nat.zero_le M) p
  exact ⟨tsum_hillGapActions_le_moments_corrected _ _ _ m hA hB h0,
    tsum_abs_hillGapMoments_le_actions_corrected _ _ _ m hA hB h0⟩


theorem norm_hillPeriodOneUnitPotential_eq_toCoeff (w : SpectralWeight)
    (p : WeightedCoeff w.doubleIndex.toWeight 2) :
    ‖hillPeriodOneUnitPotential w p‖ = ‖w.doubleIndex.toCoeff p‖ := by
  rw [WeightedCoeff.norm_eq]
  have he : WeightedCoeff.weightEquiv SpectralWeight.one.toWeight 2 (hillPeriodOneUnitPotential w p) =
      SpectralWeight.one.toCoeff (hillPeriodOneUnitPotential w p) := by
    ext k
    simp only [WeightedCoeff.weightEquiv_apply,
      SpectralWeight.one_apply, Complex.ofReal_one, one_mul, SpectralWeight.toCoeff_apply]
  rw [he, toCoeff_hillPeriodOneUnitPotential, toCoeff_hillPeriodOnePotential, Coeff.periodDouble.norm_map]

theorem norm_hillPeriodOneUnitPotential_eq_sharedL2 (M : ℕ)
    (p : WeightedCoeff (hillIntegerWeight M).doubleIndex.toWeight 2) :
    ‖hillPeriodOneUnitPotential (hillIntegerWeight M) p‖ =
      ‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg M) (hillNativeIntegerToScalar M p)‖ := by
  rw [norm_hillPeriodOneUnitPotential_eq_toCoeff]
  congr 1
  ext k
  simp only [SpectralWeight.toCoeff_apply, WeightedCoeff.sobolevToL2_apply, hillNativeIntegerToScalar_apply]


end NLS.KdV
