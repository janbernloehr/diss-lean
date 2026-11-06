import NLS.KdV.HillSummedMomentComparison
import NLS.KdV.HillSobolevHierarchyTrace
import NLS.KdV.HillHamiltonianCoercivity

/-! # Uniform global integer action/moment comparisons with the quadratic trace controlling all cutoff errors. -/

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.Fourier NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.KdV
theorem tsum_hillNativeBaseActions_eq_half_norm (M : ℕ)
    (p : RealHillWeightedPotential (hillIntegerWeight M)) (hmean : p.val.val 0 = 0) :
    let q := hillPeriodOneUnitPotential (hillIntegerWeight M) p.val
    let hq := hillPeriodOneUnitPotential_even (hillIntegerWeight M) p.val
    let hr := hillPeriodOneUnitPotential_real (hillIntegerWeight M) p.val p.property
    (∑' n, hillGapActionTerm q hq hr 0 n) = (1/2 : ℝ)*‖q‖^2 := by
  dsimp only
  let a := hillNativeIntegerToScalar M p.val
  let b := hillScalarSobolevLower M 0 (Nat.zero_le M) a
  let p0 := hillScalarToNativeInteger 0 b
  have hb (k : ℤ) : b.val k = p.val.val k := by
    simp only [b,a,hillScalarSobolevLower_apply,hillNativeIntegerToScalar_apply]
  have hrb : ∀ k, b.val (-k) = conj (b.val k) := by
    intro k
    have h := p.property k
    simpa only [hb, SpectralWeight.toCoeff_apply] using h
  have hr0 := isReal_hillScalarToNativeInteger 0 b hrb
  have hzero : p0.val 0 = 0 := by
    rw [hillScalarToNativeInteger_apply, hb, hmean]
  have hpot : hillPeriodOneUnitPotential (hillIntegerWeight 0) p0 =
      hillPeriodOneUnitPotential (hillIntegerWeight M) p.val := by
    apply hillPeriodOneUnitPotential_eq_of_coeff_eq
    intro k
    rw [hillScalarToNativeInteger_apply, hb]
  have hterm (n : ℕ) : hillHierarchyMomentTerm (hillIntegerWeight 0) ⟨p0,hr0⟩ 0 n =
      hillGapActionTerm (hillPeriodOneUnitPotential (hillIntegerWeight M) p.val)
        (hillPeriodOneUnitPotential_even (hillIntegerWeight M) p.val)
        (hillPeriodOneUnitPotential_real (hillIntegerWeight M) p.val p.property) 0 n := by
    unfold hillHierarchyMomentTerm hillGapActionTerm
    simp only [mul_zero, zero_add, pow_one]
    rw [hillRealGapIntegral_congr
      (hillPeriodOneUnitPotential (hillIntegerWeight 0) p0)
      (hillPeriodOneUnitPotential (hillIntegerWeight M) p.val)
      (hillPeriodOneUnitPotential_even (hillIntegerWeight 0) p0)
      (hillPeriodOneUnitPotential_even (hillIntegerWeight M) p.val)
      (hillPeriodOneUnitPotential_real (hillIntegerWeight 0) p0 hr0)
      (hillPeriodOneUnitPotential_real (hillIntegerWeight M) p.val p.property) hpot n 0]
  have ht := tsum_hillHierarchyMomentTerm_hierarchy_sobolev 0 ⟨p0,hr0⟩ hzero
  rw [funext hterm] at ht
  have hJ : hierarchySobolevJetL2 0 0 le_rfl b =
      WeightedCoeff.sobolevToL2 (Nat.cast_nonneg M) a := by
    ext k
    simp only [hierarchySobolevJetL2_apply, pow_zero, one_mul,
      WeightedCoeff.sobolevToL2_apply, b, hillScalarSobolevLower_apply]
  have hR : hillNativeHierarchyTraceValue 0 p0 =
      (1/2 : ℂ)*(‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg M) a‖^2 : ℝ) := by
    simp only [hillNativeHierarchyTraceValue, p0, hillNativeIntegerToScalar_scalarToNativeInteger,
      hillSobolevTraceValue, hillHierarchyTraceCoefficient_zero,
      hillSobolevHamiltonianFamily, dif_pos le_rfl, hillSobolevHamiltonianAt,
      hillScalarSobolevLower_self]
    rw [hillSobolevKinetic_real 0 b hrb, hJ]
    simp
  rw [hR] at ht
  have h := congrArg Complex.re ht
  simp only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im] at h
  norm_num at h
  rw [norm_hillPeriodOneUnitPotential_eq_sharedL2]
  exact h


theorem hillRealLabelCutoff_sq_le_baseAction_mass (M : ℕ)
    (p : RealHillWeightedPotential (hillIntegerWeight M)) (hmean : p.val.val 0 = 0) :
    let q := hillPeriodOneUnitPotential (hillIntegerWeight M) p.val
    let hq := hillPeriodOneUnitPotential_even (hillIntegerWeight M) p.val
    let hr := hillPeriodOneUnitPotential_real (hillIntegerWeight M) p.val p.property
    (hillRealLabelCutoff q : ℝ)^2 ≤ 256*(1+∑' n, hillGapActionTerm q hq hr 0 n) := by
  dsimp only
  rw [tsum_hillNativeBaseActions_eq_half_norm M p hmean]
  let q := hillPeriodOneUnitPotential (hillIntegerWeight M) p.val
  have hN := hillRealLabelCutoff_le_norm q
  have hs := pow_le_pow_left₀ (Nat.cast_nonneg (hillRealLabelCutoff q)) hN 2
  have hnorm := norm_nonneg q
  nlinarith [sq_nonneg (‖q‖-1)]


theorem exists_hillNativeGlobalMomentComparisons_uniform (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, m ≤ M →
      ∀ p : RealHillWeightedPotential (hillIntegerWeight M), p.val.val 0 = 0 →
      let q := hillPeriodOneUnitPotential (hillIntegerWeight M) p.val
      let hq := hillPeriodOneUnitPotential_even (hillIntegerWeight M) p.val
      let hr := hillPeriodOneUnitPotential_real (hillIntegerWeight M) p.val p.property
      let A := fun j => ∑' n, hillGapActionTerm q hq hr j n
      let T := fun j => ∑' n, hillGapMomentTerm q hq hr j n
      (A m ≤ (2*Real.pi)^(2*m)*T m+C*(1+A 0)^m*A 0) ∧
      ((∑' n, |hillGapMomentTerm q hq hr m n|) ≤ (Real.pi^2+1)^m*A m+C*(1+A 0)^m*A 0) := by
  let K : ℝ := (2*Real.pi)^(2*m)
  let L : ℝ := (1024*Real.pi^2)^m
  let D : ℝ := (256*(Real.pi^2+1))^m
  let C := L+K*D+D
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro M hm p hmean
  dsimp only
  let q := hillPeriodOneUnitPotential (hillIntegerWeight M) p.val
  let hq := hillPeriodOneUnitPotential_even (hillIntegerWeight M) p.val
  let hr := hillPeriodOneUnitPotential_real (hillIntegerWeight M) p.val p.property
  let A := fun j => ∑' n, hillGapActionTerm q hq hr j n
  let T := fun j => ∑' n, hillGapMomentTerm q hq hr j n
  let N := hillRealLabelCutoff q
  have hA : 0 ≤ A 0 := tsum_nonneg (hillGapActionTerm_nonneg q hq hr 0)
  have hP : 0 ≤ (1+A 0)^m := by positivity
  have hN : (N : ℝ)^2 ≤ 256*(1+A 0) := hillRealLabelCutoff_sq_le_baseAction_mass M p hmean
  have hDcut : ((Real.pi^2+1)*(N : ℝ)^2)^m ≤ D*(1+A 0)^m := by
    calc
      _ ≤ ((Real.pi^2+1)*(256*(1+A 0)))^m :=
        pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hN (by positivity)) _
      _ = _ := by dsimp [D]; simp only [mul_pow]; ring
  have hLcut : (2*Real.pi*(N : ℝ))^(2*m) ≤ L*(1+A 0)^m := by
    have hb : (2*Real.pi*(N : ℝ))^2 ≤ (1024*Real.pi^2)*(1+A 0) := by
      have h := mul_le_mul_of_nonneg_left hN (show 0 ≤ 4*Real.pi^2 by positivity)
      nlinarith
    calc
      _ = ((2*Real.pi*(N : ℝ))^2)^m := pow_mul _ 2 m
      _ ≤ ((1024*Real.pi^2)*(1+A 0))^m := pow_le_pow_left₀ (sq_nonneg _) hb _
      _ = _ := by rw [mul_pow]
  have hDle : D ≤ C := by dsimp [C]; nlinarith [mul_nonneg hK hD]
  have hDfinal : ((Real.pi^2+1)*(N : ℝ)^2)^m ≤ C*(1+A 0)^m :=
    hDcut.trans (mul_le_mul_of_nonneg_right hDle hP)
  have hEfinal : (2*Real.pi*(N : ℝ))^(2*m)+K*((Real.pi^2+1)*(N : ℝ)^2)^m ≤ C*(1+A 0)^m := by
    have h := mul_le_mul_of_nonneg_left hDcut hK
    dsimp only [C]
    nlinarith [mul_nonneg hD hP]
  have hc := hillNativeGlobalMomentComparisons M m hm p
  have hc1 : A m ≤ K*T m+((2*Real.pi*(N : ℝ))^(2*m)+K*((Real.pi^2+1)*(N : ℝ)^2)^m)*A 0 := hc.1
  have hc2 : (∑' n, |hillGapMomentTerm q hq hr m n|) ≤
      (Real.pi^2+1)^m*A m+((Real.pi^2+1)*(N : ℝ)^2)^m*A 0 := hc.2
  refine ⟨hc1.trans ?_,hc2.trans ?_⟩
  · exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hEfinal hA)
  · exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hDfinal hA)


end NLS.KdV
