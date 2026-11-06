import NLS.KdV.HillHminusOneMiuraRootSymmetry
import NLS.KdV.MiuraRealSource
import NLS.ZakharovShabat.SourceRealHigherActionIntegral

/-! # Exact signed-index reflection of the actual diagonal Dirac actions -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV

theorem hillMiura_arcoshProfile_neg (u : Coeff 2) (n : ℤ) (x : ℝ) :
    sourceRealGapArcoshProfile (by simp) (hillMiuraDiagonal u) (-n) (-x) =
      sourceRealGapArcoshProfile (by simp) (hillMiuraDiagonal u) n x := by
  simp only [sourceRealGapArcoshProfile,realGapHalfDiscriminant,ofReal_neg]
  have ht := hillMiuraFrequencyTrace_even u (x : ℂ)
  change canonicalDiscriminant (by simp) (periodOnePotential (hillMiuraDiagonal u)) (-(x : ℂ)) =
    canonicalDiscriminant (by simp) (periodOnePotential (hillMiuraDiagonal u)) (x : ℂ) at ht
  rw [ht]
  have he : (-n)%2=0 ↔ n%2=0 := by omega
  simp only [he]

/-- Every original higher action has its exact reflected spectral-power
sign. In particular the first weighted action is odd in the index. -/
theorem hillMiura_realHigherAction_neg (u : PeriodOneRealL2) (n : ℤ) (k : ℕ) :
    sourceRealHigherAction (by simp) (by norm_num) (hillMiuraRealSource u) (-n) k =
      (-1 : ℝ)^k*sourceRealHigherAction (by simp) (by norm_num) (hillMiuraRealSource u) n k := by
  rw [sourceRealHigherAction_eq_gapIntegral,sourceRealHigherAction_eq_gapIntegral]
  dsimp only [hillMiuraRealSource]
  obtain ⟨hL,hR⟩ := hillMiuraCanonicalEndpoints_neg u.val n
  change canonicalPeriodicLeft _ _ _ _ (-n) = _ at hL
  rw [hL,hR,neg_re,neg_re,←intervalIntegral.integral_comp_neg]
  have he : (∫ x in
      (canonicalPeriodicLeft (by simp) (by norm_num) (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _) n).re..
      (canonicalPeriodicRight (by simp) (by norm_num) (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _) n).re,
      (-x)^k*sourceRealGapArcoshProfile (by simp) (hillMiuraDiagonal u.val) (-n) (-x)) =
      (-1 : ℝ)^k*∫ x in
      (canonicalPeriodicLeft (by simp) (by norm_num) (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _) n).re..
      (canonicalPeriodicRight (by simp) (by norm_num) (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _) n).re,
      x^k*sourceRealGapArcoshProfile (by simp) (hillMiuraDiagonal u.val) n x := by
    rw [←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _hx
    dsimp only
    rw [hillMiura_arcoshProfile_neg]
    ring
  rw [he]
  ring

end NLS.KdV
