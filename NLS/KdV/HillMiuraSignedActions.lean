import NLS.KdV.MiuraPeriodicReflection
import NLS.KdV.MiuraRealSource
import NLS.ZakharovShabat.SourceRealHigherActionIntegral

/-! # Signed first-action symmetry of the actual Miura source -/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory
open scoped ENNReal
namespace NLS.KdV
open NLS.ZakharovShabat

theorem sourceRealGapArcoshProfile_miura_neg (u : Coeff 2) (n : ℤ) (x : ℝ) :
    sourceRealGapArcoshProfile (by norm_num) (hillMiuraDiagonal u) (-n) (-x) =
      sourceRealGapArcoshProfile (by norm_num) (hillMiuraDiagonal u) n x := by
  have ht := hillMiuraFrequencyTrace_even u (x : ℂ)
  change canonicalDiscriminant (by norm_num) (periodOnePotential (hillMiuraDiagonal u)) (-(x : ℂ)) =
    canonicalDiscriminant (by norm_num) (periodOnePotential (hillMiuraDiagonal u)) (x : ℂ) at ht
  unfold sourceRealGapArcoshProfile realGapHalfDiscriminant
  rw [ofReal_neg,ht]
  by_cases hn : n % 2 = 0
  · have hn' : (-n) % 2 = 0 := by omega
    simp only [if_pos hn,if_pos hn']
  · have hn' : (-n) % 2 ≠ 0 := by omega
    simp only [if_neg hn,if_neg hn']

theorem sourceRealHigherAction_miura_neg_one (u : PeriodOneRealL2) (n : ℤ) :
    sourceRealHigherAction (by norm_num) (by norm_num) (hillMiuraRealSource u) (-n) 1 =
      -sourceRealHigherAction (by norm_num) (by norm_num) (hillMiuraRealSource u) n 1 := by
  let a := (hillMiuraDiracLeft u.val n).re
  let b := (hillMiuraDiracRight u.val n).re
  let g : ℝ → ℝ := fun x => x*sourceRealGapArcoshProfile (by norm_num) (hillMiuraDiagonal u.val) n x
  have hl : (hillMiuraDiracLeft u.val (-n)).re = -b := by
    rw [(hillMiuraDiracPair_neg u.val).1 n,neg_re]
  have hr : (hillMiuraDiracRight u.val (-n)).re = -a := by
    rw [(hillMiuraDiracPair_neg u.val).2 n,neg_re]
  have he : (fun x : ℝ => x*sourceRealGapArcoshProfile (by norm_num) (hillMiuraDiagonal u.val) (-n) x) =
      (fun x => -g (-x)) := by
    funext x
    have hp := sourceRealGapArcoshProfile_miura_neg u.val n (-x)
    rw [neg_neg] at hp
    dsimp only [g]
    rw [hp]
    ring
  rw [sourceRealHigherAction_eq_gapIntegral,sourceRealHigherAction_eq_gapIntegral]
  simp only [pow_one]
  change (2/Real.pi)*(∫ x in (hillMiuraDiracLeft u.val (-n)).re..(hillMiuraDiracRight u.val (-n)).re,
    x*sourceRealGapArcoshProfile (by norm_num) (hillMiuraDiagonal u.val) (-n) x) = -((2/Real.pi)*(∫ x in a..b,g x))
  rw [hl,hr,he,intervalIntegral.integral_neg,intervalIntegral.integral_comp_neg,neg_neg,neg_neg]
  ring

end NLS.KdV
