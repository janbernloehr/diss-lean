import NLS.KdV.HillMiuraGroundLabels
import NLS.KdV.HillHminusOriginalLabels
import NLS.KdV.HillRealGapIntegrals
import NLS.ZakharovShabat.SourceRealHigherActionIntegral

/-! # Original Hill actions at the actual normalized critical Miura factor

The literal real arcosh profiles agree under E=x squared minus the actual
factor energy. The proved complete label comparison and a real change of
variables identify every original positive Hill action, including closed
gaps, with twice the original first weighted Dirac action. No exterior
energy, local Miura inverse, or continued-sheet choice is needed.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.KdV

theorem hillOriginal_labels_ground_miura_pair (q : RealPeriodOneHillPotential)
    (u : PeriodOneRealL2) (e : ℝ) (hm : u.val 0 = 0)
    (hi : periodOneMiura u.val = hillOriginalHminusSource q.val+
      periodOneL2Inclusion (lp.single 2 0 (e : ℂ))) (n : ℕ) (hn : 0 < n) :
    hillRealLabels q.val q.property.1 q.property.2 (2*n-1) = (hillMiuraDiracLeft u.val n).re^2-e ∧
    hillRealLabels q.val q.property.1 q.property.2 (2*n) = (hillMiuraDiracRight u.val n).re^2-e := by
  have h := hillHminusLabels_pair_eq_squared_miuraDirac_of_meanZero
    (hillOriginalHminusSource q.val) (hillOriginalHminusSource_real q.val q.property.2) u e hi hm n hn
  rwa [hillHminusRealLabels_original_source q] at h

/-- Literal equality of the original arcosh profiles at every real frequency. -/
theorem hillOriginal_profile_eq_ground_miura (q : RealPeriodOneHillPotential)
    (u : PeriodOneRealL2) (e : ℝ)
    (hi : periodOneMiura u.val = hillOriginalHminusSource q.val+
      periodOneL2Inclusion (lp.single 2 0 (e : ℂ))) (n : ℕ) (x : ℝ) :
    hillRealGapProfile (SpectralWeight.one.toCoeff q.val) n (x^2-e) =
      sourceRealGapArcoshProfile (by simp) (hillMiuraDiagonal u.val) n x := by
  have ht : hillL2Discriminant (SpectralWeight.one.toCoeff q.val) ((x^2-e : ℝ) : ℂ) =
      canonicalDiscriminant (by simp) (periodOnePotential (hillMiuraDiagonal u.val)) (x : ℂ) := by
    rw [ofReal_sub,ofReal_pow,←hillHminusDiscriminant_original_source_agreement q.val q.property.1,
      hillHminusDiscriminant_shifted_miura_square _ u.val (e : ℂ) (x : ℂ) hi]
  simp only [hillRealGapProfile,sourceRealGapArcoshProfile,realGapHalfDiscriminant]
  rw [ht,neg_one_pow_eq_pow_mod_two]
  by_cases hn : n % 2 = 0
  · have hnZ : (n : ℤ) % 2 = 0 := by omega
    simp only [hn,hnZ,pow_zero,one_mul,ite_true]
  · have hn1 : n % 2 = 1 := by omega
    have hnZ : ¬(n : ℤ) % 2 = 0 := by omega
    simp only [hn1,pow_one,neg_one_mul,if_neg hnZ]

/-- The ORIGINAL physical Hill action equals twice the ORIGINAL first
weighted Dirac action at EVERY normalized real factor and EVERY positive
index, including the first and collapsed gaps. -/
theorem hillOriginal_action_eq_twice_ground_Dirac (q : RealPeriodOneHillPotential)
    (u : PeriodOneRealL2) (e : ℝ) (hm : u.val 0 = 0)
    (hi : periodOneMiura u.val = hillOriginalHminusSource q.val+
      periodOneL2Inclusion (lp.single 2 0 (e : ℂ))) (n : ℕ) (hn : 0 < n) :
    hillRealGapIntegral q.val q.property.1 q.property.2 n 0 =
      2*sourceRealHigherAction (by simp) (by norm_num) (hillMiuraRealSource u) n 1 := by
  let a := (hillMiuraDiracLeft u.val n).re
  let b := (hillMiuraDiracRight u.val n).re
  let f : ℝ → ℝ := fun x => x^2-e
  let g : ℝ → ℝ := hillRealGapProfile (SpectralWeight.one.toCoeff q.val) n
  obtain ⟨hL,hR⟩ := hillOriginal_labels_ground_miura_pair q u e hm hi n hn
  have hab : a ≤ b := hillMiuraDiracPair_ordered u.val n
  have ha : 0 < a := hillMiura_positive_gap_left_pos u (n : ℤ) (by exact_mod_cast hn)
  have hdf : ∀ x ∈ uIcc a b, HasDerivAt f (2*x) x := by
    intro x _hx
    simpa only [Pi.pow_apply,id_eq,Nat.reduceSub,pow_one,mul_one] using! ((hasDerivAt_id x).pow 2).sub_const e
  have hg : ContinuousOn g (f '' uIcc a b) := by
    apply (continuousOn_hillRealGapProfile q.val q.property.1 q.property.2 n (by omega)).mono
    rintro _ ⟨x,hx,rfl⟩
    rw [uIcc_of_le hab] at hx
    rw [hL,hR]
    change a^2-e ≤ x^2-e ∧ x^2-e ≤ b^2-e
    constructor <;> nlinarith [hx.1,hx.2]
  have hsub := intervalIntegral.integral_comp_mul_deriv' hdf (by fun_prop) hg
  have heq : (∫ x in a..b, (g ∘ f) x*(2*x)) =
      2*∫ x in a..b, x*sourceRealGapArcoshProfile (by simp) (hillMiuraDiagonal u.val) n x := by
    rw [←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _hx
    dsimp only [Function.comp_def,g,f]
    rw [hillOriginal_profile_eq_ground_miura q u e hi n x]
    ring
  rw [heq] at hsub
  rw [hillRealGapIntegral]
  simp only [pow_zero,one_mul]
  rw [hL,hR,←hsub,sourceRealHigherAction_eq_gapIntegral]
  simp only [pow_one]
  change (2/Real.pi)*(2*∫ x in a..b,
      x*sourceRealGapArcoshProfile (by simp) (hillMiuraDiagonal u.val) n x) =
    2*((2/Real.pi)*∫ x in a..b,
      x*sourceRealGapArcoshProfile (by simp) (hillMiuraDiagonal u.val) n x)
  ring

end NLS.KdV
