import NLS.KdV.HillMiuraCriticalLabels
import NLS.KdV.HillHminusOneRealPeriodFormulas
import NLS.ZakharovShabat.SourceRealHigherActionIntegral

/-! # The actual Hill action at the normalized Miura factor

The literal real gap integral changes variables by E = x^2 - e.
The Jacobian gives the factor two in the first weighted Dirac action.
All real Hminus1 potentials and all positive indices are included.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory
open scoped ENNReal
namespace NLS.KdV
open NLS.ZakharovShabat

theorem hillHminusRealGapProfile_shifted_miura_square
    (q : PeriodOneHminusOne) (u : Coeff 2) (e x : ℝ)
    (hi : periodOneMiura u = q+periodOneL2Inclusion (lp.single 2 0 (e : ℂ))) (n : ℕ+) :
    hillHminusRealGapProfile q (n : ℕ) (x^2-e) =
      sourceRealGapArcoshProfile (by norm_num) (hillMiuraDiagonal u) (n : ℤ) x := by
  have ht := hillHminusDiscriminant_shifted_miura_square q u (e : ℂ) (x : ℂ) hi
  rw [←ofReal_pow,←ofReal_sub] at ht
  unfold hillHminusRealGapProfile sourceRealGapArcoshProfile realGapHalfDiscriminant
  rw [ht]
  congr 1
  split_ifs with hn
  · have he : Even (n : ℕ) := by
      exact_mod_cast Int.even_iff.mpr hn
    rw [he.neg_one_pow,one_mul]
  · have ho : Odd (n : ℕ) := Nat.not_even_iff_odd.mp (by
      intro he
      exact hn (Int.emod_eq_zero_of_dvd (by exact_mod_cast he.two_dvd)))
    rw [ho.neg_one_pow,neg_one_mul]

theorem hillHminusRealGapContourMoment_eq_twice_critical_Dirac_action
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (u : PeriodOneRealL2) (e : ℝ) (hm : u.val 0 = 0)
    (hi : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (e : ℂ)))
    (n : ℕ+) :
    hillHminusRealGapContourMoment q hr n 0 =
      ((2*sourceRealHigherAction (by norm_num) (by norm_num) (hillMiuraRealSource u) (n : ℤ) 1 : ℝ) : ℂ) := by
  let a := (hillMiuraDiracLeft u.val (n : ℤ)).re
  let b := (hillMiuraDiracRight u.val (n : ℤ)).re
  let f : ℝ → ℝ := fun x => x^2-e
  let g := hillHminusRealGapProfile q (n : ℕ)
  have hab : a ≤ b := hillMiuraDiracPair_ordered u.val (n : ℤ)
  have ha : 0 < a := hillMiura_positive_gap_left_pos u (n : ℤ) (by exact_mod_cast n.property)
  have hl := hillHminusRealLabels_critical_miura_left q hr u e hm hi n
  have hright := hillHminusRealLabels_critical_miura_right q hr u e hm hi n
  have hder : ∀ x ∈ uIcc a b, HasDerivAt f (2*x) x := by
    intro x _
    simpa only [f,Function.id_def,Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one] using! ((hasDerivAt_id x).pow 2).sub_const e
  have hg : ContinuousOn g (f '' uIcc a b) := by
    apply (continuousOn_hillHminusRealGapProfile q hr (n : ℕ) n.property).mono
    rintro y ⟨x,hx,rfl⟩
    rw [uIcc_of_le hab] at hx
    rw [hl,hright]
    change a^2-e ≤ x^2-e ∧ x^2-e ≤ b^2-e
    constructor <;> nlinarith [hx.1,hx.2]
  have hsub := intervalIntegral.integral_comp_mul_deriv' hder (by fun_prop) hg
  have hInt : (∫ x in a..b, (g ∘ f) x*(2*x)) =
      2*∫ x in a..b, x*sourceRealGapArcoshProfile (by norm_num) (hillMiuraDiagonal u.val) (n : ℤ) x := by
    rw [←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    change hillHminusRealGapProfile q (n : ℕ) (x^2-e)*(2*x) = _
    rw [hillHminusRealGapProfile_shifted_miura_square q u.val e x hi n]
    ring
  rw [hInt] at hsub
  rw [hillHminusRealGapContourMoment_eq_profile_integral,hl,hright,
    sourceRealHigherAction_eq_gapIntegral]
  simp only [pow_zero,one_mul,pow_one]
  apply congrArg Complex.ofReal
  change (2/Real.pi)*(∫ x in a^2-e..b^2-e, g x) = _
  change 2*(∫ x in a..b, x*sourceRealGapArcoshProfile (by norm_num) (hillMiuraDiagonal u.val) (n : ℤ) x) =
    ∫ x in a^2-e..b^2-e, g x at hsub
  rw [←hsub]
  change (2/Real.pi)*(2*∫ x in a..b, x*sourceRealGapArcoshProfile (by norm_num) (hillMiuraDiagonal u.val) (n : ℤ) x) =
    2*((2/Real.pi)*∫ x in a..b, x*sourceRealGapArcoshProfile (by norm_num) (hillMiuraDiagonal u.val) (n : ℤ) x)
  ring

end NLS.KdV
