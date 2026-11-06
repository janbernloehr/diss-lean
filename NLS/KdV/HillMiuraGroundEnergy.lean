import NLS.KdV.HillMiuraZeroGap
import NLS.KdV.HillHminusOneGlobalRealLabels
import NLS.ZakharovShabat.FiniteDiscriminant

/-! # The actual normalized Miura energy is the lowest rough Hill energy

Every actual real factor gives a lower bound for every characteristic
root: its square-root frequency belongs to the actual real Dirac
spectrum, so its square is nonnegative. A mean-zero factor attains this
bound through its actual periodic zero-energy gauge. No exterior shift
or inverse at the critical Miura factor is used.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ZakharovShabat NLS.ComplexAnalysis
namespace NLS.KdV

/-- An actual real Miura factor bounds EVERY actual complex characteristic
root below by its translated zero energy. No mean-zero premise is needed. -/
theorem neg_miura_energy_le_re_of_hillHminusRadicand_eq_zero
    (q : PeriodOneHminusOne) (u : PeriodOneRealL2) (e : ℝ)
    (hi : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (e : ℂ)))
    (E : ℂ) (hE : hillHminusRadicand q E = 0) : -e ≤ E.re := by
  let z := Complex.sqrt (E+(e : ℂ))
  have hs : z^2 = E+(e : ℂ) := complex_sqrt_sq _
  have ht := hillHminusDiscriminant_shifted_miura_square q u.val (e : ℂ) z hi
  rw [hs,add_sub_cancel_right] at ht
  have hD : z ∈ periodicSpectrum (by simp) (periodOnePotential (hillMiuraDiagonal u.val)) := by
    apply (canonicalDiscriminant_sq_eq_four_iff_finite (by simp) (by norm_num)
      (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _) z).mp
    rw [←ht]
    exact sub_eq_zero.mp hE
  have him := periodicSpectrum_im_eq_zero_of_realType (by simp)
    (periodOnePotential (hillMiuraDiagonal u.val))
    (isRealType_periodOnePotential _ (hillMiuraRealSource u).property) z hD
  have hre := congrArg Complex.re hs
  simp only [sq,Complex.mul_re,Complex.add_re,ofReal_re,him,mul_zero,sub_zero] at hre
  nlinarith [sq_nonneg z.re]

/-- The energy of ANY actual mean-zero real factor is exactly the negative
of the intrinsic lowest characteristic energy. Minimality is not assumed. -/
theorem neg_miura_energy_eq_hillHminusLowestRealRoot
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (u : PeriodOneRealL2) (e : ℝ) (hm : u.val 0 = 0)
    (hi : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (e : ℂ))) :
    -e = hillHminusLowestRealRoot q hr := by
  apply hillHminusLowestRealRoot_eq_of_minimal q hr (-e)
  · rw [hillHminusRadicand,ofReal_neg,hillHminusDiscriminant_neg_energy_eq_two q u e hm hi]
    norm_num
  · exact neg_miura_energy_le_re_of_hillHminusRadicand_eq_zero q u e hi

/-- Every real mean-zero rough source has an ACTUAL normalized factor at
EXACTLY its intrinsic ground energy, with collapsed central Dirac gap and
vanishing original indexed action. This includes all non-L2 sources. -/
theorem exists_periodOneMiura_ground_factor (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (hm : q.val 0 = 0) :
    ∃ u : PeriodOneRealL2, u.val 0 = 0 ∧
      periodOneMiura u.val = q+periodOneL2Inclusion
        (lp.single 2 0 (-hillHminusLowestRealRoot q hr : ℝ)) ∧
      ‖u.val‖^2 = -hillHminusLowestRealRoot q hr ∧
      hillHminusDiscriminant q (hillHminusLowestRealRoot q hr : ℂ) = 2 ∧
      canonicalPeriodicLeft (by simp) (by norm_num)
        (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _) 0 = 0 ∧
      canonicalPeriodicRight (by simp) (by norm_num)
        (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _) 0 = 0 ∧
      sourceIndexedAction (by simp) (by norm_num) 0 (hillMiuraDiagonal u.val) = 0 := by
  obtain ⟨e,_he,u,hu,hi,hn,_hq,_hmin⟩ := exists_periodOneMiura_minimal_meanZero_factor q hr hm
  have he := neg_miura_energy_eq_hillHminusLowestRealRoot q hr u e hu hi
  have he' : e = -hillHminusLowestRealRoot q hr := by linarith
  refine ⟨u,hu,?_,hn.trans he',?_,(hillMiura_central_endpoints_eq_zero u hu).1,
    (hillMiura_central_endpoints_eq_zero u hu).2,hillMiura_central_indexed_action_eq_zero u hu⟩
  · simpa only [he'] using hi
  · rw [←he,ofReal_neg]
    exact hillHminusDiscriminant_neg_energy_eq_two q u e hu hi

end NLS.KdV
