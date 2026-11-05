import NLS.KdV.HillMiuraFiniteGapInverseBound
import NLS.KdV.HillMiuraActionReflection
import NLS.Articles.KdVPseudomeasures.OriginalHillInverseActionTrace
import NLS.Articles.KdVPseudomeasures.OriginalHillFiniteGapMiura

/-! The actual mean-zero finite-gap Riccati lift is bounded by the literal
inverse-frequency Hill action mass, with its original factor pi. -/
noncomputable section
open Set Complex NLS.KdV NLS.ZakharovShabat
namespace NLS.Articles.KdVPseudomeasures

theorem hillMiura_signed_inverse_actions_eq_mass (u : PeriodOneRealL2)
    (hf : hillMiuraRealSource u ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    (∑ n ∈ hf.toFinset, sourceRealHigherAction (by simp) (by norm_num)
      (hillMiuraRealSource u) n 1/(n:ℝ))/Real.pi =
      hillNativeInverseActionMass (hillRealNormalizedMiura u) := by
  classical
  let f : ℤ → ℝ := fun n => sourceRealHigherAction (by simp) (by norm_num)
    (hillMiuraRealSource u) n 1/(n:ℝ)
  have hz (n : ℤ) (hn : n ∉ hf.toFinset) : f n=0 := by
    have hgap : canonicalPeriodicGap (by simp) (by norm_num)
        (periodOnePotential (hillMiuraRealSource u).val) (periodOnePotential_mem _) n=0 := by
      by_contra hg
      exact hn ((Set.Finite.mem_toFinset hf).mpr hg)
    dsimp only [f]
    rw [sourceRealHigherAction_of_collapsed _ _ _ _ hgap 1,zero_div]
  have hs : Summable f := summable_of_ne_finset_zero hz
  have heven : f.Even := by
    intro n
    dsimp only [f]
    rw [hillMiura_realHigherAction_neg]
    simp only [pow_one,Int.cast_neg,neg_one_mul,neg_div_neg_eq]
  have ht := tsum_int_eq_zero_add_two_mul_tsum_pnat heven hs
  have h0 : f 0=0 := by simp only [f,Int.cast_zero,div_zero]
  rw [h0,zero_add] at ht
  have hsum : (∑ n ∈ hf.toFinset,f n)=2*∑' n : ℕ+, f (n:ℤ) := by
    rw [← (tsum_eq_sum (f := f) (s := hf.toFinset) hz : (∑' n : ℤ, f n)=_)]
    simpa only [two_smul,two_mul] using ht
  change (∑ n ∈ hf.toFinset,f n)/Real.pi=_
  rw [hsum]
  unfold hillNativeInverseActionMass
  have hterm (n : ℕ+) :
      (hillHminusCanonicalAction n (hillRealMeanZeroInclusion (hillRealNormalizedMiura u))).re/
        (Real.pi*(n:ℕ))=(2/Real.pi)*f (n:ℤ) := by
    rw [hillRealNormalizedMiura_canonicalAction]
    unfold hillHminusMiuraIndexedAction
    rw [show hillMiuraDiagonal u.val=(hillMiuraRealSource u).val from rfl,
      sourceIndexedHigherAction_eq_real]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,
      Complex.re_ofNat,Complex.im_ofNat,f,Int.cast_natCast]
    ring
  simp_rw [hterm]
  rw [tsum_mul_left]
  ring

theorem norm_sq_mean_zero_finiteGap_lift_le_inverseActionMass
    (q : HillRealMeanZeroSource) (hf : q ∈ hillRealFiniteGapLocus)
    (u : PeriodOneRealL2) (hu0 : u.val 0=0) (c : ℝ)
    (hu : periodOneMiura u.val=hillRealMeanZeroInclusion q+
      periodOneL2Inclusion (lp.single 2 0 (c:ℂ))) :
    ‖u.val‖^2 ≤ hillNativeInverseActionMass q := by
  have hfin := hillMiuraRealSource_finiteGap_of_hillRealFiniteGap q hf u c hu
  have h := norm_sq_hillMiura_finiteGap_le_signed_inverse_actions u hu0 hfin
  rw [hillMiura_signed_inverse_actions_eq_mass u hfin,
    hillRealNormalizedMiura_eq_of_shifted_image q u c hu] at h
  exact h

end NLS.Articles.KdVPseudomeasures
