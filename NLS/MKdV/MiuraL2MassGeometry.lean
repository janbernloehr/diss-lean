import NLS.MKdV.MiuraL2MassTrace

/-! # Norm control from the full original L² action and mean map

The mass trace identifies the actual scalar L² norm and independent
native K₁. The first moment is bounded in the native weighted action
norm, giving a concrete coercive bound for the action and mean map.
-/
noncomputable section
open Set Filter Topology NLS.Poisson NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem nativeMiuraHillHamiltonian_zero_eq_L2Mass (u : ScalarSobolev 0) :
    nativeMiuraHillHamiltonian 0 u = miuraL2Mass (hierarchySobolevJetL2 0 0 le_rfl u) := by
  simp only [nativeMiuraHillHamiltonian,show ¬1 ≤ (0 : ℕ) by omega,↓reduceIte,nativeMiuraMass,
    sobolevOddKinetic,miuraL2Mass,reflectedHilbertPairing_apply,Coeff.dualPairing_apply,
    Coeff.reflection_apply,hierarchySobolevJetL2_apply,hierarchySobolevInclusion_apply,pow_zero,one_mul]
  congr 1
  apply tsum_congr
  intro j
  ring

theorem miuraL2Mass_eq_half_norm_sq (a : Coeff 2) (ha : ∀ j, a j = conj (a (-j))) :
    miuraL2Mass a = (1/2 : ℂ)*((‖a‖^2 : ℝ) : ℂ) := by
  have hpair : reflectedHilbertPairing a a = ((‖a‖^2 : ℝ) : ℂ) := by
    calc
      _ = inner ℂ a a := by
        rw [reflectedHilbertPairing_apply,lp.inner_eq_tsum]
        apply tsum_congr
        intro j
        simp only [RCLike.inner_apply',starRingEnd_apply]
        have h := ha (-j)
        simp only [neg_neg] at h
        rw [h]
        change a j*conj (a j) = conj (a j)*a j
        ring
      _ = _ := by rw [inner_self_eq_norm_sq_to_K]; norm_cast
  exact congrArg (fun z : ℂ => (1/2 : ℂ)*z) hpair

theorem miuraL2_norm_sq_eq_action_mean (a : Coeff 2) (ha : ∀ j, a j = conj (a (-j))) :
    ‖a‖^2 = (a 0).re^2+2*(miuraL2ActionMoment a).re := by
  have him : (a 0).im = 0 := by
    have h := congrArg Complex.im (ha 0)
    simp only [neg_zero,Complex.conj_im] at h
    linarith
  have h := congrArg Complex.re (miuraL2Mass_eq_mean_sq_add_actionMoment a ha)
  rw [miuraL2Mass_eq_half_norm_sq a ha] at h
  have hre : ((a 0)^2).re = (a 0).re^2 := by simp [pow_two,Complex.mul_re,him]
  norm_num [Complex.mul_re,hre] at h
  rw [← Complex.ofReal_pow,Complex.ofReal_re] at h
  linarith

/-- The native positive-index action series converges to the actual first moment. -/
theorem hasSum_miuraL2ActionMoment (a : Coeff 2) (ha : ∀ j, a j = conj (a (-j))) :
    HasSum (fun n : ℕ => (2*(Real.pi : ℂ)*(n+1))*miuraL2Action (n+1) a) (miuraL2ActionMoment a) := by
  obtain ⟨U,_,hreal,_,hcoord⟩ := exists_miuraL2ActionSequence_domain
  let v := miuraL2ActionSequence a
  have hs : HasSum (fun n : ℤ => (2*(Real.pi : ℂ)*n)*v.val n) (miuraL2ActionMoment a) := by
    change HasSum _ (∑' n : ℤ, miuraL2ActionMomentSequence v n)
    have hh := (miuraL2ActionMomentSequence v).property.summable_of_one.hasSum
    change HasSum (fun n : ℤ => miuraL2ActionMomentSequence v n) (∑' n : ℤ, miuraL2ActionMomentSequence v n) at hh
    simpa only [miuraL2ActionMomentSequence_apply] using hh
  have h := hs.nat_add_neg
  have hnonpos (n : ℕ) : v.val (-(n : ℤ)) = 0 := miuraL2ActionSequence_nonpositive a _ (by omega)
  have hz : v.val 0 = 0 := miuraL2ActionSequence_nonpositive a _ (by omega)
  simp only [hnonpos,hz,mul_zero,Int.cast_zero,add_zero] at h
  have hp := (hasSum_nat_add_iff' 1).mpr h
  simp only [Finset.sum_range_one,Nat.cast_zero,Int.cast_zero,mul_zero,zero_mul,sub_zero] at hp
  convert! hp using 1
  funext n
  rw [show v.val ((n+1 : ℕ) : ℤ) = miuraL2Action (n+1) a from hcoord a (hreal ha) (n+1) (by omega)]
  norm_cast

/-- Norm control is expressed in the full native weighted target norm. -/
theorem miuraL2_norm_sq_le_actionMeanMap (a : Coeff 2) (ha : ∀ j, a j = conj (a (-j))) :
    ‖a‖^2 ≤ ‖miuraL2ActionMeanMap a‖^2+
      2*‖miuraL2ActionMomentFunctional‖*‖miuraL2ActionMeanMap a‖ := by
  have hm : |(a 0).re| ≤ ‖miuraL2ActionMeanMap a‖ :=
    (Complex.abs_re_le_norm _).trans (norm_snd_le (miuraL2ActionMeanMap a))
  have hmsq : (a 0).re^2 ≤ ‖miuraL2ActionMeanMap a‖^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr hm
  have hJ : ‖miuraL2ActionSequence a‖ ≤ ‖miuraL2ActionMeanMap a‖ := norm_fst_le (miuraL2ActionMeanMap a)
  have hM : (miuraL2ActionMoment a).re ≤
      ‖miuraL2ActionMomentFunctional‖*‖miuraL2ActionMeanMap a‖ :=
    (Complex.re_le_norm _).trans ((miuraL2ActionMomentFunctional.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left hJ (norm_nonneg _)))
  rw [miuraL2_norm_sq_eq_action_mean a ha]
  linarith

end NLS.MKdV
