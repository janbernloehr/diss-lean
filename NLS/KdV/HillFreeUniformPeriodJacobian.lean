import NLS.KdV.HillFreeSupportedPeriodMap
import NLS.ComplexAnalysis.BanachTaylorBounds
import NLS.FunctionalAnalysis.NeumannCompositionBound

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal Classical

namespace NLS.KdV



variable
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- The nonlinear free period remainder is small in Hilbert norm uniformly
in the deleted coordinate, beyond its derivative identity at the origin. -/
theorem norm_hillFreeScaledPeriodSequence_add_projection_le (n : ℕ) (hn : 1≤n) (a : Coeff 2) :
    ‖hillFreeScaledPeriodSequence hq hr n hn a+Coeff.positiveDeletedProjection 2 (n : ℤ) a‖ ≤
      (Real.exp ((2/Real.pi^2)*‖a‖)-1)*‖a‖ := by
  let K := Real.exp ((2/Real.pi^2)*‖a‖)-1
  have hK : 0≤K := sub_nonneg.mpr (Real.one_le_exp (by positivity))
  have hrow (m : ℤ) :
      ‖(hillFreeScaledPeriodSequence hq hr n hn a+Coeff.positiveDeletedProjection 2 (n : ℤ) a) m‖ ≤
        K*‖a m‖ := by
    simp only [lp.coeFn_add,Pi.add_apply,hillFreeScaledPeriodSequence_apply,
      hillFreeScaledPeriodCoordinate,Coeff.positiveDeletedProjection_apply]
    by_cases hm : 0<m ∧ m≠(n : ℤ)
    · rw [if_pos hm,if_pos hm,hillFreeScaledHilbertPeriod_eq_product hq hr n m.toNat hn (by omega) (by omega)]
      have hcast : (m.toNat : ℤ)=m := by omega
      rw [hcast,show -a m*hilbertWeightedProduct (hillFreeSeparatedWeight n m.toNat) a+a m =
          -a m*(hilbertWeightedProduct (hillFreeSeparatedWeight n m.toNat) a-1) by ring,
        norm_mul,norm_neg]
      have hh := norm_hilbertWeightedProduct_sub_one_le (hillFreeSeparatedWeight n m.toNat) a
      have hweight := mul_le_mul_of_nonneg_left (norm_hillFreeSeparatedWeight_le n m.toNat) (norm_nonneg a)
      have hbound : ‖hilbertWeightedProduct (hillFreeSeparatedWeight n m.toNat) a-1‖≤K :=
        hh.trans (sub_le_sub_right (Real.exp_le_exp.mpr (by nlinarith)) 1)
      exact (mul_le_mul_of_nonneg_left hbound (norm_nonneg (a m))).trans_eq (by ring)
    · rw [if_neg hm,if_neg hm,zero_add,norm_zero]
      positivity
  have hnorm : ‖hillFreeScaledPeriodSequence hq hr n hn a+Coeff.positiveDeletedProjection 2 (n : ℤ) a‖ ≤
      ‖(K : ℂ) • a‖ := by
    apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞)≠0)
    intro m
    simpa only [lp.coeFn_smul,Pi.smul_apply,norm_smul,norm_real,Real.norm_eq_abs,abs_of_nonneg hK] using hrow m
  simpa only [norm_smul,norm_real,Real.norm_eq_abs,abs_of_nonneg hK] using hnorm

theorem norm_hillFreeSupportedPeriodMap_add_self_le (n : ℕ) (hn : 1≤n)
    (a : PositiveDeletedCoeff 2 (n : ℤ)) :
    ‖hillFreeSupportedPeriodMap hq hr n hn a+a‖ ≤
      (Real.exp ((2/Real.pi^2)*‖a‖)-1)*‖a‖ := by
  change ‖(hillFreeSupportedPeriodMap hq hr n hn a : Coeff 2)+(a : Coeff 2)‖≤_
  rw [hillFreeSupportedPeriodMap_coe]
  simpa only [Coeff.positiveDeleted_fixed,Submodule.norm_coe] using
    norm_hillFreeScaledPeriodSequence_add_projection_le hq hr n hn (a : Coeff 2)

/-- A common positive radius controls the actual free supported-period
Jacobian in every coordinate-index-dependent deleted Hilbert space. -/
theorem exists_hillFreeSupportedPeriodMap_uniform_jacobian_half :
    ∃ r : ℝ, 0<r ∧ ∀ n : ℕ, ∀ hn : 1≤n,
      ∀ a : PositiveDeletedCoeff 2 (n : ℤ), ‖a‖≤r →
      ‖fderiv ℂ (hillFreeSupportedPeriodMap hq hr n hn) a+
        ContinuousLinearMap.id ℂ (PositiveDeletedCoeff 2 (n : ℤ))‖≤1/2 := by
  let L : ℝ := 2/Real.pi^2
  let r : ℝ := Real.log (13/12)/(3*L)
  have hL : 0<L := by dsimp only [L];positivity
  have hrpos : 0<r := div_pos (Real.log_pos (by norm_num)) (by positivity)
  have hexp : Real.exp (3*L*r)=13/12 := by
    rw [show 3*L*r=Real.log (13/12) by dsimp only [r];field_simp]
    exact Real.exp_log (by norm_num)
  refine ⟨r,hrpos,?_⟩
  intro n hn a ha
  let F := fun b : PositiveDeletedCoeff 2 (n : ℤ) => hillFreeSupportedPeriodMap hq hr n hn b+b
  have hF : AnalyticOnNhd ℂ F univ := (analyticOnNhd_hillFreeSupportedPeriodMap hq hr n hn).add analyticOnNhd_id
  have hb (b : PositiveDeletedCoeff 2 (n : ℤ)) (hb : b∈ball a (r+r)) :
      ‖F b‖≤(Real.exp (3*L*r)-1)*(3*r) := by
    have hba : ‖b-a‖<2*r := by simpa only [mem_ball,dist_eq_norm,two_mul] using hb
    have hbr : ‖b‖≤3*r := by
      have hh := norm_add_le (b-a) a
      rw [sub_add_cancel] at hh
      linarith
    have he : 0≤Real.exp (L*‖b‖)-1 := sub_nonneg.mpr (Real.one_le_exp (by positivity))
    exact (norm_hillFreeSupportedPeriodMap_add_self_le hq hr n hn b).trans
      (mul_le_mul (sub_le_sub_right (Real.exp_le_exp.mpr (by nlinarith)) 1) hbr (norm_nonneg _) (by
        rw [hexp];norm_num))
  have hd := norm_fderiv_le_of_ball_bound F a a r r _ hrpos
    (hF.differentiableOn.mono (subset_univ _)) hb (mem_ball_self hrpos)
  have hder : fderiv ℂ F a = fderiv ℂ (hillFreeSupportedPeriodMap hq hr n hn) a+
      ContinuousLinearMap.id ℂ (PositiveDeletedCoeff 2 (n : ℤ)) := by
    exact ((analyticOnNhd_hillFreeSupportedPeriodMap hq hr n hn a (mem_univ _)).differentiableAt.hasFDerivAt.add
      (hasFDerivAt_id a)).fderiv
  rw [hder,hexp] at hd
  exact hd.trans_eq (by field_simp [ne_of_gt hrpos];ring)

/-- The actual free Jacobians have two-sided inverses of norm at most two
on one common positive ball, uniformly in the deleted coordinate index. -/
theorem exists_hillFreeSupportedPeriodMap_uniform_inverse_bound :
    ∃ r : ℝ, 0<r ∧ ∀ n : ℕ, ∀ hn : 1≤n,
      ∀ a : PositiveDeletedCoeff 2 (n : ℤ), ‖a‖≤r →
      ∃ R : PositiveDeletedCoeff 2 (n : ℤ) →L[ℂ] PositiveDeletedCoeff 2 (n : ℤ),
        (fderiv ℂ (hillFreeSupportedPeriodMap hq hr n hn) a).comp R=ContinuousLinearMap.id ℂ _ ∧
        R.comp (fderiv ℂ (hillFreeSupportedPeriodMap hq hr n hn) a)=ContinuousLinearMap.id ℂ _ ∧
        ‖R‖≤2 := by
  obtain ⟨r,hrpos,hbound⟩ := exists_hillFreeSupportedPeriodMap_uniform_jacobian_half hq hr
  refine ⟨r,hrpos,?_⟩
  intro n hn a ha
  let T := fderiv ℂ (hillFreeSupportedPeriodMap hq hr n hn) a
  let S : PositiveDeletedCoeff 2 (n : ℤ) →L[ℂ] PositiveDeletedCoeff 2 (n : ℤ) :=
    -(ContinuousLinearMap.id ℂ (PositiveDeletedCoeff 2 (n : ℤ)))
  have hSS : S.comp S=ContinuousLinearMap.id ℂ _ := by
    ext x
    simp only [S,ContinuousLinearMap.comp_apply,neg_apply,
      ContinuousLinearMap.id_apply,neg_neg]
  have he : S.comp (S-T)=T+ContinuousLinearMap.id ℂ _ := by
    ext x
    simp only [S,ContinuousLinearMap.comp_apply,neg_apply,
      sub_apply,ContinuousLinearMap.id_apply,add_apply]
    abel
  have hnear : ‖S.comp (S-T)‖≤1/2 := by rw [he];exact hbound n hn a ha
  obtain ⟨R,hTR,hRT,hR⟩ := NLS.exists_inverse_norm_le_two_mul_of_composition_near T S S hSS hSS hnear
  refine ⟨R,hTR,hRT,hR.trans ?_⟩
  have hS : ‖S‖≤1 := by
    apply ContinuousLinearMap.opNorm_le_bound S (by norm_num)
    intro x
    change ‖-x‖≤1*‖x‖
    simp
  linarith

end NLS.KdV
