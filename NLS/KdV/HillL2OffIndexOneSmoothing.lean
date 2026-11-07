import NLS.KdV.HillL2OffIndexWeightedCorrection
import NLS.KdV.HillNativeDiagonalGauge
import NLS.SequenceSpaces.WeightedInfinityAnalyticRealization
import NLS.SequenceSpaces.WeightedInfinityExponentialRemainder

/-! The ACTUAL global signed off-index exponent and its exponential
minus one are analytic in one-order weighted infinity norm near EVERY
real L2 source. One common neighborhood precedes all signed modes. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV

theorem exists_local_hillL2OffIndexCorrection_weighted_bound (q : Coeff 2)
    (hr : IsRealPeriodOneHminusOne (periodOneL2Inclusion q)) :
    ∃ U : Set (Coeff 2), IsOpen U ∧ q ∈ U ∧
      (∀ r ∈ U, periodOneL2Inclusion r ∈ hillHminusOffIndexBoundedDomain) ∧
      ∃ R : ℝ, 0 < R ∧ ∀ r ∈ U, ∀ n : ℕ+,
        (1+(n:ℝ))*‖hillHminusOffIndexAbelianCorrection n (periodOneL2Inclusion r)‖ ≤ R := by
  obtain ⟨A,H⟩ := exists_miuraHillPsiFamily_with_original_estimates
  obtain ⟨P,hqP,_,hPA⟩ := exists_hillProductEquationPatch_with_family A (periodOneL2Inclusion q) hr
  have HP : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots := by rw [hPA]; exact H
  obtain ⟨Uw,hUw,hqUw,_,R,hR,hb⟩ := P.exists_local_l2OffIndex_weighted_correction_bound HP q hqP hr
  obtain ⟨ρ,hρ,_,heq⟩ := exists_common_offIndex_correction_patch_ball P (periodOneL2Inclusion q) hqP hr
  let V := ball (periodOneL2Inclusion q) ρ ∩ hillHminusOffIndexBoundedDomain
  let U := Uw ∩ periodOneL2Inclusion ⁻¹' V
  refine ⟨U,hUw.inter ((isOpen_ball.inter isOpen_hillHminusOffIndexBoundedDomain).preimage
      periodOneL2Inclusion.continuous),⟨hqUw,mem_ball_self hρ,real_mem_hillHminusOffIndexBoundedDomain _ hr⟩,
    (fun r hrU => hrU.2.2),R,hR,?_⟩
  intro r hrU n
  rw [(heq n _ hrU.2.1).2.2]
  exact (hb r hrU.1 n).2

def hillL2OffIndexSobolevExponent (q : Coeff 2) : WeightedCoeff (Weight.sobolev 1) ⊤ :=
  WeightedCoeff.ofFunctionOrZero _ ⊤ (fun k => hillHminusSignedOffIndexExponent (periodOneL2Inclusion q) k)

private theorem signed_exponent_weighted_bound (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusOffIndexBoundedDomain) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ n : ℕ+, (1+(n:ℝ))*‖hillHminusOffIndexAbelianCorrection n q‖ ≤ C) (k : ℤ) :
    Weight.sobolev 1 k*‖hillHminusSignedOffIndexExponent q k‖ ≤ C := by
  rcases lt_trichotomy 0 k with hk | hk | hk
  · let n : ℕ+ := ⟨k.natAbs,Int.natAbs_pos.mpr (by omega)⟩
    have hn : ((n:ℕ):ℤ) = k := by change (k.natAbs:ℤ) = k; omega
    rw [← hn,hillHminusSignedOffIndexExponent_positive q hq]
    simpa only [Weight.sobolev_apply,Real.rpow_one,Int.cast_natCast,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ)),norm_mul,norm_neg,norm_I,one_mul] using hb n
  · subst k
    simp only [hillHminusSignedOffIndexExponent,lp.coeFn_add,Pi.add_apply,lp.coeFn_smul,
      Pi.smul_apply,smul_eq_mul,Coeff.reflection_apply,neg_zero,
      hillHminusOffIndexAbelianBoundedSequence_nonpositive q hq 0 le_rfl,mul_zero,zero_add,norm_zero]
    simpa only [mul_zero] using hC
  · let n : ℕ+ := ⟨k.natAbs,Int.natAbs_pos.mpr (by omega)⟩
    have hn : -((n:ℕ):ℤ) = k := by change -(k.natAbs:ℤ) = k; omega
    rw [← hn,hillHminusSignedOffIndexExponent_negative q hq,Weight.sobolev_neg]
    simpa only [Weight.sobolev_apply,Real.rpow_one,Int.cast_natCast,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ)),norm_mul,norm_I,one_mul] using hb n

private theorem analytic_exponent_coordinate (q : Coeff 2)
    (hq : periodOneL2Inclusion q ∈ hillHminusOffIndexBoundedDomain) (k : ℤ) :
    AnalyticAt ℂ (fun r : Coeff 2 => hillHminusSignedOffIndexExponent (periodOneL2Inclusion r) k) q :=
  ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) ⊤ k).analyticAt _).comp
    (f := fun r : Coeff 2 => hillHminusSignedOffIndexExponent (periodOneL2Inclusion r))
      ((analyticOnNhd_hillHminusSignedOffIndexExponent _ hq).comp
        (f := fun r : Coeff 2 => periodOneL2Inclusion r) (periodOneL2Inclusion.analyticAt q))

theorem exists_local_hillL2OffIndexSobolevExponent_data (q : Coeff 2)
    (hr : IsRealPeriodOneHminusOne (periodOneL2Inclusion q)) :
    ∃ U : Set (Coeff 2), IsOpen U ∧ q ∈ U ∧
      (∀ r ∈ U, periodOneL2Inclusion r ∈ hillHminusOffIndexBoundedDomain) ∧
      ∃ C : ℝ, 0 < C ∧ AnalyticOnNhd ℂ hillL2OffIndexSobolevExponent U ∧
        ∀ r ∈ U, ‖hillL2OffIndexSobolevExponent r‖ ≤ C ∧ ∀ k : ℤ,
          (hillL2OffIndexSobolevExponent r).val k = hillHminusSignedOffIndexExponent (periodOneL2Inclusion r) k := by
  obtain ⟨U,hU,hqU,hUD,C,hC,hb⟩ := exists_local_hillL2OffIndexCorrection_weighted_bound q hr
  have h := WeightedCoeff.analytic_infty_realization_of_weighted_bound (Weight.sobolev 1)
    (fun r k => hillHminusSignedOffIndexExponent (periodOneL2Inclusion r) k) hU
    (fun k r hrU => analytic_exponent_coordinate r (hUD r hrU) k) C hC.le
    (fun r hrU k => signed_exponent_weighted_bound _ (hUD r hrU) C hC.le (hb r hrU) k)
  exact ⟨U,hU,hqU,hUD,C,hC,h.1,h.2⟩

def hillL2OffIndexExponentialRemainder (q : Coeff 2) : WeightedCoeff (Weight.sobolev 1) ⊤ :=
  WeightedCoeff.weightedExpRemainder (Weight.sobolev 1) (hillL2OffIndexSobolevExponent q)

private theorem sobolev_one_ge_one (k : ℤ) : 1 ≤ Weight.sobolev 1 k := by
  simp only [Weight.sobolev_apply,Real.rpow_one]
  linarith [abs_nonneg (k:ℝ)]

theorem analyticAt_hillL2OffIndexExponentialRemainder (q : Coeff 2)
    (hr : IsRealPeriodOneHminusOne (periodOneL2Inclusion q)) :
    AnalyticAt ℂ hillL2OffIndexExponentialRemainder q := by
  obtain ⟨U,_,hqU,_,_,_,ha,_⟩ := exists_local_hillL2OffIndexSobolevExponent_data q hr
  exact (WeightedCoeff.analyticAt_weightedExpRemainder (Weight.sobolev 1) sobolev_one_ge_one _).comp (ha q hqU)

theorem eventually_hillL2OffIndexExponentialRemainder_apply (q : Coeff 2)
    (hr : IsRealPeriodOneHminusOne (periodOneL2Inclusion q)) :
    ∀ᶠ r in 𝓝 q, ∀ k : ℤ, (hillL2OffIndexExponentialRemainder r).val k =
      Complex.exp (hillHminusSignedOffIndexExponent (periodOneL2Inclusion r) k)-1 := by
  obtain ⟨U,hU,hqU,_,_,_,_,hraw⟩ := exists_local_hillL2OffIndexSobolevExponent_data q hr
  have hm : ∀ᶠ r in 𝓝 q, r ∈ U := hU.mem_nhds hqU
  exact hm.mono (fun r hrU k => by
    rw [hillL2OffIndexExponentialRemainder,WeightedCoeff.weightedExpRemainder_apply _ sobolev_one_ge_one,
      (hraw r hrU).2 k])

end NLS.KdV
