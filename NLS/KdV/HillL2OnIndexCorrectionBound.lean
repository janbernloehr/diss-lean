import NLS.KdV.HillL2OnIndexWeights
import NLS.KdV.HillOnIndexBoundedExponent

/-! One uniform bound for the FULL actual on-index correction after
multiplication by 1+n, on a common complex L2 neighborhood of every
real source. The original analytic finite head and weighted tail are
both included; no gap or terminal sheet is divided out. -/
noncomputable section
open Set Complex Filter Topology NLS.ZakharovShabat
namespace NLS.KdV.HillProductEquationPatch

private theorem weighted_correction_of_bounds (P : HillProductEquationPatch) (r : Coeff 2)
    (K : ℕ) (Ct Ch M : ℝ) (hCt : 0 ≤ Ct) (hCh : 0 ≤ Ch) (hM : 0 ≤ M)
    (ht : ∀ n : ℕ+, K < (n : ℕ) →
      ‖P.physicalOnIndexAbelianCorrection n (periodOneL2Inclusion r)‖ ≤ Ct *
        (‖P.physicalAbelianMidpointDisplacement (periodOneL2Inclusion r) ((n : ℕ) : ℤ)‖ +
          ‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num)
            (P.sourcePsi (periodOneL2Inclusion r)) ((n : ℕ) : ℤ)‖))
    (hh : ∀ n : ℕ+, ‖P.physicalOnIndexAbelianCorrection n (periodOneL2Inclusion r)‖ ≤ Ch)
    (hw : ∀ n : ℕ+, Weight.sobolev 1 ((n : ℕ) : ℤ) *
      (‖P.physicalAbelianMidpointDisplacement (periodOneL2Inclusion r) ((n : ℕ) : ℤ)‖ +
        ‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num)
          (P.sourcePsi (periodOneL2Inclusion r)) ((n : ℕ) : ℤ)‖) ≤ M)
    (n : ℕ+) : Weight.sobolev 1 ((n : ℕ) : ℤ) *
      ‖P.physicalOnIndexAbelianCorrection n (periodOneL2Inclusion r)‖ ≤ Ct*M+(1+(K : ℝ))*Ch := by
  by_cases hn : K < (n : ℕ)
  · calc
      _ ≤ Weight.sobolev 1 ((n : ℕ) : ℤ) * (Ct *
          (‖P.physicalAbelianMidpointDisplacement (periodOneL2Inclusion r) ((n : ℕ) : ℤ)‖ +
            ‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num)
              (P.sourcePsi (periodOneL2Inclusion r)) ((n : ℕ) : ℤ)‖)) :=
        mul_le_mul_of_nonneg_left (ht n hn) ((Weight.sobolev 1).positive _).le
      _ = Ct * (Weight.sobolev 1 ((n : ℕ) : ℤ) *
          (‖P.physicalAbelianMidpointDisplacement (periodOneL2Inclusion r) ((n : ℕ) : ℤ)‖ +
            ‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num)
              (P.sourcePsi (periodOneL2Inclusion r)) ((n : ℕ) : ℤ)‖)) := by ring
      _ ≤ Ct*M := mul_le_mul_of_nonneg_left (hw n) hCt
      _ ≤ _ := le_add_of_nonneg_right (mul_nonneg (by positivity) hCh)
  · have hnk : (n : ℕ) ≤ K := Nat.le_of_not_gt hn
    have hW : Weight.sobolev 1 ((n : ℕ) : ℤ) ≤ 1+(K : ℝ) := by
      simp only [Weight.sobolev_apply,Real.rpow_one,Int.cast_natCast,
        abs_of_nonneg (show (0 : ℝ) ≤ ((n : ℕ) : ℝ) by positivity)]
      have hr : ((n : ℕ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast hnk
      linarith
    exact (mul_le_mul hW (hh n) (norm_nonneg _) (by positivity)).trans
      (le_add_of_nonneg_left (mul_nonneg hCt hM))

private theorem eventually_l2_mem (q : Coeff 2) (U : Set PeriodOneHminusOne)
    (hU : IsOpen U) (hq : periodOneL2Inclusion q ∈ U) :
    ∀ᶠ r in 𝓝 q, periodOneL2Inclusion r ∈ U :=
  periodOneL2Inclusion.continuous.continuousAt.tendsto.eventually (hU.mem_nhds hq)

theorem exists_local_l2OnIndex_correction_weighted_bound (P : HillProductEquationPatch)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots)
    (q : Coeff 2) (hq : periodOneL2Inclusion q ∈ P.physicalDirichletSource)
    (hr : IsRealPeriodOneHminusOne (periodOneL2Inclusion q)) :
    ∃ U : Set (Coeff 2), IsOpen U ∧ q ∈ U ∧
      (∀ r ∈ U, periodOneL2Inclusion r ∈ P.physicalDirichletSource) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ r ∈ U, ∀ n : ℕ+,
        Weight.sobolev 1 ((n : ℕ) : ℤ) *
          ‖P.physicalOnIndexAbelianCorrection n (periodOneL2Inclusion r)‖ ≤ C := by
  obtain ⟨Ut,hUt,hqUt,_,K,Ct,hCt,ht⟩ :=
    P.exists_local_uniform_physicalOnIndexCorrection_weighted_tail_bound H (periodOneL2Inclusion q) hq
  obtain ⟨Uh,hUh,hqUh,_,Ch,hCh,hh⟩ :=
    P.exists_local_uniform_physicalOnIndexAbelianCorrection_bound H (periodOneL2Inclusion q) hq
  obtain ⟨Uw,hUw,hqUw,hUwP,M,hM,hw⟩ := P.exists_local_l2OnIndex_weight_bound q hq hr
  have hwe : ∀ᶠ r in 𝓝 q, r ∈ Uw := hUw.mem_nhds hqUw
  have he : ∀ᶠ r in 𝓝 q, r ∈ Uw ∧ periodOneL2Inclusion r ∈ Ut ∧ periodOneL2Inclusion r ∈ Uh :=
    hwe.and ((eventually_l2_mem q Ut hUt hqUt).and (eventually_l2_mem q Uh hUh hqUh))
  obtain ⟨U,hUsub,hU,hqU⟩ := _root_.mem_nhds_iff.mp he
  refine ⟨U,hU,hqU,(fun r hrU => hUwP r (hUsub hrU).1),Ct*M+(1+(K : ℝ))*Ch,by positivity,?_⟩
  intro r hrU n
  exact weighted_correction_of_bounds P r K Ct Ch M hCt.le hCh.le hM.le
    (ht _ (hUsub hrU).2.1) (hh _ (hUsub hrU).2.2) (hw _ (hUsub hrU).1) n

end NLS.KdV.HillProductEquationPatch
