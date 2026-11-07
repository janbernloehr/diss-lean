import NLS.KdV.HillL2OnIndexCorrectionBound
import NLS.SequenceSpaces.WeightedInfinityAnalyticRealization

/-! The SAME actual signed on-index exponent is analytic in the
one-order weighted infinity norm on complex L2 neighborhoods of every
real physical source. Every signed coefficient and the central zero
are retained from the original exponent. -/
noncomputable section
open Set Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV.HillProductEquationPatch

def l2OnIndexSobolevExponent (P : HillProductEquationPatch) (q : Coeff 2) :
    WeightedCoeff (Weight.sobolev 1) ⊤ :=
  WeightedCoeff.ofFunctionOrZero _ ⊤ (fun k => P.physicalOnIndexSignedExponent (periodOneL2Inclusion q) k)

private theorem exponent_weighted_bound (P : HillProductEquationPatch)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots)
    (r : Coeff 2) (hrP : periodOneL2Inclusion r ∈ P.physicalDirichletSource)
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ n : ℕ+, Weight.sobolev 1 ((n : ℕ) : ℤ) *
      ‖P.physicalOnIndexAbelianCorrection n (periodOneL2Inclusion r)‖ ≤ C) (k : ℤ) :
    Weight.sobolev 1 k * ‖P.physicalOnIndexSignedExponent (periodOneL2Inclusion r) k‖ ≤ C := by
  rcases lt_trichotomy 0 k with hk | hk | hk
  · let n : ℕ+ := ⟨k.natAbs,Int.natAbs_pos.mpr (by omega)⟩
    have hn : ((n : ℕ) : ℤ) = k := by change (k.natAbs : ℤ) = k; omega
    rw [← hn,P.physicalOnIndexSignedExponent_positive H _ hrP]
    simpa only [norm_mul,norm_neg,norm_I,one_mul] using hb n
  · subst k
    rw [P.physicalOnIndexSignedExponent_zero_mode H _ hrP,norm_zero,mul_zero]
    exact hC
  · let n : ℕ+ := ⟨k.natAbs,Int.natAbs_pos.mpr (by omega)⟩
    have hn : -((n : ℕ) : ℤ) = k := by change -(k.natAbs : ℤ) = k; omega
    rw [← hn,P.physicalOnIndexSignedExponent_negative H _ hrP,Weight.sobolev_neg]
    simpa only [norm_mul,norm_I,one_mul] using hb n

private theorem analytic_exponent_coordinate (P : HillProductEquationPatch)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots)
    (r : Coeff 2) (hrP : periodOneL2Inclusion r ∈ P.physicalDirichletSource) (k : ℤ) :
    AnalyticAt ℂ (fun a : Coeff 2 => P.physicalOnIndexSignedExponent (periodOneL2Inclusion a) k) r :=
  ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) ⊤ k).analyticAt _).comp
    (f := fun a : Coeff 2 => P.physicalOnIndexSignedExponent (periodOneL2Inclusion a))
      ((P.analytic_physicalOnIndexSignedExponent H _ hrP).comp
        (f := fun a : Coeff 2 => periodOneL2Inclusion a) (periodOneL2Inclusion.analyticAt r))

theorem exists_local_l2OnIndexSobolevExponent_data (P : HillProductEquationPatch)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots)
    (q : Coeff 2) (hq : periodOneL2Inclusion q ∈ P.physicalDirichletSource)
    (hr : IsRealPeriodOneHminusOne (periodOneL2Inclusion q)) :
    ∃ U : Set (Coeff 2), IsOpen U ∧ q ∈ U ∧
      (∀ r ∈ U, periodOneL2Inclusion r ∈ P.physicalDirichletSource) ∧
      ∃ C : ℝ, 0 < C ∧ AnalyticOnNhd ℂ P.l2OnIndexSobolevExponent U ∧
        ∀ r ∈ U, ‖P.l2OnIndexSobolevExponent r‖ ≤ C ∧ ∀ k : ℤ,
          (P.l2OnIndexSobolevExponent r).val k = P.physicalOnIndexSignedExponent (periodOneL2Inclusion r) k := by
  obtain ⟨U,hU,hqU,hUP,C,hC,hB⟩ := P.exists_local_l2OnIndex_correction_weighted_bound H q hq hr
  have h := WeightedCoeff.analytic_infty_realization_of_weighted_bound (Weight.sobolev 1)
    (fun r k => P.physicalOnIndexSignedExponent (periodOneL2Inclusion r) k) hU
    (fun k r hrU => P.analytic_exponent_coordinate H r (hUP r hrU) k) C hC.le
    (fun r hrU k => P.exponent_weighted_bound H r (hUP r hrU) C hC.le (hB r hrU) k)
  exact ⟨U,hU,hqU,hUP,C,hC,h.1,h.2⟩

theorem analytic_l2OnIndexSobolevExponent (P : HillProductEquationPatch)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots)
    (q : Coeff 2) (hq : periodOneL2Inclusion q ∈ P.physicalDirichletSource)
    (hr : IsRealPeriodOneHminusOne (periodOneL2Inclusion q)) :
    AnalyticAt ℂ P.l2OnIndexSobolevExponent q := by
  obtain ⟨U,_,hqU,_,_,_,ha,_⟩ := P.exists_local_l2OnIndexSobolevExponent_data H q hq hr
  exact ha q hqU

theorem l2OnIndexSobolevExponent_apply (P : HillProductEquationPatch)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots)
    (q : Coeff 2) (hq : periodOneL2Inclusion q ∈ P.physicalDirichletSource)
    (hr : IsRealPeriodOneHminusOne (periodOneL2Inclusion q)) (k : ℤ) :
    (P.l2OnIndexSobolevExponent q).val k = P.physicalOnIndexSignedExponent (periodOneL2Inclusion q) k := by
  obtain ⟨U,_,hqU,_,_,_,_,hraw⟩ := P.exists_local_l2OnIndexSobolevExponent_data H q hq hr
  exact (hraw q hqU).2 k

end NLS.KdV.HillProductEquationPatch
