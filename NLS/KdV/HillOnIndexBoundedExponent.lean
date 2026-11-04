import NLS.KdV.HillOnIndexCorrectionZeroTail
import NLS.KdV.HillOnIndexUniformCorrectionBound
import NLS.SequenceSpaces.OddBoundedAnalyticRealization

/-! The actual signed on-index phase exponent is analytic as a bounded
sequence on the retained physical divisor domain, and its signed tails
vanish. Both signs and all collapsed-gap samples are retained. -/
noncomputable section
open Set Complex NLS.ZakharovShabat NLS.LpSequence
open scoped ENNReal
namespace NLS.KdV.HillProductEquationPatch

def physicalOnIndexSignedExponent (P : HillProductEquationPatch) (q : PeriodOneHminusOne) : Coeff ⊤ :=
  (-I) • Coeff.ofFunctionOrZero ⊤
    (oddPositiveScalarExtension (fun n => P.physicalOnIndexAbelianCorrection n q))

theorem physicalOnIndexOddSequence_data (P : HillProductEquationPatch)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots) :
    (∀ q ∈ P.physicalDirichletSource, ∀ k,
      Coeff.ofFunctionOrZero ⊤ (oddPositiveScalarExtension (fun n => P.physicalOnIndexAbelianCorrection n q)) k =
        oddPositiveScalarExtension (fun n => P.physicalOnIndexAbelianCorrection n q) k) ∧
    AnalyticOnNhd ℂ (fun q => Coeff.ofFunctionOrZero ⊤
      (oddPositiveScalarExtension (fun n => P.physicalOnIndexAbelianCorrection n q))) P.physicalDirichletSource := by
  apply Coeff.analytic_odd_realization_of_local_bounds P.physicalOnIndexAbelianCorrection
    P.physicalDirichletSource_open P.analytic_physicalOnIndexAbelianCorrection
  intro q hq
  obtain ⟨U,hU,hqU,hUP,C,hC,hb⟩ := P.exists_local_uniform_physicalOnIndexAbelianCorrection_bound H q hq
  exact ⟨U,hU,hqU,hUP,C,hC.le,hb⟩

theorem analytic_physicalOnIndexSignedExponent (P : HillProductEquationPatch)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots) :
    AnalyticOnNhd ℂ P.physicalOnIndexSignedExponent P.physicalDirichletSource :=
  fun q hq => ((P.physicalOnIndexOddSequence_data H).2 q hq).const_smul (c := (-I))

theorem physicalOnIndexSignedExponent_positive (P : HillProductEquationPatch)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots)
    (q : PeriodOneHminusOne) (hq : q ∈ P.physicalDirichletSource) (n : ℕ+) :
    P.physicalOnIndexSignedExponent q ((n:ℕ):ℤ) = -I*P.physicalOnIndexAbelianCorrection n q := by
  change -I*Coeff.ofFunctionOrZero ⊤ _ ((n:ℕ):ℤ) = _
  rw [(P.physicalOnIndexOddSequence_data H).1 q hq,oddPositiveScalarExtension_apply]

theorem physicalOnIndexSignedExponent_negative (P : HillProductEquationPatch)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots)
    (q : PeriodOneHminusOne) (hq : q ∈ P.physicalDirichletSource) (n : ℕ+) :
    P.physicalOnIndexSignedExponent q (-((n:ℕ):ℤ)) = I*P.physicalOnIndexAbelianCorrection n q := by
  change -I*Coeff.ofFunctionOrZero ⊤ _ (-((n:ℕ):ℤ)) = _
  rw [(P.physicalOnIndexOddSequence_data H).1 q hq,oddPositiveScalarExtension_neg,oddPositiveScalarExtension_apply]
  ring

theorem physicalOnIndexSignedExponent_zero_mode (P : HillProductEquationPatch)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots)
    (q : PeriodOneHminusOne) (hq : q ∈ P.physicalDirichletSource) :
    P.physicalOnIndexSignedExponent q 0=0 := by
  change -I*Coeff.ofFunctionOrZero ⊤ _ 0 = _
  rw [(P.physicalOnIndexOddSequence_data H).1 q hq,oddPositiveScalarExtension_zero,mul_zero]

theorem physicalOnIndexSignedExponent_zero_tail (P : HillProductEquationPatch)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots)
    (q : PeriodOneHminusOne) (hq : q ∈ P.physicalDirichletSource) :
    ∀ ε > (0:ℝ), ∃ K : ℕ, ∀ k : ℤ, K ≤ k.natAbs → ‖P.physicalOnIndexSignedExponent q k‖ ≤ ε := by
  intro ε hε
  obtain ⟨K,hK⟩ := P.physicalOnIndexAbelianCorrection_zero_tail H q hq ε hε
  refine ⟨K,?_⟩
  intro k hk
  by_cases hz : k=0
  · subst k
    rw [P.physicalOnIndexSignedExponent_zero_mode H q hq,norm_zero]
    exact hε.le
  · by_cases hp : 0 < k
    · let n : ℕ+ := ⟨k.toNat,by omega⟩
      have hn : ((n:ℕ):ℤ)=k := Int.toNat_of_nonneg hp.le
      rw [← hn,P.physicalOnIndexSignedExponent_positive H q hq]
      simp only [norm_mul,norm_neg,norm_I,one_mul]
      apply hK n
      simpa only [← hn,Int.natAbs_natCast] using hk
    · let n : ℕ+ := ⟨(-k).toNat,by omega⟩
      have hn : -((n:ℕ):ℤ)=k := by
        have h : ((n:ℕ):ℤ) = -k := Int.toNat_of_nonneg (by omega)
        omega
      rw [← hn,P.physicalOnIndexSignedExponent_negative H q hq]
      simp only [norm_mul,norm_I,one_mul]
      apply hK n
      simpa only [← hn,Int.natAbs_neg,Int.natAbs_natCast] using hk

end NLS.KdV.HillProductEquationPatch
