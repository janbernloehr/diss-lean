import NLS.KdV.HillAbelianWeightNormBound
import NLS.SequenceSpaces.UniformPositiveReciprocalSeries

/-! Locally uniform convergence of the ACTUAL physical off-index
correction. One open source neighborhood precedes ALL n, although the
convergence rate may depend on n. Finite low terms remain unchanged. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat NLS.LpSequence
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

def physicalOffIndexAbelianTerm (P : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) (m : ℕ+) : ℂ :=
  if m = n then 0 else P.physicalOffIndexAbelianValue n m q

def physicalOffIndexAbelianPartialSum (P : HillProductEquationPatch) (n : ℕ+)
    (N : ℕ) (q : PeriodOneHminusOne) : ℂ :=
  ∑ k ∈ Finset.Icc (-(N:ℤ)) N, positiveScalarExtension (P.physicalOffIndexAbelianTerm n q) k

def physicalOffIndexAbelianCorrection (P : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) : ℂ :=
  ∑' m : ℕ+, P.physicalOffIndexAbelianTerm n q m

theorem analytic_physicalOffIndexAbelianTerm (P : HillProductEquationPatch) (n m : ℕ+) :
    AnalyticOnNhd ℂ (fun q => P.physicalOffIndexAbelianTerm n q m) P.physicalDirichletSource := by
  by_cases hmn : m = n
  · simp only [physicalOffIndexAbelianTerm,if_pos hmn]
    exact analyticOnNhd_const
  · simp only [physicalOffIndexAbelianTerm,if_neg hmn]
    exact P.analytic_physicalOffIndexAbelianValue n m hmn

theorem analytic_physicalOffIndexAbelianPartialSum (P : HillProductEquationPatch) (n : ℕ+) (N : ℕ) :
    AnalyticOnNhd ℂ (P.physicalOffIndexAbelianPartialSum n N) P.physicalDirichletSource := by
  intro q hq
  apply Finset.analyticAt_fun_sum
  intro k _
  by_cases hk : k ∈ range positiveEmbedding
  · obtain ⟨m,rfl⟩ := hk
    change AnalyticAt ℂ (fun a => positiveScalarExtension (P.physicalOffIndexAbelianTerm n a) ((m:ℕ):ℤ)) q
    simpa only [positiveScalarExtension_apply] using P.analytic_physicalOffIndexAbelianTerm n m q hq
  · have he (a : PeriodOneHminusOne) : positiveScalarExtension (P.physicalOffIndexAbelianTerm n a) k = 0 :=
      positiveScalarExtension_zero_of_not_mem_range _ k hk
    simp only [he]
    exact analyticAt_const

theorem exists_local_uniform_physicalOffIndexAbelianCorrection (P : HillProductEquationPatch)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots)
    (q : PeriodOneHminusOne) (hq : q ∈ P.physicalDirichletSource) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q ∈ U ∧ U ⊆ P.physicalDirichletSource ∧
      ∀ n : ℕ+, TendstoUniformlyOn (P.physicalOffIndexAbelianPartialSum n)
        (P.physicalOffIndexAbelianCorrection n) atTop U := by
  obtain ⟨Ut,hUt,hqt,hUP,K,C,hC,hbound⟩ := P.exists_local_uniform_physicalOffIndexAbelianValue_tail_bound H q hq
  obtain ⟨Uw,hUw,hqw,_,R,_,hweights⟩ := P.exists_local_abelianWeight_norm_bound q hq.1
  refine ⟨Ut ∩ Uw,hUt.inter hUw,⟨hqt,hqw⟩,(fun a ha => hUP ha.1),?_⟩
  intro n
  apply Coeff.tendstoUniformlyOn_positive_series_of_signed_reciprocal_tail
    (fun a => sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (P.sourcePsi a))
    P.physicalAbelianMidpointDisplacement n (P.physicalOffIndexAbelianTerm n) (Ut ∩ Uw) K C R hC.le
  · intro a _
    simp [physicalOffIndexAbelianTerm]
  · intro a ha
    exact hweights a ha.2
  · intro a ha m hm hmn
    simpa only [physicalOffIndexAbelianTerm,if_neg hmn,P.physicalAbelianMidpointDisplacement_apply] using
      hbound a ha.1 n m hm hmn

end NLS.KdV.HillProductEquationPatch
