import NLS.KdV.HillMiuraLinearizationKernel
import NLS.FunctionalAnalysis.CompactPerturbationInjectiveInverse
import NLS.FunctionalAnalysis.LocalInverseFixedPoints
import NLS.ComplexAnalysis.AnalyticEquivDerivativeInverse

/-! At every physical real L2 lift with NONZERO raw mean, the actual
Miura linearization is a complex Banach equivalence and the true analytic
local inverse preserves physical reality. Original norms are unchanged. -/
noncomputable section
open Set Complex Filter Topology NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.KdV

def realMeanNonzeroMiuraLinearizationEquiv (u : PeriodOneRealL2) (hu : u.val 0 ≠ 0) :
    Coeff 2 ≃L[ℂ] PeriodOneHminusOne :=
  CompactSpectrum.equivOfInjectiveCompactDifference (periodOneMassEquiv 0)
    (periodOneMiuraLinearization u.val) (isCompactOperator_periodOneMiuraLinearization_sub_mass u.val)
    (periodOneMiuraLinearization_injective_of_real_mean_ne_zero u hu)

theorem periodOneMiura_realConjugation (u : Coeff 2) :
    periodOneMiura (coeffRealConjugation u)=
      WeightedCoeff.conjugateReflection (Weight.sobolev (-1)) (Weight.sobolev_neg (-1)) (periodOneMiura u) := by
  apply Subtype.ext
  funext k
  rw [WeightedCoeff.conjugateReflection_apply]
  change (periodOneShiftedMiura 0 (coeffRealConjugation u)).val k-
    (periodOneL2Inclusion (coeffRealConjugation u)).val k=
      conj ((periodOneShiftedMiura 0 u).val (-k)-(periodOneL2Inclusion u).val (-k))
  rw [periodOneShiftedMiura_realConjugation,WeightedCoeff.conjugateReflection_apply,
    map_sub,periodOneL2Inclusion_apply,periodOneL2Inclusion_apply,coeffRealConjugation_apply]

theorem exists_real_preserving_localInverse_periodOneMiura
    (u : PeriodOneRealL2) (hu : u.val 0 ≠ 0) :
    ∃ g : PeriodOneHminusOne → Coeff 2,
      AnalyticAt ℂ g (periodOneMiura u.val) ∧ g (periodOneMiura u.val)=u.val ∧
      (∀ᶠ v in 𝓝 u.val, g (periodOneMiura v)=v) ∧
      (∀ᶠ p in 𝓝 (periodOneMiura u.val), periodOneMiura (g p)=p) ∧
      (∀ᶠ p in 𝓝 (periodOneMiura u.val), IsRealPeriodOneHminusOne p →
        ∀ k : ℤ, g p (-k)=conj (g p k)) := by
  have ha : AnalyticAt ℂ periodOneMiura u.val :=
    (analyticAt_periodOneShiftedMiura 0 u.val).sub (periodOneL2Inclusion.analyticAt u.val)
  obtain ⟨g,hg,hbase,hleft,hright,_⟩ := ComplexAnalysis.exists_localInverse_of_equiv_fderiv
    ha (realMeanNonzeroMiuraLinearizationEquiv u hu) (fderiv_periodOneMiura u.val)
  have hcon : Continuous coeffRealConjugation := continuous_star.comp Coeff.reflection.continuous
  have hfix : coeffRealConjugation u.val=u.val := by
    ext k
    rw [coeffRealConjugation_apply,u.property,conj_conj]
  have ht : Tendsto g (𝓝 (periodOneMiura u.val)) (𝓝 u.val) := by
    simpa only [hbase] using hg.continuousAt.tendsto
  have hp := NLS.FunctionalAnalysis.eventually_localInverse_fixedPoints periodOneMiura g coeffRealConjugation
    (WeightedCoeff.conjugateReflection (Weight.sobolev (-1)) (Weight.sobolev_neg (-1))) u.val
    hcon.continuousAt hfix periodOneMiura_realConjugation ht hleft hright
  refine ⟨g,hg,hbase,hleft,hright,?_⟩
  filter_upwards [hp] with p hp hreal
  have he := hp (periodOne_realConjugation_eq_self p hreal)
  intro k
  have hh := congrArg (fun v : Coeff 2 => v (-k)) he
  simpa only [coeffRealConjugation_apply,neg_neg] using hh.symm

end NLS.KdV
