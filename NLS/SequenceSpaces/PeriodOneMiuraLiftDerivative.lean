import NLS.SequenceSpaces.PeriodOneMiuraCompactDerivative
import NLS.FunctionalAnalysis.CompactPerturbationRightInverse
import NLS.ComplexAnalysis.AnalyticEquivDerivativeInverse

/-! Every actual analytic local Miura lift has a derivative which is a
Banach equivalence. Its inverse is the literal distributional Miura
linearization, and it differs compactly from the explicit massive inverse.
Only the actual local Miura identity is used, with a fixed energy shift. -/
noncomputable section
open Filter Topology
namespace NLS

theorem periodOneMiuraLinearization_comp_fderiv_lift
    (u : PeriodOneHminusOne → Coeff 2) (c q : PeriodOneHminusOne)
    (hu : AnalyticAt ℂ u q)
    (he : (fun a => periodOneMiura (u a)) =ᶠ[𝓝 q] (fun a => a+c)) :
    (periodOneMiuraLinearization (u q)).comp (fderiv ℂ u q)=
      ContinuousLinearMap.id ℂ PeriodOneHminusOne := by
  have hd := (hasFDerivAt_periodOneMiura (u q)).comp q hu.differentiableAt.hasFDerivAt
  have hi : HasFDerivAt (fun a : PeriodOneHminusOne => a+c)
      (ContinuousLinearMap.id ℂ PeriodOneHminusOne) q := (hasFDerivAt_id q).add_const c
  exact hd.fderiv.symm.trans (he.fderiv_eq.trans hi.fderiv)

def periodOneMiuraLiftDerivativeEquiv
    (u : PeriodOneHminusOne → Coeff 2) (c q : PeriodOneHminusOne)
    (hu : AnalyticAt ℂ u q)
    (he : (fun a => periodOneMiura (u a)) =ᶠ[𝓝 q] (fun a => a+c)) :
    PeriodOneHminusOne ≃L[ℂ] Coeff 2 :=
  (CompactSpectrum.equivOfCompactRightInverse (periodOneMassEquiv 0)
    (periodOneMiuraLinearization (u q)) (fderiv ℂ u q)
    (isCompactOperator_periodOneMiuraLinearization_sub_mass (u q))
    (periodOneMiuraLinearization_comp_fderiv_lift u c q hu he)).symm

theorem periodOneMiuraLiftDerivativeEquiv_toCLM
    (u : PeriodOneHminusOne → Coeff 2) (c q : PeriodOneHminusOne)
    (hu : AnalyticAt ℂ u q)
    (he : (fun a => periodOneMiura (u a)) =ᶠ[𝓝 q] (fun a => a+c)) :
    (periodOneMiuraLiftDerivativeEquiv u c q hu he).toContinuousLinearMap=fderiv ℂ u q := rfl

theorem periodOneMiuraLiftDerivativeEquiv_symm_toCLM
    (u : PeriodOneHminusOne → Coeff 2) (c q : PeriodOneHminusOne)
    (hu : AnalyticAt ℂ u q)
    (he : (fun a => periodOneMiura (u a)) =ᶠ[𝓝 q] (fun a => a+c)) :
    (periodOneMiuraLiftDerivativeEquiv u c q hu he).symm.toContinuousLinearMap=
      periodOneMiuraLinearization (u q) := rfl

theorem fderiv_lift_comp_periodOneMiuraLinearization
    (u : PeriodOneHminusOne → Coeff 2) (c q : PeriodOneHminusOne)
    (hu : AnalyticAt ℂ u q)
    (he : (fun a => periodOneMiura (u a)) =ᶠ[𝓝 q] (fun a => a+c)) :
    (fderiv ℂ u q).comp (periodOneMiuraLinearization (u q))=
      ContinuousLinearMap.id ℂ (Coeff 2) := by
  apply ContinuousLinearMap.ext
  intro h
  exact (periodOneMiuraLiftDerivativeEquiv u c q hu he).apply_symm_apply h

theorem isCompactOperator_fderiv_Miura_lift_sub_massInverse
    (u : PeriodOneHminusOne → Coeff 2) (c q : PeriodOneHminusOne)
    (hu : AnalyticAt ℂ u q)
    (he : (fun a => periodOneMiura (u a)) =ᶠ[𝓝 q] (fun a => a+c)) :
    IsCompactOperator (fderiv ℂ u q-periodOneMassInverse 0) :=
  CompactSpectrum.isCompactOperator_rightInverse_sub_equiv_inverse (periodOneMassEquiv 0)
    (periodOneMiuraLinearization (u q)) (fderiv ℂ u q)
    (isCompactOperator_periodOneMiuraLinearization_sub_mass (u q))
    (periodOneMiuraLinearization_comp_fderiv_lift u c q hu he)

theorem eventually_Miura_lift_left_inverse
    (u : PeriodOneHminusOne → Coeff 2) (c q : PeriodOneHminusOne)
    (hu : AnalyticAt ℂ u q)
    (he : (fun a => periodOneMiura (u a)) =ᶠ[𝓝 q] (fun a => a+c)) :
    ∀ᶠ v in 𝓝 (u q), u (periodOneMiura v-c)=v := by
  let e := periodOneMiuraLiftDerivativeEquiv u c q hu he
  obtain ⟨g,hg,hgq,_,hr,_⟩ := ComplexAnalysis.exists_localInverse_of_equiv_fderiv hu e rfl
  have hgc : Tendsto g (𝓝 (u q)) (𝓝 q) := by
    simpa only [hgq] using hg.continuousAt.tendsto
  have hcomp := hgc.eventually he
  filter_upwards [hr,hcomp] with v hv hidentity
  change periodOneMiura (u (g v))=g v+c at hidentity
  rw [hv] at hidentity
  have hgv : g v=periodOneMiura v-c := by rw [hidentity]; abel
  rw [← hgv]
  exact hv

end NLS
