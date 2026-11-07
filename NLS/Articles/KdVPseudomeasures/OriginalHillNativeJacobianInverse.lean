import NLS.Articles.KdVPseudomeasures.OriginalHillJacobianDenseRange
import NLS.KdV.HillNativeJacobianFredholm
import NLS.FunctionalAnalysis.CompactPerturbationDenseRange
import NLS.ComplexAnalysis.AnalyticEquivDerivativeInverse

/-! The ACTUAL native complex mean-zero derivative is a Banach
isomorphism at EVERY physical source, including all collapsed gaps.
The exact derivative gives a genuine analytic local inverse germ. -/
noncomputable section
open Set Complex Filter Topology NLS.KdV
namespace NLS.Articles.KdVPseudomeasures

/-- The full actual native Jacobian is bijective at every physical source. -/
theorem hillRealNativeJacobian_bijective (q : HillRealMeanZeroSource) :
    Function.Bijective (fderiv ℂ hillMeanZeroComplexMap q.val) :=
  CompactSpectrum.bijective_of_compact_sub_equiv_denseRange
    (hillMeanZeroJacobianReference q.val) (fderiv ℂ hillMeanZeroComplexMap q.val)
    (isCompactOperator_hillMeanZeroJacobian_sub_reference q.val q.property)
    (hillRealNativeJacobian_denseRange q)

/-- The constructed equivalence is the actual native derivative between
the original complex Hminus-one source and signed minus-half target. -/
def hillRealNativeJacobianEquiv (q : HillRealMeanZeroSource) : HillMeanZeroSource ≃L[ℂ] HillSignedComplexTarget :=
  CompactSpectrum.equivOfCompactDenseRange (hillMeanZeroJacobianReference q.val)
    (fderiv ℂ hillMeanZeroComplexMap q.val)
    (isCompactOperator_hillMeanZeroJacobian_sub_reference q.val q.property)
    (hillRealNativeJacobian_denseRange q)

@[simp] theorem hillRealNativeJacobianEquiv_toContinuousLinearMap (q : HillRealMeanZeroSource) :
    (hillRealNativeJacobianEquiv q).toContinuousLinearMap=fderiv ℂ hillMeanZeroComplexMap q.val := rfl

/-- The original potential supplies an actual derivative Banach equivalence,
without an inverse, closed-range or positive-gap hypothesis. -/
theorem original_Hill_native_Jacobian_equivalence (q : OriginalHminusOnePotential) :
    ∃ e : HillMeanZeroSource ≃L[ℂ] HillSignedComplexTarget,
      e.toContinuousLinearMap=fderiv ℂ hillMeanZeroComplexMap (originalHillRealMeanZeroSource q).val :=
  ⟨hillRealNativeJacobianEquiv (originalHillRealMeanZeroSource q),rfl⟩

/-- Both inverse identities hold on full complex neighborhoods at every
physical source, with derivative equal to the true inverse Jacobian. -/
theorem hillRealNativeMap_localInverse (q : HillRealMeanZeroSource) :
    ∃ g : HillSignedComplexTarget → HillMeanZeroSource,
      AnalyticAt ℂ g (hillMeanZeroComplexMap q.val) ∧
      g (hillMeanZeroComplexMap q.val)=q.val ∧
      (∀ᶠ a in 𝓝 q.val, g (hillMeanZeroComplexMap a)=a) ∧
      (∀ᶠ z in 𝓝 (hillMeanZeroComplexMap q.val), hillMeanZeroComplexMap (g z)=z) ∧
      fderiv ℂ g (hillMeanZeroComplexMap q.val)=(hillRealNativeJacobianEquiv q).symm.toContinuousLinearMap :=
  NLS.ComplexAnalysis.exists_localInverse_of_equiv_fderiv
    (analyticOnNhd_hillMeanZeroComplexMap q.val (real_mem_hillMeanZeroComplexDomain q.val q.property))
    (hillRealNativeJacobianEquiv q) (hillRealNativeJacobianEquiv_toContinuousLinearMap q).symm

/-- The all-source actual complex local inverse in the original physical notation. -/
theorem original_Hill_native_localInverse (q : OriginalHminusOnePotential) :
    ∃ g : HillSignedComplexTarget → HillMeanZeroSource,
      AnalyticAt ℂ g (hillMeanZeroComplexMap (originalHillRealMeanZeroSource q).val) ∧
      g (hillMeanZeroComplexMap (originalHillRealMeanZeroSource q).val)=(originalHillRealMeanZeroSource q).val ∧
      (∀ᶠ a in 𝓝 (originalHillRealMeanZeroSource q).val, g (hillMeanZeroComplexMap a)=a) ∧
      (∀ᶠ z in 𝓝 (hillMeanZeroComplexMap (originalHillRealMeanZeroSource q).val), hillMeanZeroComplexMap (g z)=z) ∧
      fderiv ℂ g (hillMeanZeroComplexMap (originalHillRealMeanZeroSource q).val)=
        (hillRealNativeJacobianEquiv (originalHillRealMeanZeroSource q)).symm.toContinuousLinearMap :=
  hillRealNativeMap_localInverse (originalHillRealMeanZeroSource q)

end NLS.Articles.KdVPseudomeasures
