import NLS.Articles.KdVPseudomeasures.OriginalHillNativeJacobianInverse
import NLS.KdV.HillNativeRealDerivative
import NLS.SequenceSpaces.FourierRealZeroDecomposition
import NLS.FunctionalAnalysis.ComplexEquivRealForm
import NLS.FunctionalAnalysis.AnalyticEquivalenceInverse

/-! The actual physical REAL native map has an actual REAL derivative
Banach equivalence and genuine analytic local inverse at EVERY physical
source. The Fourier real forms, weights and mean-zero constraints are retained. -/
noncomputable section
open Set Complex Filter Topology NLS.KdV
namespace NLS.Articles.KdVPseudomeasures

/-- Restrict the actual complex Jacobian to the physical real Fourier forms. -/
def hillPhysicalNativeJacobianEquiv (q : HillRealMeanZeroSource) :
    HillRealMeanZeroSource ≃L[ℝ] HillRealSignedTarget :=
  NLS.FunctionalAnalysis.equivOfComplexEquivRealForm
    (WeightedCoeff.fourierRealZeroSubmodule (Weight.sobolev (-1)) 2)
    (WeightedCoeff.fourierRealZeroSubmodule (Weight.signedSobolev (-1/2)) 2)
    (WeightedCoeff.fourierRealZeroProjection (Weight.sobolev (-1)) (Weight.sobolev_neg (-1)))
    (WeightedCoeff.fourierRealZeroProjection (Weight.signedSobolev (-1/2)) (Weight.signedSobolev_neg (-1/2)))
    (WeightedCoeff.fourierRealZeroProjection_decomposition _ _)
    (WeightedCoeff.fourierRealZeroProjection_inclusion _ _)
    (WeightedCoeff.fourierRealZeroProjection_I_smul _ _)
    (hillRealNativeJacobianEquiv q) (fderiv ℝ hillRealSignedMap q)
    (fun h => (fderiv_hillRealSignedMap_coe q h).symm)

@[simp] theorem hillPhysicalNativeJacobianEquiv_toContinuousLinearMap (q : HillRealMeanZeroSource) :
    (hillPhysicalNativeJacobianEquiv q).toContinuousLinearMap=fderiv ℝ hillRealSignedMap q := rfl

/-- The inverse complex derivative itself preserves the physical real form. -/
theorem hillPhysicalNativeJacobianEquiv_symm_coe (q : HillRealMeanZeroSource) (z : HillRealSignedTarget) :
    ((hillPhysicalNativeJacobianEquiv q).symm z : HillMeanZeroSource)=
      (hillRealNativeJacobianEquiv q).symm (z : HillSignedComplexTarget) :=
  NLS.FunctionalAnalysis.equivOfComplexEquivRealForm_symm_coe _ _ _ _ _ _ _ _ _ _ z

/-- The actual physical real Jacobian is bijective at every physical source,
with no open-gap, inverse-derivative or range hypothesis. -/
theorem hillPhysicalNativeJacobian_bijective (q : HillRealMeanZeroSource) :
    Function.Bijective (fderiv ℝ hillRealSignedMap q) :=
  (hillPhysicalNativeJacobianEquiv q).bijective

/-- Both inverse identities hold in the correct physical real Banach norms. -/
theorem hillPhysicalNativeMap_localInverse (q : HillRealMeanZeroSource) :
    ∃ g : HillRealSignedTarget → HillRealMeanZeroSource,
      AnalyticAt ℝ g (hillRealSignedMap q) ∧ g (hillRealSignedMap q)=q ∧
      (∀ᶠ a in 𝓝 q, g (hillRealSignedMap a)=a) ∧
      (∀ᶠ z in 𝓝 (hillRealSignedMap q), hillRealSignedMap (g z)=z) ∧
      fderiv ℝ g (hillRealSignedMap q)=(hillPhysicalNativeJacobianEquiv q).symm.toContinuousLinearMap :=
  NLS.FunctionalAnalysis.exists_localInverse_of_equiv_fderiv
    (analyticAt_hillRealSignedMap q) (hillPhysicalNativeJacobianEquiv q)
    (hillPhysicalNativeJacobianEquiv_toContinuousLinearMap q).symm

/-- The physical real derivative equivalence in the original potential notation. -/
theorem original_Hill_physical_real_Jacobian_equivalence (q : OriginalHminusOnePotential) :
    ∃ e : HillRealMeanZeroSource ≃L[ℝ] HillRealSignedTarget,
      e.toContinuousLinearMap=fderiv ℝ hillRealSignedMap (originalHillRealMeanZeroSource q) :=
  ⟨hillPhysicalNativeJacobianEquiv (originalHillRealMeanZeroSource q),rfl⟩

/-- The all-source actual physical real analytic local inverse. -/
theorem original_Hill_physical_real_localInverse (q : OriginalHminusOnePotential) :
    ∃ g : HillRealSignedTarget → HillRealMeanZeroSource,
      AnalyticAt ℝ g (hillRealSignedMap (originalHillRealMeanZeroSource q)) ∧
      g (hillRealSignedMap (originalHillRealMeanZeroSource q))=originalHillRealMeanZeroSource q ∧
      (∀ᶠ a in 𝓝 (originalHillRealMeanZeroSource q), g (hillRealSignedMap a)=a) ∧
      (∀ᶠ z in 𝓝 (hillRealSignedMap (originalHillRealMeanZeroSource q)), hillRealSignedMap (g z)=z) ∧
      fderiv ℝ g (hillRealSignedMap (originalHillRealMeanZeroSource q))=
        (hillPhysicalNativeJacobianEquiv (originalHillRealMeanZeroSource q)).symm.toContinuousLinearMap :=
  hillPhysicalNativeMap_localInverse (originalHillRealMeanZeroSource q)

end NLS.Articles.KdVPseudomeasures
