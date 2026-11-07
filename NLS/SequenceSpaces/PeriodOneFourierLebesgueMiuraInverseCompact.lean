import NLS.SequenceSpaces.PeriodOneFourierLebesgueMiuraJacobian
import NLS.FunctionalAnalysis.CompactRightInverseBetweenSpaces

/-! # Compact free remainders of the SAME actual native Miura inverse germ -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS

theorem isCompactOperator_fderiv_fourierLebesgueMiura_rightInverse_sub_free
    (s p : ℝ) (hs : -1/2≤s) (hp : 2<p) [Fact (1≤ENNReal.ofReal p)]
    (g : WeightedCoeff (Weight.sobolev s) (ENNReal.ofReal p) →
      WeightedCoeff (Weight.sobolev (s+1)) (ENNReal.ofReal p))
    (q k : WeightedCoeff (Weight.sobolev s) (ENNReal.ofReal p)) (hg : DifferentiableAt ℂ g q)
    (he : (fun x => periodOneFourierLebesgueMiura s p hs hp (g x)) =ᶠ[𝓝 q] (fun x => x+k)) :
    IsCompactOperator (fderiv ℂ g q-
      (periodOneFourierLebesgueFreeMassEquiv 0 s (ENNReal.ofReal p)).symm.toContinuousLinearMap) := by
  have hright : (periodOneFourierLebesgueMiuraJacobian s p hs hp (g q)).comp (fderiv ℂ g q)=
      ContinuousLinearMap.id ℂ (WeightedCoeff (Weight.sobolev s) (ENNReal.ofReal p)) :=
    (((hasFDerivAt_periodOneFourierLebesgueMiura s p hs hp (g q)).comp q hg.hasFDerivAt).congr_of_eventuallyEq he.symm).unique ((hasFDerivAt_id q).add_const k)
  exact isCompactOperator_rightInverse_sub_equiv_symm _ _
    (periodOneFourierLebesgueFreeMassEquiv 0 s (ENNReal.ofReal p))
    (isCompactOperator_periodOneFourierLebesgueMiuraJacobian_sub_free s p hs hp (g q)) hright

end NLS
