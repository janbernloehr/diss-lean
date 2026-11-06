import NLS.MKdV.MiuraHillPhysicalTraceComparison
import NLS.MKdV.MiuraHillHamiltonianTrace
import NLS.KdV.ClassicalHillPrimitiveReflection

/-! # The physical Miura IVP and the shared scalar Hill discriminant

The identification uses uniqueness of the actual position/derivative state
equation. It therefore includes zero energy and does not assume equality of
spectral objects as a hypothesis. The continuous Hill potential may agree
with the physical Miura potential only almost everywhere.
-/
noncomputable section
open Set Complex Filter Topology MeasureTheory NLS.LinearVolterra
open NLS.FunctionalAnalysis NLS.KdV NLS.ZakharovShabat
open scoped ContDiff
namespace NLS.MKdV

end NLS.MKdV
