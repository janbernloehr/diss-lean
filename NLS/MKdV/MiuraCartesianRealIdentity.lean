import NLS.MKdV.MiuraCartesianRealForm
import NLS.SequenceSpaces.PhysicalRealUnweightedDecomposition
import NLS.ComplexAnalysis.ContinuousRealFormIdentity

/-! # Holomorphic uniqueness from the genuine physical Cartesian real form -/
noncomputable section
open Set Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem miuraCartesianRealProjection_inclusion (z : MiuraPositiveCartesianTarget) :
    (miuraCartesianRealProjection z).val =
      miuraCartesianFreeJacobian (Coeff.physicalRealPart 2 (miuraCartesianFreeInverse z)).val := rfl

theorem miuraCartesianRealProjection_complex_decomp (z : MiuraPositiveCartesianTarget) :
    z = (miuraCartesianRealProjection z).val+I • (miuraCartesianRealProjection ((-I) • z)).val := by
  have h := congrArg miuraCartesianFreeJacobian
    (Coeff.physicalRealPart_complex_decomp 2 (miuraCartesianFreeInverse z))
  rw [miuraCartesianFreeJacobian_inverse,map_add,map_smul] at h
  rw [miuraCartesianRealProjection_inclusion,miuraCartesianRealProjection_inclusion,map_smul]
  exact h

/-- A Banach-valued holomorphic identity on the physical Cartesian slice
extends over any connected open complex domain meeting that slice. -/
theorem analytic_cartesian_eq_zero_of_physical_real
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (U : Set MiuraPositiveCartesianTarget) (hU : IsOpen U) (hconn : IsPreconnected U)
    (h0 : (0 : MiuraPositiveCartesianTarget) ∈ U) (f : MiuraPositiveCartesianTarget → F)
    (hf : AnalyticOnNhd ℂ f U)
    (hz : ∀ z ∈ U, z ∈ miuraCartesianRealSubmodule → f z = 0) : EqOn f 0 U := by
  let A : MiuraPositiveCartesianTarget →L[ℝ] MiuraPositiveCartesianTarget :=
    miuraCartesianRealSubmodule.subtypeL.comp miuraCartesianRealProjection
  let B : MiuraPositiveCartesianTarget →L[ℝ] MiuraPositiveCartesianTarget :=
    A.comp (((-I) • ContinuousLinearMap.id ℂ MiuraPositiveCartesianTarget).restrictScalars ℝ)
  apply AnalyticOnNhd.eqOn_zero_of_continuous_real_form
    (miuraCartesianRealSubmodule : Set MiuraPositiveCartesianTarget)
    (fun _ _ hx hy => miuraCartesianRealSubmodule.add_mem hx hy)
    (fun t x hx => by change t • x ∈ miuraCartesianRealSubmodule; exact miuraCartesianRealSubmodule.smul_mem t hx)
    A B (fun z => (miuraCartesianRealProjection z).property)
    (fun z => (miuraCartesianRealProjection ((-I) • z)).property)
    miuraCartesianRealProjection_complex_decomp A.continuous.continuousAt A.map_zero
    B.continuous.continuousAt B.map_zero U hU hconn ⟨0,h0,miuraCartesianRealSubmodule.zero_mem⟩ f hf hz

end NLS.MKdV
