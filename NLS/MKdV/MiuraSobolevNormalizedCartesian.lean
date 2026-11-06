import NLS.MKdV.MiuraSobolevCartesianAnalyticInverse
import NLS.MKdV.MiuraGeneralCartesianComplexInverse

/-! # Native Sobolev Cartesian charts in a fixed normalized target

Weight transport identifies the native order-(s+1/2) target with the
fixed half-order target. Complex inverse germs preserve the physical
real form by comparison with the proved global real native inverse.
-/
noncomputable section
open Set Complex Filter Topology NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

def miuraSobolevNormalizedCartesianMap (s : ℕ) (a : ScalarSobolev s) : MiuraPositiveCartesianTarget :=
  miuraPositiveSobolevWeightEquiv s (miuraSobolevPositiveCartesianMap s a)

theorem analyticAt_miuraSobolevNormalizedCartesianMap (s : ℕ) (a : ScalarSobolev s)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    AnalyticAt ℂ (miuraSobolevNormalizedCartesianMap s) a :=
  ((miuraPositiveSobolevWeightEquiv s).analyticAt _).comp
    (analyticAt_miuraSobolevPositiveCartesianMap s a ha)

def miuraPhysicalSobolevNormalizedCartesianMap (s : ℕ) (a : MiuraRealSobolevSource s) : MiuraRealCartesianTarget :=
  miuraSobolevCartesianRealWeightEquiv s (miuraPhysicalSobolevCartesianMap s a)

theorem miuraPhysicalSobolevNormalizedCartesianMap_inclusion (s : ℕ) (a : MiuraRealSobolevSource s) :
    (miuraPhysicalSobolevNormalizedCartesianMap s a).val = miuraSobolevNormalizedCartesianMap s a.val := by
  change miuraPositiveSobolevWeightEquiv s (miuraPhysicalSobolevCartesianMap s a).val = _
  rw [miuraPhysicalSobolevCartesianMap_inclusion]
  rfl

theorem miuraSobolevNormalizedCartesianMap_real (s : ℕ) (a : MiuraRealSobolevSource s) :
    miuraSobolevNormalizedCartesianMap s a.val ∈ miuraCartesianRealSubmodule := by
  rw [← miuraPhysicalSobolevNormalizedCartesianMap_inclusion]
  exact (miuraPhysicalSobolevNormalizedCartesianMap s a).property

theorem exists_miuraSobolevNormalizedCartesian_analytic_chart (s : ℕ) (hs : 1 ≤ s)
    (a : MiuraRealSobolevSource s) :
    ∃ P : OpenPartialHomeomorph (ScalarSobolev s) MiuraPositiveCartesianTarget,
      (P : ScalarSobolev s → MiuraPositiveCartesianTarget) = miuraSobolevNormalizedCartesianMap s ∧
      a.val ∈ P.source ∧ AnalyticOnNhd ℂ (miuraSobolevNormalizedCartesianMap s) P.source ∧
        AnalyticOnNhd ℂ P.symm P.target := by
  obtain ⟨L,hL⟩ := exists_miuraSobolevCartesian_derivative_equiv s hs a.val a.property
  let E := miuraPositiveSobolevWeightEquiv s
  let A := L.trans E
  have hd := E.toContinuousLinearMap.hasFDerivAt.comp a.val
    (analyticAt_miuraSobolevPositiveCartesianMap s a.val a.property).differentiableAt.hasFDerivAt
  have he : fderiv ℂ (miuraSobolevNormalizedCartesianMap s) a.val = A.toContinuousLinearMap := by
    change HasFDerivAt (miuraSobolevNormalizedCartesianMap s) _ a.val at hd
    rw [hd.fderiv,← hL]
    rfl
  exact exists_analytic_openPartialHomeomorph_of_fderiv_equiv
    (analyticAt_miuraSobolevNormalizedCartesianMap s a.val a.property) A he

theorem miuraSobolevNormalizedCartesian_inverse_real_germ (s : ℕ) (hs : 1 ≤ s)
    (a : MiuraRealSobolevSource s) (g : MiuraPositiveCartesianTarget → ScalarSobolev s)
    (hl : ∀ᶠ b in 𝓝 a.val, g (miuraSobolevNormalizedCartesianMap s b) = b) :
    ∀ᶠ z in 𝓝 (miuraPhysicalSobolevNormalizedCartesianMap s a),
      g z.val ∈ MiuraRealSobolevSource s := by
  let E := miuraSobolevCartesianRealWeightEquiv s
  let gR : MiuraRealCartesianTarget → MiuraRealSobolevSource s :=
    fun z => miuraPhysicalSobolevCartesianInverse s hs (E.symm z)
  have hc : ContinuousAt gR (miuraPhysicalSobolevNormalizedCartesianMap s a) := by
    exact (analyticOnNhd_miuraPhysicalSobolevCartesianInverse s hs _ (mem_univ _)).continuousAt.comp
      E.symm.continuous.continuousAt
  have hbase : gR (miuraPhysicalSobolevNormalizedCartesianMap s a) = a := by
    change miuraPhysicalSobolevCartesianInverse s hs (E.symm (E (miuraPhysicalSobolevCartesianMap s a))) = a
    rw [ContinuousLinearEquiv.symm_apply_apply,miuraPhysicalSobolevCartesianInverse_map]
  have hr : ∀ᶠ z in 𝓝 (miuraPhysicalSobolevNormalizedCartesianMap s a),
      miuraPhysicalSobolevNormalizedCartesianMap s (gR z) = z := by
    apply Filter.Eventually.of_forall
    intro z
    change E (miuraPhysicalSobolevCartesianMap s (miuraPhysicalSobolevCartesianInverse s hs (E.symm z))) = z
    rw [miuraPhysicalSobolevCartesianMap_inverse,ContinuousLinearEquiv.apply_symm_apply]
  exact inverse_germ_preserves_subspace
    (fun v : MiuraRealSobolevSource s => v.val) continuous_subtype_val
    (fun z : MiuraRealCartesianTarget => z.val) (miuraSobolevNormalizedCartesianMap s)
    (miuraPhysicalSobolevNormalizedCartesianMap s) a g gR hc hbase hl hr
    (miuraPhysicalSobolevNormalizedCartesianMap_inclusion s)
    (fun v => v ∈ MiuraRealSobolevSource s) (fun v => v.property)

end NLS.MKdV
