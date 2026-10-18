import NLS.ZakharovShabat.SourcePhysicalActionAngle

/-! # Complex extension on the original physical Hilbert space

The full sequence map extends analytically to an open physical L2
neighborhood of the real form. Its real restriction agrees exactly with
the global physical action-angle homeomorphism, and its complex action
radii retain the original indexed actions.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- A physical complex neighborhood obtained from the exact Hilbert Fourier equivalence. -/
def physicalBirkhoffDomain (V : Set (CoeffPair 2)) : Set IntervalPairL2 :=
  sourcePhysicalL2Equiv.symm ⁻¹' V

/-- The full complex map in the native Hilbert pair norm. -/
def physicalBirkhoffMap (s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n)
    (u : IntervalPairL2) : CoeffPair 2 :=
  WithLp.toLp 2 (sourceBirkhoffMap (by simp) (by norm_num) s (sourcePhysicalL2Equiv.symm u))

/-- Complex inclusion of the native real Hilbert target preserves all coordinates. -/
def physicalRealTargetComplex : PhysicalRealBirkhoffTarget →L[ℝ] CoeffPair 2 :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (Coeff 2) (Coeff 2)).symm.toContinuousLinearMap.comp
    (((RealCoeff.complexCLM 2).prodMap (RealCoeff.complexCLM 2)).comp
      physicalRealTargetEquiv.toContinuousLinearMap)

namespace SourceSection14OriginalData
variable {W₀ W V : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
  (D : SourceSection14OriginalData (by simp) (by norm_num) W₀ W V s)

include D in
/-- The complex physical domain is open in the original L2 topology. -/
theorem physicalBirkhoffDomain_open : IsOpen (physicalBirkhoffDomain V) :=
  D.complex.source_open.preimage sourcePhysicalL2Equiv.symm.continuous

include D in
/-- The complex domain contains every real physical L2 source. -/
theorem physicalBirkhoffDomain_real (u : physicalRealSubmodule) : u.val ∈ physicalBirkhoffDomain V :=
  D.complex.real_subset u.property

include D in
/-- The full complex map is analytic in the original physical source and target Hilbert norms. -/
theorem physicalBirkhoffMap_analytic : AnalyticOnNhd ℂ (physicalBirkhoffMap s) (physicalBirkhoffDomain V) := by
  intro u hu
  exact ((WithLp.prodContinuousLinearEquiv 2 ℂ (Coeff 2) (Coeff 2)).symm.analyticAt _).comp
    ((D.complex.analytic _ hu).comp (sourcePhysicalL2Equiv.symm.toContinuousLinearEquiv.analyticAt u))

/-- The complex physical map extends the global real action-angle homeomorphism. -/
theorem physicalBirkhoffMap_real (u : physicalRealSubmodule) :
    physicalRealTargetComplex (D.physicalRealActionAngleHomeomorph u) = physicalBirkhoffMap s u.val := by
  apply WithLp.ofLp_injective
  change ((RealCoeff.complexCLM 2).prodMap (RealCoeff.complexCLM 2))
    (D.realActionAngleMap (realSourcePhysicalL2Equiv.symm u)) = _
  rw [D.realActionAngleMap_eq]
  exact D.complex.real_map_complex_inclusion (realSourcePhysicalL2Equiv.symm u)

include D in
/-- The exact indexed-action radius holds for every complex input in the physical domain. -/
theorem physicalBirkhoffMap_action_radius (u : IntervalPairL2) (hu : u ∈ physicalBirkhoffDomain V) (n : ℤ) :
    (physicalBirkhoffMap s u).fst n ^ 2 + (physicalBirkhoffMap s u).snd n ^ 2 =
      2*physicalIndexedAction n u := D.indexed_action_radius _ hu n

end SourceSection14OriginalData

end NLS.ZakharovShabat
