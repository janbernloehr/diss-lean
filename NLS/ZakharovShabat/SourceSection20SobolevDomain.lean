import NLS.ComplexAnalysis.DenseLinearConnectedPreimage
import NLS.ComplexAnalysis.AnalyticNonzeroConnected
import NLS.ZakharovShabat.SourceSection20SobolevEnergy
import NLS.ZakharovShabat.SourceSection18HamiltonianCorrection

/-! # Connected complex H¹ open-gap domains for the original Section 20 family

The dense H¹ inclusion lifts the connected original source domain. The
squared gap is analytic there, so removing its zero locus preserves
connectedness. A real single-action source supplies a nonzero witness for
every index. No index-dependent shrinking of the source domain is needed.
-/
noncomputable section
open Set Filter Topology
namespace NLS.ZakharovShabat

/-- The physical H¹ source inclusion has dense range in the Hilbert source space. -/
theorem sobolevSourceInclusion_denseRange : DenseRange sobolevSourceInclusion :=
  (CoeffPair.toMax 2).symm.surjective.denseRange.comp
    ((scalarInclusion_denseRange (p := 2) (by simp)).prodMap
      (scalarInclusion_denseRange (p := 2) (by simp))) (CoeffPair.toMax 2).symm.continuous

/-- The H¹ part of a source domain with one selected periodic gap open. -/
def sourceSobolevOpenGapDomain (U : Set (CoeffPair 2)) (n : ℤ) :
    Set (ScalarDomain 2 × ScalarDomain 2) :=
  {a | sobolevSourceInclusion a ∈ U ∧ canonicalPeriodicGap (by simp) (by norm_num)
    (periodOnePotential (sobolevSourceInclusion a)) (periodOnePotential_mem _) n ≠ 0}

/-- A real H¹ source with any selected open gap exists without supplied spectral witnesses. -/
theorem exists_realSobolev_open_gap (n : ℤ) :
    ∃ a : realTypeSobolevSourceLocus, canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (sobolevSourceInclusion a.val)) (periodOnePotential_mem _) n ≠ 0 := by
  obtain ⟨a,ha,_,_⟩ := exists_realSobolev_single_action n 1 (by norm_num)
  refine ⟨a,?_⟩
  intro hz
  have hact := (sourceComplexAction_nonneg_and_eq_zero_iff_gap_zero (by simp) (by norm_num)
    n (sobolevSourceInclusion a.val) a.property).2.2.mpr
    (by simpa only [sourcePeriodicGapDisplacement_apply] using hz)
  rw [ha n] at hact
  norm_num at hact

namespace SourceSection20Data
variable {W₀ W V Wa B U : Set (CoeffPair 2)}
  {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
  {D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s}
  {A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa s}
  (Q : SourceSection20Data D A B U)
include Q

/-- The whole complex H¹ preimage of the original source domain is connected. -/
theorem isConnected_sobolev_domain : IsConnected (sobolevSourceInclusion ⁻¹' U) :=
  NLS.ComplexAnalysis.isConnected_preimage_dense_linear
    (sobolevSourceInclusion.restrictScalars ℝ).toLinearMap
    sobolevSourceInclusion_denseRange Q.source_open Q.connected

/-- The actual squared periodic gap is analytic on the original complex H¹ domain. -/
theorem analyticOnNhd_sobolev_squaredGap (n : ℤ) :
    AnalyticOnNhd ℂ (fun a : ScalarDomain 2 × ScalarDomain 2 =>
      (canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential (sobolevSourceInclusion a))
        (periodOnePotential_mem _) n)^2) (sobolevSourceInclusion ⁻¹' U) := by
  intro a ha
  have E := D.previous.original_theta_common_domain
  exact ((E.symmetric_analytic _ (E.source_subset (D.complex.source_subset (Q.original_subset ha))) n).2).comp
    (sobolevSourceInclusion.analyticAt a)

/-- The full original H¹ open-gap domain is open, including nonreal sources. -/
theorem isOpen_sobolev_openGapDomain (n : ℤ) : IsOpen (sourceSobolevOpenGapDomain U n) := by
  have hU : IsOpen (sobolevSourceInclusion ⁻¹' U) := Q.source_open.preimage sobolevSourceInclusion.continuous
  have he : sourceSobolevOpenGapDomain U n = {a ∈ sobolevSourceInclusion ⁻¹' U |
      (canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential (sobolevSourceInclusion a))
        (periodOnePotential_mem _) n)^2 ≠ 0} := by
    ext a
    simp [sourceSobolevOpenGapDomain]
  rw [he]
  exact (Q.analyticOnNhd_sobolev_squaredGap n).continuousOn.isOpen_inter_preimage hU isOpen_compl_singleton

/-- Removing the collapsed selected gap leaves the full original complex H¹ domain connected. -/
theorem isConnected_sobolev_openGapDomain (n : ℤ) : IsConnected (sourceSobolevOpenGapDomain U n) := by
  obtain ⟨a,hn⟩ := exists_realSobolev_open_gap n
  have hc := NLS.ComplexAnalysis.isConnected_analytic_nonzero
    (Q.source_open.preimage sobolevSourceInclusion.continuous) Q.isConnected_sobolev_domain
    _ (Q.analyticOnNhd_sobolev_squaredGap n) a.val (Q.real_subset a.property) (pow_ne_zero 2 hn)
  simpa only [sourceSobolevOpenGapDomain,ne_eq,pow_eq_zero_iff (by decide : 2 ≠ 0)] using! hc

end SourceSection20Data
end NLS.ZakharovShabat
