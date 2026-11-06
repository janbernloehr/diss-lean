import NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianNativeGerms
import NLS.KdV.HillHminusPhysicalGermDifferentials
import NLS.KdV.HillHminusActionHamiltonianVector

/-! # Actual original actions as genuine analytic rough germs

The literal global signed products recover the original physical Hill gap
integrals. Physical germ uniqueness identifies their full original even L2
differentials and their actual rough Gardner Hamiltonian vectors.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.KdV
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

/-- The original positive action as a literal product of the SAME signed map. -/
def roughActionCoordinate (D : GlobalRoughAbelianForwardData) (n : ℕ+)
    (q : PeriodOneHminusOne) : ℂ :=
  (D.signed q).val (n : ℤ)*(D.signed q).val (-(n : ℤ))

/-- The scalar original action is complex analytic on the actual global rough domain. -/
theorem roughActionCoordinate_analytic (D : GlobalRoughAbelianForwardData) (n : ℕ+) :
    AnalyticOnNhd ℂ (D.roughActionCoordinate n) D.domain := by
  intro q hq
  have hs := D.signed_analytic q hq
  exact (((WeightedCoeff.evalCLM (Weight.sobolev (-1/2)) 2 (n : ℤ)).analyticAt _).comp hs).mul
    (((WeightedCoeff.evalCLM (Weight.sobolev (-1/2)) 2 (-(n : ℤ))).analyticAt _).comp hs)

/-- All physical original sources, including all collapsed gaps, have the
actual real-gap action integral with its original normalization. -/
theorem roughActionCoordinate_physical (D : GlobalRoughAbelianForwardData)
    (q : RealPeriodOneHillPotential) (n : ℕ+) :
    D.roughActionCoordinate n (hillOriginalHminusSource q.val) =
      (hillRealGapIntegral q.val q.property.1 q.property.2 n 0 : ℂ) := by
  rw [roughActionCoordinate,hillOriginalHminusSource_eq_physical,D.signed_physical,D.signed_physical]
  have he := hillPhysicalAbelianMap_action SpectralWeight.one (hillUnitRealSourceUnembed q) n n.pos
  have hq := congrArg (fun p : RealPeriodOneHillPotential =>
    hillRealGapIntegral p.val p.property.1 p.property.2 n 0) (hillRealWeightedEmbedding_unitUnembed q)
  change hillPeriodOneAction SpectralWeight.one (hillUnitRealSourceUnembed q).val
    (hillUnitRealSourceUnembed q).property n = hillRealGapIntegral q.val q.property.1 q.property.2 n 0 at hq
  simpa only [hillPhysicalAbelianMap,hillAbelianCoordinateSequence_apply,hq] using! he

/-- No regularity or gap-opening assumption is needed for the actual rough action germ. -/
theorem analyticAt_roughActionCoordinate_physical (D : GlobalRoughAbelianForwardData)
    (q : RealPeriodOneHillPotential) (n : ℕ+) :
    AnalyticAt ℂ (D.roughActionCoordinate n) (hillOriginalHminusSource q.val) :=
  D.roughActionCoordinate_analytic n _ (D.real_mem_domain _
    (hillOriginalHminusSource_real q.val q.property.2))

/-- ANY actual matching physical L2 action germ has the SAME original even
physical differential as the globally fixed rough signed product. -/
theorem roughActionCoordinate_fderiv_original (D : GlobalRoughAbelianForwardData)
    (q : RealPeriodOneHillPotential) (n : ℕ+) (G : Coeff 2 → ℂ)
    (hG : AnalyticAt ℂ G (SpectralWeight.one.toCoeff q.val))
    (hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      G (SpectralWeight.one.toCoeff p.val) = (hillRealGapIntegral p.val p.property.1 p.property.2 n 0 : ℂ))
    (h : WeightedCoeff SpectralWeight.one.toWeight 2)
    (heven : SpectralWeight.one.toCoeff h ∈ Coeff.paritySubspace 0) :
    (fderiv ℂ (D.roughActionCoordinate n) (hillOriginalHminusSource q.val)) (hillOriginalHminusSource h) =
      (fderiv ℂ G (SpectralWeight.one.toCoeff q.val)) (SpectralWeight.one.toCoeff h) := by
  apply hillHminusPhysicalGerm_fderiv_original q _ G (D.analyticAt_roughActionCoordinate_physical q n) hG
    (hmatch.mono (fun p hp => (D.roughActionCoordinate_physical p n).trans hp.symm)) h heven

/-- The genuine rough action Hamiltonian vector has the verified physical
contour source and the original unit-period Gardner sign, with no supplied gradient. -/
theorem roughActionCoordinate_hamiltonianVector (D : GlobalRoughAbelianForwardData)
    (q : RealPeriodOneHillPotential) (n : ℕ+) :
    NLS.Poisson.gardnerHamiltonianVector (D.roughActionCoordinate n) (hillOriginalHminusSource q.val) =
      -hillOriginalHminusSource
        (hillPhysicalMomentHamiltonianSource q.val q.property.1 q.property.2 n n.pos 0) :=
  hillOriginalAction_hminus_HamiltonianVector_eq_neg_source q n (D.roughActionCoordinate n)
    (D.analyticAt_roughActionCoordinate_physical q n)
    (Eventually.of_forall (fun p => D.roughActionCoordinate_physical p n))

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
