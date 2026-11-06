import NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianNativeGerms
import NLS.KdV.HillHminusPhysicalGermDifferentials
import NLS.KdV.HillAbelianCartesianNormalization
import NLS.KdV.HillRoughAbelianGardner

/-! # The actual rough signed coordinate has the physical Abelian differential -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.KdV
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

/-- Exact positive original Abelian coordinate, with no residual scaling. -/
theorem positiveComponent_physical (D : GlobalRoughAbelianForwardData)
    (p : RealPeriodOneHillPotential) (n : ℕ+) :
    hillRoughSignedAbelianComponent D.signed true n (hillOriginalHminusSource p.val) =
      hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n n.pos := by
  change (D.signed (hillOriginalHminusSource p.val)).val (n : ℤ) = _
  rw [hillOriginalHminusSource_eq_physical,
    D.signed_physical,hillAbelianRawCoordinateSequence_original_nat]

/-- ANY actual matching original L2 Abelian coordinate germ has the SAME
even physical differential as the globally fixed rough coordinate. -/
theorem positiveComponent_fderiv_original (D : GlobalRoughAbelianForwardData)
    (p : RealPeriodOneHillPotential) (n : ℕ+) (G : Coeff 2 → ℂ)
    (hG : AnalyticAt ℂ G (SpectralWeight.one.toCoeff p.val))
    (hmatch : ∀ᶠ a : RealPeriodOneHillPotential in 𝓝 p,
      G (SpectralWeight.one.toCoeff a.val) =
        hillDirichletAbelianCoordinate a.val a.property.1 a.property.2 n n.pos)
    (h : WeightedCoeff SpectralWeight.one.toWeight 2)
    (heven : SpectralWeight.one.toCoeff h ∈ Coeff.paritySubspace 0) :
    (fderiv ℂ (hillRoughSignedAbelianComponent D.signed true n) (hillOriginalHminusSource p.val))
      (hillOriginalHminusSource h) =
      (fderiv ℂ G (SpectralWeight.one.toCoeff p.val)) (SpectralWeight.one.toCoeff h) := by
  apply hillHminusPhysicalGerm_fderiv_original p _ G
    (hillRoughSignedAbelianComponent_analytic D.signed D.signed_analytic true n _
      (D.real_mem_domain _ (hillOriginalHminusSource_real p.val p.property.2))) hG
    (hmatch.mono (fun a ha => (D.positiveComponent_physical a n).trans ha.symm)) h heven

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
