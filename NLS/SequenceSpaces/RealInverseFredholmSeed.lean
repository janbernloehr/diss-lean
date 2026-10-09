import NLS.SequenceSpaces.RealDerivativeEntries
import NLS.SequenceSpaces.RealAnalyticInverseRestriction
import NLS.SequenceSpaces.RealOperator
import NLS.FunctionalAnalysis.CompactDecomposition

/-! # A real local inverse supplies the complex Fredholm seed

A differentiable real left inverse forces injectivity on real directions.
Reality of the derivative then forces complex injectivity, and the Fredholm
alternative upgrades it to invertibility. No complex inverse is assumed.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Under the source compactness assumption, an actual real differentiable
local left inverse supplies the invertible complex derivative required by I.4. -/
theorem isUnit_fderiv_of_real_localLeftInverse (hp : p ≠ ⊤)
    {F : Coeff p → Coeff p} {x : RealCoeff p}
    (hF : AnalyticAt ℂ F (RealCoeff.complexCLM p x))
    (hreal : ∀ᶠ y in 𝓝 (RealCoeff.complexCLM p x), y ∈ realLocus p → F y ∈ realLocus p)
    (hcompact : IsCompactOperator (fderiv ℂ F (RealCoeff.complexCLM p x)-1 : Coeff p →L[ℂ] Coeff p))
    {G : RealCoeff p → RealCoeff p} (hG : DifferentiableAt ℝ G (realRestriction F x))
    (hl : ∀ᶠ y in 𝓝 x, G (realRestriction F y) = y) :
    IsUnit (fderiv ℂ F (RealCoeff.complexCLM p x)) := by
  let A := fderiv ℂ F (RealCoeff.complexCLM p x)
  let D := fderiv ℝ (realRestriction F) x
  have hFr := analyticAt_realRestriction hF
  have he : (G ∘ realRestriction F) =ᶠ[𝓝 x] id := hl
  have hD := he.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_comp x hG hFr.differentiableAt,fderiv_id] at hD
  have hDz {b : RealCoeff p} (hb : D b = 0) : b = 0 := by
    have hh := congrArg (fun T : RealCoeff p →L[ℝ] RealCoeff p => T b) hD
    change (fderiv ℝ G (realRestriction F x)) (D b) = b at hh
    rw [hb,map_zero] at hh
    exact hh.symm
  have hxr : RealCoeff.complexCLM p x ∈ realLocus p := by intro n; simp
  have hentries := fderiv_entries_real_of_eventually_real hxr hF hreal
  have hinj : Function.Injective A := operator_injective_of_realKernelZero hp A hentries (by
    intro b hb hAb
    have hj : RealCoeff.complexCLM p (reCLM p b) = b := RealCoeff.complexCLM_reCLM p b hb
    have hDb : D (reCLM p b) = 0 := by
      dsimp [D]
      rw [fderiv_realRestriction hF]
      change reCLM p (A (RealCoeff.complexCLM p (reCLM p b))) = 0
      rw [hj,hAb,map_zero]
    have hz := congrArg (RealCoeff.complexCLM p) (hDz hDb)
    simpa only [hj,map_zero] using hz)
  apply ContinuousLinearMap.isUnit_iff_bijective.mpr
  exact CompactSpectrum.bijective_of_injective_compact_sub_smul A (c := 1) one_ne_zero
    (by simpa only [one_smul] using hcompact) hinj

end NLS.Coeff
