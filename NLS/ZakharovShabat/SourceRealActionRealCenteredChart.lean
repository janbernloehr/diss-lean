import NLS.ZakharovShabat.SourceComplexAction

/-! # Actual action charts with a real spectral center

The existing local action construction uses a midpoint circle. Retaining
its real-center property provides actual action charts directly comparable
with the normalized psi contours.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- An actual action chart centered at any real source can be chosen
with a real spectral center, without an additional contour premise. -/
theorem exists_sourceRealActionBallChart_realCentered
    (hp : p ≠ ⊤) (hp1 : 1 < p) (k : ℤ) (φ : realTypeSourceLocus p) :
    ∃ ch : SourceRealActionBallChart hp hp1 k,
      ch.center = φ.val ∧ ch.spectralCenter.im = 0 := by
  obtain ⟨c,R,hR,hc,V,hV,hφ,hgeom,hdiff,hagree⟩ :=
    exists_local_differentiable_extension_of_sourceRealAction_real_center hp hp1 φ.val φ.property k
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hφ)
  refine ⟨{
    center := φ.val
    center_real := φ.property
    radius := r
    radius_pos := hr
    spectralCenter := c
    spectralRadius := R
    spectralRadius_pos := hR
    geometry := fun ψ hψ => hgeom ψ (hball hψ)
    differentiable := hdiff.mono hball
    agrees_real := fun ψ hψ hreal => hagree ψ (hball hψ) hreal
  },rfl,hc⟩

end NLS.ZakharovShabat
