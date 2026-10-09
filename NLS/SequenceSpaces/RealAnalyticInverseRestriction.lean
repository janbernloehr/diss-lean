import NLS.SequenceSpaces.RealCoeff
import NLS.SequenceSpaces.RealFormIdentity
import NLS.ComplexAnalysis.AnalyticLocalInverseCriterion

/-! # Actual real-valued restrictions of analytic inverse pairs -/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- A map on real coefficient sequences, using the real part of its complex extension. -/
def realRestriction (f : Coeff p → Coeff q) : RealCoeff p → RealCoeff q :=
  fun y => reCLM q (f (RealCoeff.complexCLM p y))

/-- Complex analyticity gives real analyticity of the actual real-valued map. -/
theorem analyticAt_realRestriction {f : Coeff p → Coeff q} {x : RealCoeff p}
    (hf : AnalyticAt ℂ f (RealCoeff.complexCLM p x)) :
    AnalyticAt ℝ (realRestriction f) x :=
  ((reCLM q).analyticAt _).comp
    (hf.restrictScalars.comp ((RealCoeff.complexCLM p).analyticAt x))

/-- The derivative of the real restriction is the restricted complex derivative
followed by real-part projection. -/
theorem fderiv_realRestriction {f : Coeff p → Coeff q} {x : RealCoeff p}
    (hf : AnalyticAt ℂ f (RealCoeff.complexCLM p x)) :
    fderiv ℝ (realRestriction f) x =
      (reCLM q).comp (((fderiv ℂ f (RealCoeff.complexCLM p x)).restrictScalars ℝ).comp
        (RealCoeff.complexCLM p)) := by
  exact ((reCLM q).hasFDerivAt.comp x
    ((hf.differentiableAt.hasFDerivAt.restrictScalars ℝ).comp x
      (RealCoeff.complexCLM p).hasFDerivAt)).fderiv

/-- Where the extension is real, its real restriction recovers its full complex value. -/
theorem complexCLM_realRestriction {f : Coeff p → Coeff q} {x : RealCoeff p}
    (hx : f (RealCoeff.complexCLM p x) ∈ realLocus q) :
    RealCoeff.complexCLM q (realRestriction f x) = f (RealCoeff.complexCLM p x) :=
  RealCoeff.complexCLM_reCLM q _ hx

/-- Both inverse identities survive restriction to real coefficient spaces. -/
theorem realRestriction_localInverse
    {F G : Coeff p → Coeff p} {x : RealCoeff p}
    (hF : AnalyticAt ℂ F (RealCoeff.complexCLM p x))
    (hG : AnalyticAt ℂ G (F (RealCoeff.complexCLM p x)))
    (hFx : F (RealCoeff.complexCLM p x) ∈ realLocus p)
    (hGx : G (F (RealCoeff.complexCLM p x)) = RealCoeff.complexCLM p x)
    (hl : ∀ᶠ y in 𝓝 (RealCoeff.complexCLM p x), G (F y) = y)
    (hr : ∀ᶠ z in 𝓝 (F (RealCoeff.complexCLM p x)), F (G z) = z)
    (hrealF : ∀ᶠ y in 𝓝 (RealCoeff.complexCLM p x), y ∈ realLocus p → F y ∈ realLocus p)
    (hrealG : ∀ᶠ z in 𝓝 (F (RealCoeff.complexCLM p x)), z ∈ realLocus p → G z ∈ realLocus p) :
    AnalyticAt ℝ (realRestriction F) x ∧
    AnalyticAt ℝ (realRestriction G) (realRestriction F x) ∧
    realRestriction G (realRestriction F x) = x ∧
    (∀ᶠ y in 𝓝 x, realRestriction G (realRestriction F y) = y) ∧
    (∀ᶠ z in 𝓝 (realRestriction F x), realRestriction F (realRestriction G z) = z) := by
  have hcx := complexCLM_realRestriction hFx
  have hGa : AnalyticAt ℂ G (RealCoeff.complexCLM p (realRestriction F x)) := by
    rwa [hcx]
  refine ⟨analyticAt_realRestriction hF,analyticAt_realRestriction hGa,?_,?_,?_⟩
  · change reCLM p (G (RealCoeff.complexCLM p (realRestriction F x))) = x
    rw [hcx,hGx,RealCoeff.reCLM_complexCLM]
  · filter_upwards [(RealCoeff.complexCLM p).continuous.continuousAt hl,
      (RealCoeff.complexCLM p).continuous.continuousAt hrealF] with y hy hyr
    have hyreal : RealCoeff.complexCLM p y ∈ realLocus p := by intro n; simp
    change reCLM p (G (RealCoeff.complexCLM p (realRestriction F y))) = y
    rw [complexCLM_realRestriction (hyr hyreal),hy,RealCoeff.reCLM_complexCLM]
  · have ht : Tendsto (RealCoeff.complexCLM p) (𝓝 (realRestriction F x))
        (𝓝 (F (RealCoeff.complexCLM p x))) := by
      simpa only [hcx] using (RealCoeff.complexCLM p).continuous.tendsto (realRestriction F x)
    filter_upwards [ht hr,ht hrealG] with z hz hzr
    have hzreal : RealCoeff.complexCLM p z ∈ realLocus p := by intro n; simp
    change reCLM p (F (RealCoeff.complexCLM p (realRestriction G z))) = z
    rw [complexCLM_realRestriction (hzr hzreal),hz,RealCoeff.reCLM_complexCLM]

end NLS.Coeff
