import NLS.SequenceSpaces.NonnegativeRealLocalInverse
import NLS.SequenceSpaces.RealInverseFredholmSeed

/-! # I.4 with an actual real local-inverse seed

This is the real sequence-space conclusion on the unweighted cone. Both the
initial inverse and the generic inverses are real analytic maps on real
sequence neighborhoods, represented by local complex extension atlases.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {f : nonnegativeLocus p → Coeff p} {U : Set (nonnegativeLocus p)}

/-- Genuine real analytic local-inverse points of the original cone map. -/
def NonnegativeAnalyticAtlas.realLocalInversePoints (a : NonnegativeAnalyticAtlas f U) :
    Set (nonnegativeLocus p) :=
  {x ∈ U | ∃ G : RealCoeff p → RealCoeff p,
    AnalyticAt ℝ G (reCLM p (f x)) ∧ G (reCLM p (f x)) = reCLM p x.val ∧
    (∀ᶠ y in 𝓝 (reCLM p x.val), G (realRestriction (a.extension x) y) = y) ∧
    (∀ᶠ z in 𝓝 (reCLM p (f x)), realRestriction (a.extension x) (G z) = z)}

/-- A differentiable real left inverse suffices to obtain the complex seed. -/
theorem NonnegativeAnalyticAtlas.isUnit_derivative_of_real_localLeftInverse
    (hp : p ≠ ⊤) (a : NonnegativeAnalyticAtlas f U) (hU : IsOpen U)
    (hreal : ∀ x ∈ U, f x ∈ realLocus p) {x : nonnegativeLocus p} (hx : x ∈ U)
    (hcompact : IsCompactOperator (a.derivative x-1 : Coeff p →L[ℂ] Coeff p))
    {G : RealCoeff p → RealCoeff p} (hG : DifferentiableAt ℝ G (reCLM p (f x)))
    (hl : ∀ᶠ y in 𝓝 (reCLM p x.val), G (realRestriction (a.extension x) y) = y) :
    IsUnit (a.derivative x) := by
  have hcx : RealCoeff.complexCLM p (reCLM p x.val) = x.val :=
    RealCoeff.complexCLM_reCLM p _ (fun n => (x.property n).1)
  have hfx : f x = a.extension x x.val := (a.agreement x hx).eq_of_nhds
  have hbase : realRestriction (a.extension x) (reCLM p x.val) = reCLM p (f x) := by
    change reCLM p (a.extension x (RealCoeff.complexCLM p (reCLM p x.val))) = _
    rw [hcx,← hfx]
  have hh := isUnit_fderiv_of_real_localLeftInverse hp (F := a.extension x) (x := reCLM p x.val)
    (by rw [hcx]; exact a.analyticAt x hx)
    (by rw [hcx]; exact a.extension_eventually_real hU hreal hx)
    (by rw [hcx]; exact hcompact)
    (by rw [hbase]; exact hG) hl
  simpa only [hcx,NonnegativeAnalyticAtlas.derivative] using hh

/-- Under the source compactness assumption, the real and complex local-inverse
loci agree; in particular a real local inverse supplies the complex seed. -/
theorem NonnegativeAnalyticAtlas.realLocalInversePoints_eq
    (hp : p ≠ ⊤) (a : NonnegativeAnalyticAtlas f U) (hU : IsOpen U)
    (hreal : ∀ x ∈ U, f x ∈ realLocus p)
    (hcompact : ∀ x ∈ U, IsCompactOperator (a.derivative x-1 : Coeff p →L[ℂ] Coeff p)) :
    a.realLocalInversePoints = a.localInversePoints := by
  rw [a.localInversePoints_eq]
  ext x
  change (x ∈ U ∧ _) ↔ (x ∈ U ∧ _)
  apply and_congr_right
  intro hx
  constructor
  · rintro ⟨G,hG,_,hl,_⟩
    exact a.isUnit_derivative_of_real_localLeftInverse hp hU hreal hx (hcompact x hx)
      hG.differentiableAt hl
  · intro hu
    obtain ⟨G,_,hG,hGx,hl,hr,_⟩ :=
      exists_realRestriction_localInverse_of_nonnegative_atlas hp a hU hreal hx hu
    exact ⟨G,hG,hGx,hl,hr⟩

/-- Real local diffeomorphism points are relatively open and dense when there
is one such point. The domain may contain zero and arbitrary cone boundary points. -/
theorem sourcePropositionI4_real_unweighted
    (hp : p ≠ ⊤) (a : NonnegativeAnalyticAtlas f U) (hU : IsOpen U)
    (hconn : IsPreconnected U) (hreal : ∀ x ∈ U, f x ∈ realLocus p)
    (hcompact : ∀ x ∈ U, IsCompactOperator (a.derivative x-1 : Coeff p →L[ℂ] Coeff p))
    (hstart : a.realLocalInversePoints.Nonempty) :
    IsOpen a.realLocalInversePoints ∧ U ⊆ closure a.realLocalInversePoints := by
  rw [a.realLocalInversePoints_eq hp hU hreal hcompact] at hstart ⊢
  exact open_dense_localInversePoints_of_nonnegative_atlas hp a hU hconn hcompact hstart

/-- The initial local inverse need only be differentiable and a left inverse.
The generic inverse points still have two-sided real analytic inverses. -/
theorem sourcePropositionI4_real_of_differentiable_seed
    (hp : p ≠ ⊤) (a : NonnegativeAnalyticAtlas f U) (hU : IsOpen U)
    (hconn : IsPreconnected U) (hreal : ∀ x ∈ U, f x ∈ realLocus p)
    (hcompact : ∀ x ∈ U, IsCompactOperator (a.derivative x-1 : Coeff p →L[ℂ] Coeff p))
    (hstart : ∃ x ∈ U, ∃ G : RealCoeff p → RealCoeff p,
      DifferentiableAt ℝ G (reCLM p (f x)) ∧
      ∀ᶠ y in 𝓝 (reCLM p x.val), G (realRestriction (a.extension x) y) = y) :
    IsOpen a.realLocalInversePoints ∧ U ⊆ closure a.realLocalInversePoints := by
  rw [a.realLocalInversePoints_eq hp hU hreal hcompact]
  apply open_dense_localInversePoints_of_nonnegative_atlas hp a hU hconn hcompact
  rw [a.localInversePoints_eq]
  obtain ⟨x,hx,G,hG,hl⟩ := hstart
  exact ⟨x,hx,a.isUnit_derivative_of_real_localLeftInverse hp hU hreal hx (hcompact x hx) hG hl⟩

end NLS.Coeff
