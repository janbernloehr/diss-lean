import NLS.SequenceSpaces.WeightedRealAnalyticAtlas

/-! # I.4 from real analytic germs in the original weighted spaces

All analyticity data, starting inverses, and resulting inverse germs concern
the actual real sequence space. Compactness is imposed only at cone points
on the complexification of the original real derivative minus identity.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {w : Weight} {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {f : nonnegativeLocus w p → WeightedRealCoeff w p} {U : Set (nonnegativeLocus w p)}

/-- Proposition I.4 with its real-analytic hypothesis, for arbitrary positive weights. -/
theorem sourcePropositionI4_real_analytic
    (hp : p ≠ ⊤) (a : NonnegativeRealAnalyticAtlas f U) (hU : IsOpen U)
    (hconn : IsPreconnected U)
    (hc : ∀ x ∈ U, IsCompactOperator
      (a.complexifiedDerivative x-1 : WeightedCoeff w p →L[ℂ] WeightedCoeff w p))
    (hs : a.localInversePoints.Nonempty) :
    IsOpen a.localInversePoints ∧ U ⊆ closure a.localInversePoints := by
  have hc' : ∀ x ∈ U, IsCompactOperator
      (a.toComplex.derivative x-1 : WeightedCoeff w p →L[ℂ] WeightedCoeff w p) := by
    intro x hx
    rw [a.toComplex_derivative hx]
    exact hc x hx
  have hs' : a.toComplex.realLocalInversePoints.Nonempty := by
    rwa [a.toComplex_realLocalInversePoints]
  have h := sourcePropositionI4_real_weighted hp a.toComplex hU hconn
    (fun x _ n => WeightedRealCoeff.im_eq_zero w p (f x) n) hc' hs'
  rwa [a.toComplex_realLocalInversePoints] at h

namespace NonnegativeRealAnalyticAtlas

/-- The real extension takes the original value at its center. -/
theorem extension_center (a : NonnegativeRealAnalyticAtlas f U)
    {x : nonnegativeLocus w p} (hx : x ∈ U) :
    a.extension x (reCLM w p x.val) = f x := (a.agreement x hx).eq_of_nhds.symm

/-- The inverse maps and both identities belong to the original real extensions;
the inverse also recovers the original cone map near its center. -/
theorem exists_localInverse (a : NonnegativeRealAnalyticAtlas f U)
    {x : nonnegativeLocus w p} (hx : x ∈ a.localInversePoints) :
    ∃ G : WeightedRealCoeff w p → WeightedRealCoeff w p,
      AnalyticAt ℝ (a.extension x) (reCLM w p x.val) ∧
      AnalyticAt ℝ G (f x) ∧ G (f x) = reCLM w p x.val ∧
      (∀ᶠ y in 𝓝 (reCLM w p x.val), G (a.extension x y) = y) ∧
      (∀ᶠ z in 𝓝 (f x), a.extension x (G z) = z) ∧
      (∀ᶠ y in 𝓝 x, G (f y) = reCLM w p y.val) := by
  obtain ⟨hx,G,hG,hGx,hl,hr⟩ := hx
  rw [a.extension_center hx] at hG hGx hr
  refine ⟨G,a.analyticAt x hx,hG,hGx,hl,hr,?_⟩
  have ht : Tendsto (fun y : nonnegativeLocus w p => reCLM w p y.val)
      (𝓝 x) (𝓝 (reCLM w p x.val)) :=
    ((reCLM w p).continuous.comp continuous_subtype_val).continuousAt
  filter_upwards [ht hl,a.agreement x hx] with y hy he
  change G (a.extension x (reCLM w p y.val)) = reCLM w p y.val at hy
  rwa [he]

/-- Intrinsic inverse locus: it does not depend on the chosen real extensions. -/
theorem localInversePoints_eq_of_atlas
    (hp : p ≠ ⊤) (a b : NonnegativeRealAnalyticAtlas f U) (hU : IsOpen U)
    (hc : ∀ x ∈ U, IsCompactOperator
      (a.complexifiedDerivative x-1 : WeightedCoeff w p →L[ℂ] WeightedCoeff w p)) :
    a.localInversePoints = b.localInversePoints := by
  rw [← a.toComplex_realLocalInversePoints,← b.toComplex_realLocalInversePoints]
  apply a.toComplex.realLocalInversePoints_eq_of_atlas hp b.toComplex hU
    (fun x _ n => WeightedRealCoeff.im_eq_zero w p (f x) n)
  intro x hx
  rw [a.toComplex_derivative hx]
  exact hc x hx

end NonnegativeRealAnalyticAtlas

/-- A differentiable real left inverse at one point suffices for Proposition I.4. -/
theorem sourcePropositionI4_real_analytic_of_differentiable_seed
    (hp : p ≠ ⊤) (a : NonnegativeRealAnalyticAtlas f U) (hU : IsOpen U)
    (hconn : IsPreconnected U)
    (hc : ∀ x ∈ U, IsCompactOperator
      (a.complexifiedDerivative x-1 : WeightedCoeff w p →L[ℂ] WeightedCoeff w p))
    (hs : ∃ x ∈ U, ∃ G : WeightedRealCoeff w p → WeightedRealCoeff w p,
      DifferentiableAt ℝ G (f x) ∧
      ∀ᶠ y in 𝓝 (reCLM w p x.val), G (a.extension x y) = y) :
    IsOpen a.localInversePoints ∧ U ⊆ closure a.localInversePoints := by
  have hc' : ∀ x ∈ U, IsCompactOperator
      (a.toComplex.derivative x-1 : WeightedCoeff w p →L[ℂ] WeightedCoeff w p) := by
    intro x hx
    rw [a.toComplex_derivative hx]
    exact hc x hx
  have hs' : ∃ x ∈ U, ∃ G : WeightedRealCoeff w p → WeightedRealCoeff w p,
      DifferentiableAt ℝ G (reCLM w p (f x).val) ∧
      ∀ᶠ y in 𝓝 (reCLM w p x.val), G (realRestriction (a.toComplex.extension x) y) = y := by
    obtain ⟨x,hx,G,hG,hl⟩ := hs
    refine ⟨x,hx,G,?_,?_⟩
    · simpa only [reCLM,Coeff.coordinateReCLM_val] using hG
    · filter_upwards [a.toComplex_restriction hx,hl] with y hy hyl
      rwa [hy]
  have h := sourcePropositionI4_real_weighted_of_differentiable_seed hp a.toComplex hU hconn
    (fun x _ n => WeightedRealCoeff.im_eq_zero w p (f x) n) hc' hs'
  rwa [a.toComplex_realLocalInversePoints] at h

end NLS.WeightedCoeff
