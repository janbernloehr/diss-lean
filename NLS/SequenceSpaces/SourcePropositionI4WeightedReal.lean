import NLS.SequenceSpaces.WeightedRealLocalInverse

/-! # I.4 in the original weighted real sequence spaces

Local analyticity at cone boundary points is represented by complex extension
atlases. Actual real local inverses, their seed, and both inverse identities
live in the original weighted real Banach space, for every positive weight.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {w : Weight} {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {f : nonnegativeLocus w p → WeightedCoeff w p} {U : Set (nonnegativeLocus w p)}

/-- One actual weighted real inverse gives a relatively open dense inverse locus. -/
theorem sourcePropositionI4_real_weighted
    (hp : p ≠ ⊤) (a : NonnegativeAnalyticAtlas f U) (hU : IsOpen U)
    (hconn : IsPreconnected U) (hr : ∀ x ∈ U, f x ∈ realLocus w p)
    (hc : ∀ x ∈ U, IsCompactOperator (a.derivative x-1 : WeightedCoeff w p →L[ℂ] WeightedCoeff w p))
    (hs : a.realLocalInversePoints.Nonempty) :
    IsOpen a.realLocalInversePoints ∧ U ⊆ closure a.realLocalInversePoints := by
  rw [a.realLocalInversePoints_eq hp hU hr hc] at hs ⊢
  exact open_dense_localInversePoints_of_nonnegative_atlas hp a hU hconn hc hs

/-- Each real inverse point has actual real analytic inverse maps, with both
identities and recovery of the original cone map in its relative topology. -/
theorem NonnegativeAnalyticAtlas.exists_real_localInverse
    (a : NonnegativeAnalyticAtlas f U) {x : nonnegativeLocus w p}
    (hx : x ∈ a.realLocalInversePoints) : ∃ G : WeightedRealCoeff w p → WeightedRealCoeff w p,
      AnalyticAt ℝ (realRestriction (a.extension x)) (reCLM w p x.val) ∧
      AnalyticAt ℝ G (reCLM w p (f x)) ∧ G (reCLM w p (f x)) = reCLM w p x.val ∧
      (∀ᶠ y in 𝓝 (reCLM w p x.val), G (realRestriction (a.extension x) y) = y) ∧
      (∀ᶠ z in 𝓝 (reCLM w p (f x)), realRestriction (a.extension x) (G z) = z) ∧
      (∀ᶠ y in 𝓝 x, G (reCLM w p (f y)) = reCLM w p y.val) := by
  obtain ⟨hx,G,hG,hGx,hl,hr⟩ := hx
  rw [a.realRestriction_center hx] at hG hGx hr
  have hreal : (weightIsometry w p).toContinuousLinearEquiv x.val ∈ Coeff.realLocus p :=
    (mem_realLocus_iff w p _).mp (fun n => (x.property n).1)
  have hF := Coeff.analyticAt_coordinateRestriction (weightIsometry w p).toContinuousLinearEquiv
    (f := a.extension x) (x := reCLM w p x.val)
    (by rw [Coeff.val_coordinateReCLM _ _ hreal]; exact a.analyticAt x hx)
  refine ⟨G,hF,hG,hGx,hl,hr,?_⟩
  have ht : Tendsto (fun y : nonnegativeLocus w p => reCLM w p y.val)
      (𝓝 x) (𝓝 (reCLM w p x.val)) :=
    ((reCLM w p).continuous.comp continuous_subtype_val).continuousAt
  filter_upwards [ht hl,a.agreement x hx] with y hy he
  change G (realRestriction (a.extension x) (reCLM w p y.val)) = reCLM w p y.val at hy
  have heq : realRestriction (a.extension x) (reCLM w p y.val) = reCLM w p (a.extension x y.val) :=
    Coeff.coordinateRestriction_coordinateReCLM (weightIsometry w p).toContinuousLinearEquiv _ _
      ((mem_realLocus_iff w p _).mp (fun n => (y.property n).1))
  rw [heq,← he] at hy
  exact hy

/-- A differentiable real left inverse is enough for the weighted Fredholm seed. -/
theorem NonnegativeAnalyticAtlas.isUnit_derivative_of_real_localLeftInverse
    (hp : p ≠ ⊤) (a : NonnegativeAnalyticAtlas f U) (hU : IsOpen U)
    (hr : ∀ x ∈ U, f x ∈ realLocus w p) {x : nonnegativeLocus w p} (hx : x ∈ U)
    (hc : IsCompactOperator (a.derivative x-1 : WeightedCoeff w p →L[ℂ] WeightedCoeff w p))
    {G : WeightedRealCoeff w p → WeightedRealCoeff w p}
    (hG : DifferentiableAt ℝ G (reCLM w p (f x)))
    (hl : ∀ᶠ y in 𝓝 (reCLM w p x.val), G (realRestriction (a.extension x) y) = y) :
    IsUnit (a.derivative x) := by
  have hseed : ComplexAnalysis.HasDifferentiableLeftInverse (𝕜 := ℝ)
      (realRestriction (a.extension x)) (reCLM w p x.val) := by
    refine ⟨G,?_,hl⟩
    rwa [a.realRestriction_center hx]
  have hx' : nonnegativeHomeomorph w p x ∈ (nonnegativeHomeomorph w p).symm ⁻¹' U := by
    simpa only [mem_preimage,Homeomorph.symm_apply_apply] using hx
  have hn' : ComplexAnalysis.HasDifferentiableLeftInverse (𝕜 := ℝ)
      (Coeff.realRestriction (a.toCoeff.extension (nonnegativeHomeomorph w p x)))
      (Coeff.reCLM p (nonnegativeHomeomorph w p x).val) :=
    Coeff.real_leftInverse_seed_in_coordinates
    (weightIsometry w p).toContinuousLinearEquiv (nonnegativeHomeomorph w p) Subtype.val
    (nonnegativeHomeomorph_symm_val_linear (w := w)) f U a.extension a.analyticAt a.agreement x hseed
  obtain ⟨H,hH,hleft⟩ := hn'
  rw [a.toCoeff.realRestriction_center hx'] at hH
  have hu := a.toCoeff.isUnit_derivative_of_real_localLeftInverse hp
    (hU.preimage (nonnegativeHomeomorph w p).symm.continuous) (a.toCoeff_real hr) hx'
    (by rw [a.toCoeff_derivative hx]; exact ComplexAnalysis.compact_sub_one_linear_conjugate _ hc)
    hH hleft
  rw [a.toCoeff_derivative hx] at hu
  exact (MulEquiv.isUnit_map (weightIsometry w p).toContinuousLinearEquiv.conjContinuousAlgEquiv).mp hu

/-- The initial weighted real inverse need only be differentiable and a left inverse. -/
theorem sourcePropositionI4_real_weighted_of_differentiable_seed
    (hp : p ≠ ⊤) (a : NonnegativeAnalyticAtlas f U) (hU : IsOpen U)
    (hconn : IsPreconnected U) (hr : ∀ x ∈ U, f x ∈ realLocus w p)
    (hc : ∀ x ∈ U, IsCompactOperator (a.derivative x-1 : WeightedCoeff w p →L[ℂ] WeightedCoeff w p))
    (hs : ∃ x ∈ U, ∃ G : WeightedRealCoeff w p → WeightedRealCoeff w p,
      DifferentiableAt ℝ G (reCLM w p (f x)) ∧
      ∀ᶠ y in 𝓝 (reCLM w p x.val), G (realRestriction (a.extension x) y) = y) :
    IsOpen a.realLocalInversePoints ∧ U ⊆ closure a.realLocalInversePoints := by
  rw [a.realLocalInversePoints_eq hp hU hr hc]
  apply open_dense_localInversePoints_of_nonnegative_atlas hp a hU hconn hc
  rw [a.localInversePoints_eq]
  obtain ⟨x,hx,G,hG,hl⟩ := hs
  exact ⟨x,hx,a.isUnit_derivative_of_real_localLeftInverse hp hU hr hx (hc x hx) hG hl⟩

end NLS.WeightedCoeff
