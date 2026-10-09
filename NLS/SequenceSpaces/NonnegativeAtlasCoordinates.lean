import NLS.SequenceSpaces.NonnegativeAnalyticAtlas
import NLS.ComplexAnalysis.LinearCoordinatesLocalInverse

/-! # Local cone atlases in compatible linear coordinates -/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {E S : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace S] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Construct a normalized cone atlas from compatible parameter and linear coordinates. -/
def NonnegativeAnalyticAtlas.ofCoordinates
    (L : E ≃L[ℂ] Coeff p) (e : S ≃ₜ nonnegativeLocus p) (i : S → E)
    (hi : ∀ y, i (e.symm y) = L.symm y.val)
    (f : S → E) (U : Set S) (F : S → E → E)
    (ha : ∀ x ∈ U, AnalyticAt ℂ (F x) (i x))
    (he : ∀ x ∈ U, f =ᶠ[𝓝 x] (fun y => F x (i y))) :
    NonnegativeAnalyticAtlas (fun y => L (f (e.symm y))) (e.symm ⁻¹' U) where
  extension y z := L (F (e.symm y) (L.symm z))
  analyticAt y hy := by
    have hh := ComplexAnalysis.analyticAt_linear_conjugate L (ha (e.symm y) hy)
    rw [hi,L.apply_symm_apply] at hh
    exact hh
  agreement y hy := by
    have hh := (he (e.symm y) hy).comp_tendsto e.symm.continuous.continuousAt
    filter_upwards [hh] with z hz
    change f (e.symm z) = F (e.symm y) (i (e.symm z)) at hz
    rw [hi] at hz
    exact congrArg L hz

/-- Compact derivative shifts transport without unfolding the parameter space. -/
theorem compact_family_in_coordinates
    (L : E ≃L[ℂ] Coeff p) (e : S ≃ₜ nonnegativeLocus p) {U : Set S}
    {A : S → E →L[ℂ] E} {B : nonnegativeLocus p → Coeff p →L[ℂ] Coeff p}
    (hAB : ∀ x ∈ U, B (e x) = L.conjContinuousAlgEquiv (A x))
    (hc : ∀ x ∈ U, IsCompactOperator (A x-1 : E →L[ℂ] E)) :
    ∀ y ∈ e.symm ⁻¹' U, IsCompactOperator (B y-1 : Coeff p →L[ℂ] Coeff p) := by
  intro y hy
  have he : y = e (e.symm y) := (e.apply_symm_apply y).symm
  rw [he,hAB _ hy]
  exact ComplexAnalysis.compact_sub_one_linear_conjugate L (hc _ hy)

omit [NormedAddCommGroup E] [NormedSpace ℂ E] [Fact (1 ≤ p)] in
/-- Transport a range predicate along compatible parameter and output coordinates. -/
theorem range_predicate_in_coordinates
    {T : Type*} [TopologicalSpace T] (L : E → Coeff p) (e : S ≃ₜ T)
    {P : E → Prop} {Q : Coeff p → Prop} (hPQ : ∀ z, P z ↔ Q (L z))
    {f : S → E} {U : Set S} (hr : ∀ x ∈ U, P (f x)) :
    ∀ y ∈ e.symm ⁻¹' U, Q (L (f (e.symm y))) :=
  fun _ hy => (hPQ _).mp (hr _ hy)

/-- Identify intrinsic inverse loci using a normalized locus and derivative coordinates. -/
theorem inverse_locus_eq_in_coordinates
    (L : E ≃L[ℂ] Coeff p) (e : S ≃ₜ nonnegativeLocus p)
    {U R C : Set S} {R' C' : Set (nonnegativeLocus p)}
    {A : S → E →L[ℂ] E} {B : nonnegativeLocus p → Coeff p →L[ℂ] Coeff p}
    (hR : ∀ x, x ∈ R ↔ e x ∈ R') (hRC : R' = C')
    (hC : C = {x ∈ U | IsUnit (A x)})
    (hC' : C' = {y ∈ e.symm ⁻¹' U | IsUnit (B y)})
    (hAB : ∀ x ∈ U, B (e x) = L.conjContinuousAlgEquiv (A x)) : R = C := by
  ext x
  rw [hR,hRC,hC',hC]
  change (e.symm (e x) ∈ U ∧ _) ↔ (x ∈ U ∧ _)
  rw [e.symm_apply_apply]
  apply and_congr_right
  intro hx
  rw [hAB x hx]
  exact MulEquiv.isUnit_map L.conjContinuousAlgEquiv

end NLS.Coeff
