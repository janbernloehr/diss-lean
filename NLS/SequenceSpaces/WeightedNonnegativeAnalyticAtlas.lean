import NLS.FunctionalAnalysis.WeightedNonnegativeAnalyticFredholm
import NLS.SequenceSpaces.NonnegativeAnalyticAtlas

/-! # Analytic local inverses on the original weighted nonnegative cone

All derivatives, compactness assumptions, inverse maps, and inverse identities
live on the original weighted sequence space. Positive weighting is used only
to prove uniqueness of local extension germs and relative Fredholm density.
-/
noncomputable section
open Set Filter Topology Metric
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {w : Weight} {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- The weighted cone determines a holomorphic germ, including all its boundary points. -/
theorem eventuallyEq_of_nonnegative_restriction (hp : p ≠ ⊤)
    {f g : WeightedCoeff w p → F} {x : nonnegativeLocus w p}
    (hf : AnalyticAt ℂ f x.val) (hg : AnalyticAt ℂ g x.val)
    (he : (fun y : nonnegativeLocus w p => f y.val) =ᶠ[𝓝 x] (fun y => g y.val)) :
    f =ᶠ[𝓝 x.val] g := by
  let L := (weightIsometry w p).toContinuousLinearEquiv
  let e := nonnegativeHomeomorph w p
  have hf' : AnalyticAt ℂ (fun z => f (L.symm z)) (L x.val) := by
    exact hf.comp_of_eq (f := L.symm) (L.symm.analyticAt (L x.val)) (L.symm_apply_apply x.val)
  have hg' : AnalyticAt ℂ (fun z => g (L.symm z)) (L x.val) := by
    exact hg.comp_of_eq (f := L.symm) (L.symm.analyticAt (L x.val)) (L.symm_apply_apply x.val)
  have he' : (fun y : Coeff.nonnegativeLocus p => f (L.symm y.val)) =ᶠ[𝓝 (e x)]
      (fun y => g (L.symm y.val)) := by
    have heAt : (fun y : nonnegativeLocus w p => f y.val) =ᶠ[𝓝 (e.symm (e x))]
        (fun y => g y.val) := by simpa only [e.symm_apply_apply] using he
    have hh := heAt.comp_tendsto e.symm.continuous.continuousAt
    change (fun y : Coeff.nonnegativeLocus p => f ((e.symm y).val)) =ᶠ[𝓝 (e x)]
      (fun y => g ((e.symm y).val)) at hh
    exact hh
  have hh := Coeff.eventuallyEq_of_nonnegative_restriction hp (x := e x) hf' hg' he'
  have ht := hh.comp_tendsto L.continuous.continuousAt
  simpa only [Function.comp_def,L.symm_apply_apply] using ht

/-- Local extensions of a cone map. Each extension is required to agree
with the map only near its own center in the relative topology. -/
structure NonnegativeAnalyticAtlas (f : nonnegativeLocus w p → F)
    (U : Set (nonnegativeLocus w p)) where
  extension : nonnegativeLocus w p → WeightedCoeff w p → F
  analyticAt : ∀ x ∈ U, AnalyticAt ℂ (extension x) x.val
  agreement : ∀ x ∈ U, f =ᶠ[𝓝 x] (fun y => extension x y.val)

namespace NonnegativeAnalyticAtlas
variable {f : nonnegativeLocus w p → F} {U : Set (nonnegativeLocus w p)}

/-- The complexified source derivative, evaluated using a local extension. -/
def derivative (a : NonnegativeAnalyticAtlas f U) (x : nonnegativeLocus w p) :
    WeightedCoeff w p →L[ℂ] F := fderiv ℂ (a.extension x) x.val

/-- The derivative is intrinsic to the original cone map. -/
theorem derivative_eq (hp : p ≠ ⊤) (a b : NonnegativeAnalyticAtlas f U)
    {x : nonnegativeLocus w p} (hx : x ∈ U) : a.derivative x = b.derivative x := by
  exact (eventuallyEq_of_nonnegative_restriction hp (a.analyticAt x hx) (b.analyticAt x hx)
    ((a.agreement x hx).symm.trans (b.agreement x hx))).fderiv_eq

/-- Nearby derivatives are the derivatives of any fixed local extension. -/
theorem eventually_derivative_eq (hp : p ≠ ⊤) (a : NonnegativeAnalyticAtlas f U)
    (hU : IsOpen U) {x : nonnegativeLocus w p} (hx : x ∈ U) :
    a.derivative =ᶠ[𝓝 x] (fun y => fderiv ℂ (a.extension x) y.val) := by
  filter_upwards [hU.mem_nhds hx, (a.agreement x hx).eventually_nhds,
    continuous_subtype_val.continuousAt ((a.analyticAt x hx).eventually_analyticAt)] with y hy he ha
  exact (eventuallyEq_of_nonnegative_restriction hp (a.analyticAt y hy) ha
    ((a.agreement y hy).symm.trans he)).fderiv_eq

/-- The complexified derivative admits local analytic extensions as an
operator-valued map on the cone. -/
theorem derivative_hasLocalAnalyticExtensions (hp : p ≠ ⊤)
    (a : NonnegativeAnalyticAtlas f U) (hU : IsOpen U) :
    HasLocalAnalyticExtensions a.derivative U := by
  intro x hx
  exact ⟨fderiv ℂ (a.extension x), (a.analyticAt x hx).fderiv,
    a.eventually_derivative_eq hp hU hx⟩

end NonnegativeAnalyticAtlas

/-- Every map admitting local analytic extensions has an atlas. -/
def HasLocalAnalyticExtensions.atlas
    {f : nonnegativeLocus w p → F} {U : Set (nonnegativeLocus w p)}
    (hf : HasLocalAnalyticExtensions f U) : NonnegativeAnalyticAtlas f U := by
  classical
  exact {
    extension := fun x => if hx : x ∈ U then (hf x hx).choose else 0
    analyticAt := fun x hx => by simpa only [dif_pos hx] using (hf x hx).choose_spec.1
    agreement := fun x hx => by simpa only [dif_pos hx] using (hf x hx).choose_spec.2 }

/-- Relative generic invertibility and actual local inverses for cone maps.
The inverse identities hold for the ambient extension; its left inverse
also recovers the original map on the cone, including boundary points. -/
theorem open_dense_localInverse_of_nonnegative_atlas
    (hp : p ≠ ⊤) {f : nonnegativeLocus w p → WeightedCoeff w p} {U : Set (nonnegativeLocus w p)}
    (a : NonnegativeAnalyticAtlas f U) (hU : IsOpen U) (hconn : IsPreconnected U)
    (hcompact : ∀ x ∈ U, IsCompactOperator (a.derivative x - 1 : WeightedCoeff w p →L[ℂ] WeightedCoeff w p))
    (hstart : ∃ x ∈ U, IsUnit (a.derivative x)) :
    IsOpen {x ∈ U | IsUnit (a.derivative x)} ∧
    U ⊆ closure {x ∈ U | IsUnit (a.derivative x)} ∧
    ∀ x ∈ U, IsUnit (a.derivative x) → ∃ G : WeightedCoeff w p → WeightedCoeff w p,
      AnalyticAt ℂ G (f x) ∧ G (f x) = x.val ∧
      (∀ᶠ y in 𝓝 x, G (f y) = y.val) ∧
      (∀ᶠ y in 𝓝 x.val, G (a.extension x y) = y) ∧
      (∀ᶠ z in 𝓝 (f x), a.extension x (G z) = z) ∧
      fderiv ℂ G (f x) = Ring.inverse (a.derivative x) := by
  have hd := open_dense_isUnit_of_nonnegative_analytic_compact_shift hp hU hconn
    (a.derivative_hasLocalAnalyticExtensions hp hU) (c := 1) one_ne_zero
    (by simpa only [one_smul] using hcompact) hstart
  refine ⟨hd.1,hd.2,?_⟩
  intro x hx hu
  obtain ⟨G,hG,hGx,hleft,hright,hDG⟩ :=
    ComplexAnalysis.exists_localInverse_of_isUnit_fderiv (a.analyticAt x hx) hu
  have hfx : f x = a.extension x x.val := (a.agreement x hx).eq_of_nhds
  refine ⟨G,by rwa [hfx],by rwa [hfx],?_,hleft,by rwa [hfx],by rwa [hfx]⟩
  filter_upwards [a.agreement x hx,continuous_subtype_val.continuousAt hleft] with y he hy
  rw [he]
  exact hy


/-- Points where the local extension has a two-sided analytic inverse. At
a cone boundary this is an inverse in the ambient sequence space. -/
def NonnegativeAnalyticAtlas.localInversePoints
    {f : nonnegativeLocus w p → WeightedCoeff w p} {U : Set (nonnegativeLocus w p)}
    (a : NonnegativeAnalyticAtlas f U) : Set (nonnegativeLocus w p) :=
  {x ∈ U | ∃ G : WeightedCoeff w p → WeightedCoeff w p,
    AnalyticAt ℂ G (a.extension x x.val) ∧ G (a.extension x x.val) = x.val ∧
    (∀ᶠ y in 𝓝 x.val, G (a.extension x y) = y) ∧
    (∀ᶠ z in 𝓝 (a.extension x x.val), a.extension x (G z) = z)}

/-- Local inverses are detected exactly by the intrinsic derivative. -/
theorem NonnegativeAnalyticAtlas.localInversePoints_eq
    {f : nonnegativeLocus w p → WeightedCoeff w p} {U : Set (nonnegativeLocus w p)}
    (a : NonnegativeAnalyticAtlas f U) :
    a.localInversePoints = {x ∈ U | IsUnit (a.derivative x)} := by
  ext x
  change (x ∈ U ∧ _) ↔ (x ∈ U ∧ _)
  apply and_congr_right
  intro hx
  exact (ComplexAnalysis.isUnit_fderiv_iff_localInverse (a.analyticAt x hx)).symm

/-- The local-inverse locus does not depend on which extension atlas is used. -/
theorem NonnegativeAnalyticAtlas.localInversePoints_eq_of_atlas (hp : p ≠ ⊤)
    {f : nonnegativeLocus w p → WeightedCoeff w p} {U : Set (nonnegativeLocus w p)}
    (a b : NonnegativeAnalyticAtlas f U) : a.localInversePoints = b.localInversePoints := by
  rw [a.localInversePoints_eq,b.localInversePoints_eq]
  ext x
  apply and_congr_right
  intro hx
  rw [a.derivative_eq hp b hx]

/-- A single actual local inverse implies relative openness and density
of all local-inverse points for a compact perturbation of the identity. -/
theorem open_dense_localInversePoints_of_nonnegative_atlas
    (hp : p ≠ ⊤) {f : nonnegativeLocus w p → WeightedCoeff w p} {U : Set (nonnegativeLocus w p)}
    (a : NonnegativeAnalyticAtlas f U) (hU : IsOpen U) (hconn : IsPreconnected U)
    (hcompact : ∀ x ∈ U, IsCompactOperator (a.derivative x - 1 : WeightedCoeff w p →L[ℂ] WeightedCoeff w p))
    (hstart : a.localInversePoints.Nonempty) :
    IsOpen a.localInversePoints ∧ U ⊆ closure a.localInversePoints := by
  rw [a.localInversePoints_eq] at hstart ⊢
  have hd := open_dense_isUnit_of_nonnegative_analytic_compact_shift hp hU hconn
    (a.derivative_hasLocalAnalyticExtensions hp hU) (c := 1) one_ne_zero
    (by simpa only [one_smul] using hcompact)
    (by obtain ⟨x,hx,hu⟩ := hstart; exact ⟨x,hx,hu⟩)
  exact hd

end NLS.WeightedCoeff
