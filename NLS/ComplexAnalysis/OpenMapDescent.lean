import Mathlib.Topology.Constructions
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Logic.Function.Basic

/-! # Continuous descent along an open map

A continuous function constant on fibers of a continuous open map
descends continuously to the image of any open domain. This topological
step makes no claim about analytic regularity of the descended function.
-/
noncomputable section
open Set Topology
namespace NLS.ComplexAnalysis
variable {E B F : Type*} [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace F]
  [Nonempty F]

/-- Extend a function from the fibers of a restricted map to its target. -/
def openMapDescent (Q : E → B) (f : E → F) (U : Set E) : B → F :=
  Function.extend (fun x : U => Q x.val) (fun x : U => f x.val) (fun _ => Classical.arbitrary F)

omit [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace F] in
/-- The descended function recovers the original one on the domain. -/
theorem openMapDescent_apply (Q : E → B) (f : E → F) (U : Set E)
    (hinv : ∀ x ∈ U, ∀ y ∈ U, Q x = Q y → f x = f y) (x : E) (hx : x ∈ U) :
    openMapDescent Q f U (Q x) = f x := by
  have h : Function.FactorsThrough (fun x : U => f x.val) (fun x : U => Q x.val) :=
    fun x y he => hinv x.val x.property y.val y.property he
  exact h.extend_apply (fun _ => Classical.arbitrary F) ⟨x,hx⟩

/-- A continuous fiber invariant descends continuously to the open image. -/
theorem continuousOn_openMapDescent (Q : E → B) (f : E → F) (U : Set E)
    (hQ : Continuous Q) (hQo : IsOpenMap Q) (hU : IsOpen U) (hf : ContinuousOn f U)
    (hinv : ∀ x ∈ U, ∀ y ∈ U, Q x = Q y → f x = f y) :
    ContinuousOn (openMapDescent Q f U) (Q '' U) := by
  let P : U → (Q '' U) := fun x => ⟨Q x.val,⟨x.val,x.property,rfl⟩⟩
  have hPo : IsOpenMap P := (hQo.domRestrict hU).codRestrict (s := Q '' U)
    (fun x : U => ⟨x.val,x.property,rfl⟩)
  have hPc : Continuous P := (hQ.comp continuous_subtype_val).subtype_mk _
  have hPs : Function.Surjective P := by
    rintro ⟨b,⟨x,hx,rfl⟩⟩
    exact ⟨⟨x,hx⟩,rfl⟩
  rw [continuousOn_iff_continuous_domRestrict]
  apply (hPo.isQuotientMap hPc hPs).continuous_iff.mpr
  have he : (fun x : U => openMapDescent Q f U (Q x.val)) = (fun x : U => f x.val) :=
    funext (fun x => openMapDescent_apply Q f U hinv x.val x.property)
  change Continuous (fun x : U => openMapDescent Q f U (Q x.val))
  rw [he]
  exact continuousOn_iff_continuous_domRestrict.mp hf

omit [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace F] in
/-- Agreement on the lifted domain uniquely determines the descended
function on the image, regardless of values assigned elsewhere. -/
theorem eqOn_openMapDescent (Q : E → B) (f : E → F) (U : Set E)
    (hinv : ∀ x ∈ U, ∀ y ∈ U, Q x = Q y → f x = f y)
    (g : B → F) (hg : ∀ x ∈ U, g (Q x) = f x) :
    EqOn g (openMapDescent Q f U) (Q '' U) := by
  rintro _ ⟨x,hx,rfl⟩
  rw [hg x hx,openMapDescent_apply Q f U hinv x hx]

end NLS.ComplexAnalysis
