import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

/-! # Compact perturbations of a nonzero scalar identity

These results work over real as well as complex scalars. Compactness gives
a finite-dimensional kernel; if that kernel vanishes, the Fredholm alternative
gives bijectivity. No injectivity assumption is hidden in the compactness premise.
-/
noncomputable section
open Module Module.End
namespace NLS.CompactScalarPerturbation
variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The kernel of a compact perturbation of a nonzero scalar identity is finite dimensional. -/
theorem finiteDimensional_ker [CompleteSpace 𝕜] (A : E →L[𝕜] E) {c : 𝕜} (hc : c ≠ 0)
    (hA : IsCompactOperator (A - c • 1 : E →L[𝕜] E)) :
    FiniteDimensional 𝕜 A.ker := by
  let T := A - c • 1
  let W := A.ker
  have heigen (v : E) (hv : v ∈ W) : T v = (-c) • v := by
    change A v - c • v = (-c) • v
    have hv0 : A v = 0 := hv
    rw [hv0]
    simp
  have hpres : ∀ v ∈ W, (T : Module.End 𝕜 E) v ∈ W := by
    intro v hv
    change T v ∈ W
    rw [heigen v hv]
    exact W.smul_mem (-c) hv
  have hclosed : IsClosed (W : Set E) := A.isClosed_ker
  have hcompact := hA.restrict (f := (T : Module.End 𝕜 E)) hpres hclosed
  have hid : ((-c)⁻¹ • ((T : Module.End 𝕜 E).restrict hpres : W → W)) = id := by
    funext v
    apply Subtype.ext
    change (-c)⁻¹ • T (v : E) = (v : E)
    rw [heigen v v.property, inv_smul_smul₀ (neg_ne_zero.mpr hc)]
  exact FiniteDimensional.of_isCompactOperator_id (𝕜 := 𝕜)
    (hid ▸ hcompact.smul (-c)⁻¹)

/-- An injective compact perturbation of a nonzero scalar identity is bijective. -/
theorem bijective_of_injective [CompleteSpace E]
    (A : E →L[𝕜] E) {c : 𝕜} (hc : c ≠ 0)
    (hA : IsCompactOperator (A - c • 1 : E →L[𝕜] E))
    (hinj : Function.Injective A) : Function.Bijective A := by
  rcases hA.hasEigenvalue_or_mem_resolventSet (neg_ne_zero.mpr hc) with he | hr
  · obtain ⟨v,hv⟩ := he.exists_hasEigenvector
    have hvzero : A v = 0 := by
      have h := hv.apply_eq_smul
      change A v - c • v = -c • v at h
      rw [neg_smul] at h
      exact sub_eq_neg_self.mp h
    exact False.elim (hv.2 (hinj (hvzero.trans (map_zero A).symm)))
  · rw [spectrum.mem_resolventSet_iff] at hr
    have heq : algebraMap 𝕜 (E →L[𝕜] E) (-c) - (A - c • 1) = -A := by
      simp only [Algebra.algebraMap_eq_smul_one, neg_smul]
      abel
    rw [heq, IsUnit.neg_iff, ContinuousLinearMap.isUnit_iff_bijective] at hr
    exact hr

end NLS.CompactScalarPerturbation
