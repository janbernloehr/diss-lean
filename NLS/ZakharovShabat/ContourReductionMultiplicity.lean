import NLS.ZakharovShabat.SymmetricEigenvalues
import Mathlib.LinearAlgebra.Eigenspace.Zero

/-!
# Original multiplicities in the contour reduction

Generalized eigenvectors of the finite contour restriction are exactly the
original recursive root vectors lying in its range. Thus its characteristic
polynomial counts the original algebraic multiplicities, including Jordan blocks.
-/

noncomputable section
open Complex Metric Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The domain-valued contour map lifts a vector in the spectral range itself. -/
theorem domainInclusion_contourLift_range (hp : p ≠ ⊤) (φ : PairSpace p)
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp φ)
    (x : (resolventCircleIntegral hp φ c r).range) :
    domainInclusion (resolventCircleIntegralToDomain hp φ c r x) = (x : PairSpace p) := by
  rw [← ContinuousLinearMap.comp_apply, ← resolventCircleIntegral_eq_inclusion hp φ c r hr hc]
  obtain ⟨y,hy⟩ := x.property
  change resolventCircleIntegral hp φ c r y = (x : PairSpace p) at hy
  rw [← hy]
  exact congrArg (fun A : PairSpace p →L[ℂ] PairSpace p => A y)
    (resolventCircleIntegral_idempotent hp φ c r hr hc)

/-- At every finite chain length the reduction retains the original operator-domain recursion. -/
theorem reducedContourOperator_mem_genEigenspace_iff (hp : p ≠ ⊤) (φ : PairSpace p)
    (c z : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp φ) (k : ℕ)
    (x : (resolventCircleIntegral hp φ c r).range) :
    x ∈ Module.End.genEigenspace (reducedContourOperator hp φ φ c r).toLinearMap z (k : ℕ∞) ↔
      (x : PairSpace p) ∈ periodicRootSpace hp φ z k := by
  let A := (reducedContourOperator hp φ φ c r).toLinearMap
  change x ∈ Module.End.genEigenspace A z (k : ℕ∞) ↔ _
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    have he : x ∈ Module.End.genEigenspace A z ((k+1 : ℕ) : ℕ∞) ↔
        (A-z • 1) x ∈ Module.End.genEigenspace A z (k : ℕ∞) := by
      simp only [Module.End.mem_genEigenspace_nat, pow_succ, LinearMap.mem_ker, Module.End.mul_apply]
    rw [he, ih]
    have hx := domainInclusion_contourLift_range hp φ c r hr hc x
    have hd : (((A-z • 1) x : (resolventCircleIntegral hp φ c r).range) : PairSpace p) =
        -spectralPencil hp φ z (resolventCircleIntegralToDomain hp φ c r x) := by
      change (reducedContourOperator hp φ φ c r x : PairSpace p) - z • (x : PairSpace p) = _
      rw [reducedContourOperator_self_apply hp φ c r hr hc x, spectralPencil_apply, hx]
      change _ = -(z • (x : PairSpace p) - contourOperator hp φ c r x)
      abel
    rw [hd, Submodule.neg_mem_iff, mem_periodicRootSpace_succ]
    constructor
    · exact fun h => ⟨_,hx,h⟩
    · rintro ⟨f,hf,hfroot⟩
      have hJ : resolventCircleIntegralToDomain hp φ c r x = f :=
        domainInclusion_injective (hx.trans hf.symm)
      simpa only [hJ] using hfroot

/-- The full generalized eigenspace is the pullback of the original full root space. -/
theorem reducedContourOperator_maxGenEigenspace (hp : p ≠ ⊤) (φ : PairSpace p)
    (c z : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp φ) :
    Module.End.maxGenEigenspace (reducedContourOperator hp φ φ c r).toLinearMap z =
      (periodicRootSpaceTop hp φ z).comap (resolventCircleIntegral hp φ c r).range.subtype := by
  ext x
  simp only [Module.End.mem_maxGenEigenspace, Submodule.mem_comap, mem_periodicRootSpaceTop]
  apply exists_congr
  intro k
  simpa only [Module.End.mem_genEigenspace_nat, LinearMap.mem_ker, Submodule.subtype_apply] using
    reducedContourOperator_mem_genEigenspace_iff hp φ c z r hr hc k x

/-- Each enclosed root space lies in the contour range, with all generalized vectors. -/
theorem periodicRootSpaceTop_le_contourRange (hp : p ≠ ⊤) (φ : PairSpace p)
    (c z : ℂ) (r : ℝ) (hc : sphere c r ⊆ resolventSet hp φ) (hz : z ∈ ball c r) :
    periodicRootSpaceTop hp φ z ≤ (resolventCircleIntegral hp φ c r).range := by
  intro x hx
  exact ⟨x,resolventCircleIntegral_apply_root hp φ c z r hc hz x hx⟩

/-- The finite reduction's characteristic-root multiplicity is the actual original multiplicity. -/
theorem reducedContourOperator_rootMultiplicity (hp : p ≠ ⊤) (φ : PairSpace p)
    (c z : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ resolventSet hp φ)
    (hz : z ∈ ball c r) :
    letI := finiteDimensional_range_resolventCircleIntegral hp φ c r hr hc
    (reducedContourOperator hp φ φ c r).toLinearMap.charpoly.rootMultiplicity z =
      periodicAlgebraicMultiplicity hp φ z := by
  let := finiteDimensional_range_resolventCircleIntegral hp φ c r hr hc
  change (reducedContourOperator hp φ φ c r).toLinearMap.charpoly.rootMultiplicity z = _
  rw [← LinearMap.finrank_maxGenEigenspace_eq, reducedContourOperator_maxGenEigenspace hp φ c z r hr hc]
  exact (Submodule.comapSubtypeEquivOfLe (periodicRootSpaceTop_le_contourRange hp φ c z r hc hz)).finrank_eq

end NLS.ZakharovShabat
