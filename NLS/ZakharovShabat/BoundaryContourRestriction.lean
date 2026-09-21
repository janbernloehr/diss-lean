import NLS.ZakharovShabat.BoundarySpectralReduction
import NLS.ZakharovShabat.ContourReductionMultiplicity

/-!
# Original root chains in finite boundary contour restrictions
The bounded restriction on the actual boundary contour range retains every
original generalized vector. Its characteristic polynomial consequently
uses the restricted operator's original algebraic multiplicities.
-/

noncomputable section
open Complex Metric Topology
open scoped ENNReal
namespace NLS.ZakharovShabat.BoundaryCondition
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] (b : BoundaryCondition)

/-- The bounded original operator restricted to the actual boundary contour range. -/
def contourRestriction (hp : p ≠ ⊤) (φ : PairSpace p) (c : ℂ) (r : ℝ) :
    (b.contourProjection hp φ c r).range →L[ℂ] (b.contourProjection hp φ c r).range :=
  ProjectionTrace.restriction (b.contourProjection hp φ c r) (b.contourOperator hp φ c r)

/-- The boundary contour range is contained in the full periodic contour range. -/
theorem contourRange_le_full (hp : p ≠ ⊤) (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace)
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ ZakharovShabat.resolventSet hp φ) :
    (b.contourProjection hp φ c r).range ≤ (resolventCircleIntegral hp φ c r).range := by
  rw [b.range_contourProjection hp φ hφ c r hr hc]
  exact inf_le_left

/-- On its range the boundary restriction is the original periodic contour operator. -/
theorem contourRestriction_apply (hp : p ≠ ⊤) (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace)
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ ZakharovShabat.resolventSet hp φ)
    (x : (b.contourProjection hp φ c r).range) :
    (b.contourRestriction hp φ c r x : PairSpace p) = ZakharovShabat.contourOperator hp φ c r x := by
  rw [contourRestriction,ProjectionTrace.restriction_apply _ _
    (b.contourProjection_idempotent hp φ hφ c r hr hc)
    (b.contourOperator_commute_projection hp φ hφ c r hr hc)]
  have hb : (x : PairSpace p) ∈ space b :=
    ((b.range_contourProjection hp φ hφ c r hr hc).le.trans inf_le_right) x.property
  have hJ := b.periodicContourLift_projection hp φ hφ c r hr hc x
  rw [b.projection_eq_self hb] at hJ
  change operator hp φ (b.contourLift hp φ c r x) = _
  rw [← hJ]
  rfl

/-- Every finite generalized eigenspace preserves the original operator-domain recursion. -/
theorem contourRestriction_mem_genEigenspace_iff (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (c z : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : sphere c r ⊆ ZakharovShabat.resolventSet hp φ) (k : ℕ)
    (x : (b.contourProjection hp φ c r).range) :
    x ∈ Module.End.genEigenspace (b.contourRestriction hp φ c r).toLinearMap z (k : ℕ∞) ↔
      (x : PairSpace p) ∈ periodicRootSpace hp φ z k := by
  let A := (b.contourRestriction hp φ c r).toLinearMap
  change x ∈ Module.End.genEigenspace A z (k : ℕ∞) ↔ _
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    have he : x ∈ Module.End.genEigenspace A z ((k+1 : ℕ) : ℕ∞) ↔
        (A-z • 1) x ∈ Module.End.genEigenspace A z (k : ℕ∞) := by
      simp only [Module.End.mem_genEigenspace_nat,pow_succ,LinearMap.mem_ker,Module.End.mul_apply]
    rw [he,ih]
    have hx := domainInclusion_contourLift_range hp φ c r hr hc
      ⟨x,b.contourRange_le_full hp φ hφ c r hr hc x.property⟩
    have hd : (((A-z • 1) x : (b.contourProjection hp φ c r).range) : PairSpace p) =
        -spectralPencil hp φ z (resolventCircleIntegralToDomain hp φ c r x) := by
      change (b.contourRestriction hp φ c r x : PairSpace p) - z • (x : PairSpace p) = _
      rw [b.contourRestriction_apply hp φ hφ c r hr hc x,spectralPencil_apply,hx]
      change _ = -(z • (x : PairSpace p)-ZakharovShabat.contourOperator hp φ c r x)
      abel
    rw [hd,Submodule.neg_mem_iff,mem_periodicRootSpace_succ]
    constructor
    · exact fun h => ⟨_,hx,h⟩
    · rintro ⟨f,hf,hfroot⟩
      have hJ : resolventCircleIntegralToDomain hp φ c r x = f :=
        domainInclusion_injective (hx.trans hf.symm)
      simpa only [hJ] using hfroot

/-- The maximal generalized eigenspace is exactly the original full boundary root space in the range. -/
theorem contourRestriction_maxGenEigenspace (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (c z : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : sphere c r ⊆ ZakharovShabat.resolventSet hp φ) :
    Module.End.maxGenEigenspace (b.contourRestriction hp φ c r).toLinearMap z =
      (periodicRootSpaceTop hp φ z ⊓ space b).comap (b.contourProjection hp φ c r).range.subtype := by
  ext x
  have hb : (x : PairSpace p) ∈ space b :=
    ((b.range_contourProjection hp φ hφ c r hr hc).le.trans inf_le_right) x.property
  simp only [Module.End.mem_maxGenEigenspace,Submodule.mem_comap,Submodule.mem_inf,
    Submodule.subtype_apply,hb,and_true,mem_periodicRootSpaceTop]
  apply exists_congr
  intro k
  simpa only [Module.End.mem_genEigenspace_nat,LinearMap.mem_ker] using
    b.contourRestriction_mem_genEigenspace_iff hp φ hφ c z r hr hc k x

/-- Enclosed original boundary root spaces lie wholly in the boundary contour range. -/
theorem rootSpace_le_contourRange (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (c z : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : sphere c r ⊆ ZakharovShabat.resolventSet hp φ) (hz : z ∈ ball c r) :
    periodicRootSpaceTop hp φ z ⊓ space b ≤ (b.contourProjection hp φ c r).range := by
  rw [b.range_contourProjection hp φ hφ c r hr hc]
  exact inf_le_inf_right _ (periodicRootSpaceTop_le_contourRange hp φ c z r hc hz)

/-- The finite characteristic polynomial retains the original restricted-operator multiplicities. -/
theorem contourRestriction_rootMultiplicity (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (c z : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : sphere c r ⊆ ZakharovShabat.resolventSet hp φ) (hz : z ∈ ball c r) :
    letI := b.finiteDimensional_range_contourProjection hp φ c r hr hc
    (b.contourRestriction hp φ c r).toLinearMap.charpoly.rootMultiplicity z =
      b.algebraicMultiplicity hp φ hφ z := by
  let := b.finiteDimensional_range_contourProjection hp φ c r hr hc
  change (b.contourRestriction hp φ c r).toLinearMap.charpoly.rootMultiplicity z = _
  rw [← LinearMap.finrank_maxGenEigenspace_eq,b.contourRestriction_maxGenEigenspace hp φ hφ c z r hr hc]
  exact (Submodule.comapSubtypeEquivOfLe (b.rootSpace_le_contourRange hp φ hφ c z r hr hc hz)).finrank_eq.trans
    (b.finrank_periodicRootSpaceTop_inf hp φ hφ z)

/-- Every eigenvalue of the finite boundary restriction lies inside the original periodic contour. -/
theorem contourRestriction_eigenvalue_mem_periodic (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (c z : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : sphere c r ⊆ ZakharovShabat.resolventSet hp φ)
    (hz : Module.End.HasEigenvalue (b.contourRestriction hp φ c r).toLinearMap z) :
    z ∈ enclosedPeriodicSpectrum hp φ c r := by
  obtain ⟨x,hx⟩ := hz.exists_hasEigenvector
  let y : (resolventCircleIntegral hp φ c r).range :=
    ⟨x,b.contourRange_le_full hp φ hφ c r hr hc x.property⟩
  have hy0 : y ≠ 0 := by
    intro he
    have he0 : (x : PairSpace p) = 0 := congrArg (fun a : (resolventCircleIntegral hp φ c r).range => (a : PairSpace p)) he
    exact hx.2 (Subtype.ext he0)
  have he : (reducedContourOperator hp φ φ c r).toLinearMap y = z • y := by
    apply Subtype.ext
    change (reducedContourOperator hp φ φ c r y : PairSpace p) = z • (x : PairSpace p)
    rw [reducedContourOperator_self_apply hp φ c r hr hc y]
    change ZakharovShabat.contourOperator hp φ c r x = _
    rw [← b.contourRestriction_apply hp φ hφ c r hr hc x]
    exact congrArg (fun a : (b.contourProjection hp φ c r).range => (a : PairSpace p)) hx.apply_eq_smul
  exact (reducedContourOperator_hasEigenvalue_iff hp φ c z r hr hc).mp
    (Module.End.hasEigenvalue_of_hasEigenvector (Module.End.hasEigenvector_iff.mpr
      ⟨Module.End.mem_eigenspace_iff.mpr he,hy0⟩))

end NLS.ZakharovShabat.BoundaryCondition
