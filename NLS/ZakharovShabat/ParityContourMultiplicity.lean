import NLS.ZakharovShabat.ParityContourDeterminant

/-!
# Original generalized multiplicities in parity contour reductions

Every finite root chain of the reduction is an original root chain lying in
the chosen parity range. The determinant consequently retains parity Jordan
multiplicities, including roots shared by the two sectors.
-/

noncomputable section
open Complex Metric Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Inclusion of a parity contour range in the full range. -/
theorem parityContourRange_le_full (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (c : ℂ) (R : ℝ) (r : ℤ)
    (hR : 0 ≤ R) (hc : sphere c R ⊆ resolventSet hp φ) :
    (parityContourProjection hp φ c R r).range ≤ (resolventCircleIntegral hp φ c R).range := by
  rw [range_parityContourProjection hp φ hφ c R r hR hc]
  exact inf_le_left

/-- The parity reduction retains the original domain recursion at every finite chain length. -/
theorem reducedParityContourOperator_mem_genEigenspace_iff (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (c z : ℂ) (R : ℝ) (r : ℤ)
    (hR : 0 ≤ R) (hc : sphere c R ⊆ resolventSet hp φ) (k : ℕ)
    (x : (parityContourProjection hp φ c R r).range) :
    x ∈ Module.End.genEigenspace (reducedParityContourOperator hp φ φ c R r).toLinearMap z (k : ℕ∞) ↔
      (x : PairSpace p) ∈ periodicRootSpace hp φ z k := by
  let A := (reducedParityContourOperator hp φ φ c R r).toLinearMap
  change x ∈ Module.End.genEigenspace A z (k : ℕ∞) ↔ _
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    have he : x ∈ Module.End.genEigenspace A z ((k+1 : ℕ) : ℕ∞) ↔
        (A-z • 1) x ∈ Module.End.genEigenspace A z (k : ℕ∞) := by
      simp only [Module.End.mem_genEigenspace_nat, pow_succ, LinearMap.mem_ker, Module.End.mul_apply]
    rw [he, ih]
    have hx := domainInclusion_contourLift_range hp φ c R hR hc
      ⟨x, parityContourRange_le_full hp φ hφ c R r hR hc x.property⟩
    have hd : (((A-z • 1) x : (parityContourProjection hp φ c R r).range) : PairSpace p) =
        -spectralPencil hp φ z (resolventCircleIntegralToDomain hp φ c R x) := by
      change (reducedParityContourOperator hp φ φ c R r x : PairSpace p) - z • (x : PairSpace p) = _
      rw [reducedParityContourOperator_self_apply hp φ hφ c R r hR hc x, spectralPencil_apply, hx]
      change _ = -(z • (x : PairSpace p) - contourOperator hp φ c R x)
      abel
    rw [hd, Submodule.neg_mem_iff, mem_periodicRootSpace_succ]
    constructor
    · exact fun h => ⟨_,hx,h⟩
    · rintro ⟨f,hf,hfroot⟩
      have hJ : resolventCircleIntegralToDomain hp φ c R x = f :=
        domainInclusion_injective (hx.trans hf.symm)
      simpa only [hJ] using hfroot

/-- The maximal generalized eigenspace is the pullback of the original parity root space. -/
theorem reducedParityContourOperator_maxGenEigenspace (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (c z : ℂ) (R : ℝ) (r : ℤ)
    (hR : 0 ≤ R) (hc : sphere c R ⊆ resolventSet hp φ) :
    Module.End.maxGenEigenspace (reducedParityContourOperator hp φ φ c R r).toLinearMap z =
      (periodicRootSpaceTop hp φ z ⊓ pairParitySubspace r).comap
        (parityContourProjection hp φ c R r).range.subtype := by
  ext x
  have hpar : (x : PairSpace p) ∈ pairParitySubspace r := by
    exact ((range_parityContourProjection hp φ hφ c R r hR hc).le.trans inf_le_right) x.property
  simp only [Module.End.mem_maxGenEigenspace, Submodule.mem_comap, Submodule.mem_inf,
    Submodule.subtype_apply, hpar, and_true, mem_periodicRootSpaceTop]
  apply exists_congr
  intro k
  simpa only [Module.End.mem_genEigenspace_nat, LinearMap.mem_ker] using
    reducedParityContourOperator_mem_genEigenspace_iff hp φ hφ c z R r hR hc k x

/-- Every enclosed original parity root space lies in the selected contour range. -/
theorem parityRootSpace_le_parityContourRange (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (c z : ℂ) (R : ℝ) (r : ℤ)
    (hR : 0 ≤ R) (hc : sphere c R ⊆ resolventSet hp φ) (hz : z ∈ ball c R) :
    periodicRootSpaceTop hp φ z ⊓ pairParitySubspace r ≤ (parityContourProjection hp φ c R r).range := by
  rw [range_parityContourProjection hp φ hφ c R r hR hc]
  exact inf_le_inf_right _ (periodicRootSpaceTop_le_contourRange hp φ c z R hc hz)

/-- Characteristic-root multiplicity equals the original parity generalized dimension. -/
theorem reducedParityContourOperator_rootMultiplicity (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (c z : ℂ) (R : ℝ) (r : ℤ)
    (hR : 0 ≤ R) (hc : sphere c R ⊆ resolventSet hp φ) (hz : z ∈ ball c R) :
    letI := finiteDimensional_range_parityContourProjection hp φ hφ c R r hR hc
    (reducedParityContourOperator hp φ φ c R r).toLinearMap.charpoly.rootMultiplicity z =
      parityAlgebraicMultiplicity hp φ r z := by
  let := finiteDimensional_range_parityContourProjection hp φ hφ c R r hR hc
  change (reducedParityContourOperator hp φ φ c R r).toLinearMap.charpoly.rootMultiplicity z = _
  rw [← LinearMap.finrank_maxGenEigenspace_eq,
    reducedParityContourOperator_maxGenEigenspace hp φ hφ c z R r hR hc]
  exact (Submodule.comapSubtypeEquivOfLe
    (parityRootSpace_le_parityContourRange hp φ hφ c z R r hR hc hz)).finrank_eq

/-- Every eigenvalue of the parity restriction belongs to the original enclosed spectrum. -/
theorem reducedParityContourOperator_eigenvalue_mem (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (c z : ℂ) (R : ℝ) (r : ℤ)
    (hR : 0 ≤ R) (hc : sphere c R ⊆ resolventSet hp φ)
    (hz : Module.End.HasEigenvalue (reducedParityContourOperator hp φ φ c R r).toLinearMap z) :
    z ∈ enclosedPeriodicSpectrum hp φ c R := by
  obtain ⟨x,hx⟩ := hz.exists_hasEigenvector
  let y : (resolventCircleIntegral hp φ c R).range :=
    ⟨x, parityContourRange_le_full hp φ hφ c R r hR hc x.property⟩
  have hy0 : y ≠ 0 := by
    intro he
    have he0 : (x : PairSpace p) = 0 := congrArg (fun a : (resolventCircleIntegral hp φ c R).range => (a : PairSpace p)) he
    exact hx.2 (Subtype.ext he0)
  have he : (reducedContourOperator hp φ φ c R).toLinearMap y = z • y := by
    apply Subtype.ext
    change (reducedContourOperator hp φ φ c R y : PairSpace p) = z • (x : PairSpace p)
    rw [reducedContourOperator_self_apply hp φ c R hR hc y]
    change contourOperator hp φ c R x = _
    rw [← reducedParityContourOperator_self_apply hp φ hφ c R r hR hc x]
    exact congrArg (fun a : (parityContourProjection hp φ c R r).range => (a : PairSpace p)) hx.apply_eq_smul
  exact (reducedContourOperator_hasEigenvalue_iff hp φ c z R hR hc).mp
    (Module.End.hasEigenvalue_of_hasEigenvector (Module.End.hasEigenvector_iff.mpr
      ⟨Module.End.mem_eigenspace_iff.mpr he,hy0⟩))

/-- The parity determinant is the original finite root product with all parity multiplicities. -/
theorem parityContourDeterminant_eq_prod (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (c : ℂ) (R : ℝ) (r : ℤ)
    (hR : 0 ≤ R) (hc : sphere c R ⊆ resolventSet hp φ) (z : ℂ) :
    parityContourDeterminant hp φ c R r z =
      ∏ a ∈ enclosedPeriodicSpectrum hp φ c R, (a-z)^parityAlgebraicMultiplicity hp φ r a := by
  classical
  let := finiteDimensional_range_parityContourProjection hp φ hφ c R r hR hc
  let A := (reducedParityContourOperator hp φ φ c R r).toLinearMap
  have hs : A.charpoly.roots.toFinset ⊆ enclosedPeriodicSpectrum hp φ c R := by
    intro a ha
    simp only [Multiset.mem_toFinset, Polynomial.mem_roots A.charpoly_monic.ne_zero,
      ← Module.End.hasEigenvalue_iff_isRoot_charpoly] at ha
    exact reducedParityContourOperator_eigenvalue_mem hp φ hφ c a R r hR hc ha
  change (A-z • 1).det = _
  rw [FiniteSpectralDeterminant.shifted_det_eq_prod_roots]
  calc
    _ = ∏ a ∈ enclosedPeriodicSpectrum hp φ c R, (a-z)^A.charpoly.rootMultiplicity a := by
      apply Finset.prod_subset hs
      intro a _ ha
      have hn : ¬ A.charpoly.IsRoot a := by
        simpa only [Multiset.mem_toFinset, Polynomial.mem_roots A.charpoly_monic.ne_zero] using ha
      rw [Polynomial.rootMultiplicity_eq_zero hn, pow_zero]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro a ha
      rw [reducedParityContourOperator_rootMultiplicity hp φ hφ c a R r hR hc
        ((mem_enclosedPeriodicSpectrum hp φ c a R).mp ha).2]

end NLS.ZakharovShabat
