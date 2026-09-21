import NLS.ZakharovShabat.BoundaryContourRestriction
import NLS.FunctionalAnalysis.ProjectionDeterminant

/-!
# Analytic boundary contour determinants
The determinant on the actual finite boundary spectral range is jointly
analytic in the spectral parameter and reflected potential. It equals the
finite product of original boundary roots, including algebraic multiplicities.
-/

noncomputable section
open Set Complex Metric Topology Filter
open scoped ENNReal Classical
namespace NLS.ZakharovShabat.BoundaryCondition
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] (b : BoundaryCondition)

/-- The determinant of the actual boundary contour restriction, with root-minus-parameter orientation. -/
def contourDeterminant (hp : p ≠ ⊤) (φ : PairSpace p) (c : ℂ) (r : ℝ) (z : ℂ) : ℂ :=
  ProjectionDeterminant.determinant (b.contourProjection hp φ c r) (b.contourOperator hp φ c r) z

/-- The boundary contour determinant is jointly analytic on reflected potentials at every admissible circle. -/
theorem analyticAt_contourDeterminant (hp : p ≠ ⊤) (φ : dirichletSubspace (p := p))
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ ZakharovShabat.resolventSet hp φ.val) (z : ℂ) :
    AnalyticAt ℂ (fun t : ℂ × dirichletSubspace (p := p) => b.contourDeterminant hp t.2.val c r t.1) (z,φ) := by
  let : FiniteDimensional ℂ (b.contourProjection hp φ.val c r).range :=
    b.finiteDimensional_range_contourProjection hp φ.val c r hr hc
  have hi : AnalyticAt ℂ (fun t : ℂ × dirichletSubspace (p := p) => t.2.val) (z,φ) :=
    ((dirichletSubspace (p := p)).subtypeL.analyticAt φ).comp analyticAt_snd
  have hP : AnalyticAt ℂ (fun t : ℂ × dirichletSubspace (p := p) => b.contourProjection hp t.2.val c r) (z,φ) :=
    AnalyticAt.comp (g := fun ψ : PairSpace p => b.contourProjection hp ψ c r)
      (f := fun t : ℂ × dirichletSubspace (p := p) => t.2.val) (x := (z,φ))
      (b.analyticAt_contourProjection hp φ.val c r hr hc) hi
  have hA : AnalyticAt ℂ (fun t : ℂ × dirichletSubspace (p := p) => b.contourOperator hp t.2.val c r) (z,φ) :=
    AnalyticAt.comp (g := fun ψ : PairSpace p => b.contourOperator hp ψ c r)
      (f := fun t : ℂ × dirichletSubspace (p := p) => t.2.val) (x := (z,φ))
      (b.analyticAt_contourOperator hp φ.val c r hr hc) hi
  apply ProjectionDeterminant.analyticAt_determinant hP hA analyticAt_fst
    (b.contourProjection_idempotent hp φ.val φ.property c r hr hc)
  have hcircle : ∀ᶠ t : ℂ × dirichletSubspace (p := p) in 𝓝 (z,φ),
      sphere c r ⊆ ZakharovShabat.resolventSet hp t.2.val :=
    ((isOpen_resolventCircleDomain hp c r).preimage
      (show Continuous (fun t : ℂ × dirichletSubspace (p := p) => t.2.val) from
        continuous_subtype_val.comp continuous_snd)).mem_nhds hc
  filter_upwards [hcircle] with t ht
  exact ⟨b.contourProjection_idempotent hp t.2.val t.2.property c r hr ht,
    b.contourOperator_commute_projection hp t.2.val t.2.property c r hr ht⟩

/-- The determinant uses original boundary multiplicities throughout the enclosed periodic cluster. -/
theorem contourDeterminant_eq_periodicProd (hp : p ≠ ⊤) (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace)
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ ZakharovShabat.resolventSet hp φ) (z : ℂ) :
    b.contourDeterminant hp φ c r z =
      ∏ a ∈ enclosedPeriodicSpectrum hp φ c r, (a-z)^b.algebraicMultiplicity hp φ hφ a := by
  let := b.finiteDimensional_range_contourProjection hp φ c r hr hc
  let A := (b.contourRestriction hp φ c r).toLinearMap
  have hs : A.charpoly.roots.toFinset ⊆ enclosedPeriodicSpectrum hp φ c r := by
    intro a ha
    simp only [Multiset.mem_toFinset,Polynomial.mem_roots A.charpoly_monic.ne_zero,
      ← Module.End.hasEigenvalue_iff_isRoot_charpoly] at ha
    exact b.contourRestriction_eigenvalue_mem_periodic hp φ hφ c a r hr hc ha
  change (A-z • 1).det = _
  rw [FiniteSpectralDeterminant.shifted_det_eq_prod_roots]
  calc
    _ = ∏ a ∈ enclosedPeriodicSpectrum hp φ c r, (a-z)^A.charpoly.rootMultiplicity a := by
      apply Finset.prod_subset hs
      intro a _ ha
      have hn : ¬ A.charpoly.IsRoot a := by
        simpa only [Multiset.mem_toFinset,Polynomial.mem_roots A.charpoly_monic.ne_zero] using ha
      rw [Polynomial.rootMultiplicity_eq_zero hn,pow_zero]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro a ha
      rw [b.contourRestriction_rootMultiplicity hp φ hφ c a r hr hc
        ((mem_enclosedPeriodicSpectrum hp φ c a r).mp ha).2]

/-- Filtering out the other boundary condition leaves exactly the actual boundary root product. -/
theorem contourDeterminant_eq_prod (hp : p ≠ ⊤) (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace)
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ ZakharovShabat.resolventSet hp φ) (z : ℂ) :
    b.contourDeterminant hp φ c r z =
      ∏ a ∈ b.enclosedSpectrum hp φ hφ c r, (a-z)^b.algebraicMultiplicity hp φ hφ a := by
  rw [b.contourDeterminant_eq_periodicProd hp φ hφ c r hr hc z,enclosedSpectrum,Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro a _
  by_cases ha : a ∈ b.spectrum hp φ hφ
  · rw [if_pos ha]
  · rw [if_neg ha,(b.algebraicMultiplicity_eq_zero_iff hp φ hφ a).mpr (by simpa [spectrum] using ha),pow_zero]

/-- Finite boundary products are jointly analytic even when individual central roots collide. -/
theorem analyticAt_enclosedPolynomial (hp : p ≠ ⊤) (φ : dirichletSubspace (p := p))
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ ZakharovShabat.resolventSet hp φ.val) (z : ℂ) :
    AnalyticAt ℂ (fun t : ℂ × dirichletSubspace (p := p) =>
      ∏ a ∈ b.enclosedSpectrum hp t.2.val t.2.property c r,
        (a-t.1)^b.algebraicMultiplicity hp t.2.val t.2.property a) (z,φ) := by
  apply (b.analyticAt_contourDeterminant hp φ c r hr hc z).congr
  have hcircle : ∀ᶠ t : ℂ × dirichletSubspace (p := p) in 𝓝 (z,φ),
      sphere c r ⊆ ZakharovShabat.resolventSet hp t.2.val :=
    ((isOpen_resolventCircleDomain hp c r).preimage
      (show Continuous (fun t : ℂ × dirichletSubspace (p := p) => t.2.val) from
        continuous_subtype_val.comp continuous_snd)).mem_nhds hc
  filter_upwards [hcircle] with t ht
  exact b.contourDeterminant_eq_prod hp t.2.val t.2.property c r hr ht t.1

end NLS.ZakharovShabat.BoundaryCondition
