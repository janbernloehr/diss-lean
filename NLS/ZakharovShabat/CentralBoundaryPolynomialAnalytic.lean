import NLS.ZakharovShabat.BoundaryContourDeterminant
import NLS.ZakharovShabat.CentralBoundaryPolynomials
import NLS.ZakharovShabat.CentralPolynomialAnalytic

/-!
# Joint analyticity of the intrinsic central boundary polynomials
One neighborhood and threshold make all large central polynomials jointly
analytic for both boundary conditions. The proof uses contour determinants,
so it does not require analytic choices of colliding central eigenvalues.
-/

noncomputable section
open Set Complex Metric Topology Filter
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- When an admissible circle encloses the central cluster, the intrinsic boundary polynomial is its determinant. -/
theorem BoundaryCondition.centralPolynomial_eq_contourDeterminant (b : BoundaryCondition)
    (hp : p ≠ ⊤) (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace) (N : ℕ)
    (hc : sphere 0 (centralCircleRadius N) ⊆ ZakharovShabat.resolventSet hp φ)
    (he : enclosedPeriodicSpectrum hp φ 0 (centralCircleRadius N) = centralPeriodicSpectrum hp φ N) (z : ℂ) :
    b.centralPolynomial hp φ hφ N z = b.contourDeterminant hp φ 0 (centralCircleRadius N) z := by
  rw [b.contourDeterminant_eq_prod hp φ hφ 0 _ (centralCircleRadius_pos N).le hc z]
  simp only [BoundaryCondition.enclosedSpectrum,he,BoundaryCondition.centralPolynomial,BoundaryCondition.centralSpectrum]

/-- Both central boundary polynomials are jointly analytic at all large cutoffs on one neighborhood. -/
theorem exists_uniform_analytic_centralBoundaryPolynomials (hp : p ≠ ⊤) (φ : dirichletSubspace (p := p)) :
    ∃ N₀ : ℕ, ∃ U : Set (dirichletSubspace (p := p)), 0 < N₀ ∧ IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ b : BoundaryCondition, ∀ N ≥ N₀, AnalyticOnNhd ℂ
        (fun t : ℂ × dirichletSubspace (p := p) => b.centralPolynomial hp t.2.val t.2.property N t.1) (univ ×ˢ U) := by
  obtain ⟨N₀,V,hN₀,ho,hconv,hφ,h0,hV⟩ := exists_uniform_centralCircle hp φ.val
  let F := (dirichletSubspace (p := p)).subtypeL
  let U := F ⁻¹' V
  have hUo : IsOpen U := ho.preimage F.continuous
  refine ⟨N₀,U,hN₀,hUo,hconv.linear_preimage (F.restrictScalars ℝ).toLinearMap,hφ,?_,?_⟩
  · simpa only [U,mem_preimage,map_zero] using h0
  · intro b N hN t ht
    apply (b.analyticAt_contourDeterminant hp t.2 0 _ (centralCircleRadius_pos N).le
      (hV t.2.val ht.2 N hN).2.1 t.1).congr
    filter_upwards [(continuous_snd.tendsto t) (hUo.mem_nhds ht.2)] with a ha
    exact (b.centralPolynomial_eq_contourDeterminant hp a.2.val a.2.property N
      (hV a.2.val ha N hN).2.1 (hV a.2.val ha N hN).2.2.1 a.1).symm

/-- The same common neighborhood gives joint analyticity of both normalized intrinsic approximants. -/
theorem exists_uniform_analytic_normalizedCentralBoundaryPolynomials (hp : p ≠ ⊤)
    (φ : dirichletSubspace (p := p)) :
    ∃ N₀ : ℕ, ∃ U : Set (dirichletSubspace (p := p)), 0 < N₀ ∧ IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ b : BoundaryCondition, ∀ N ≥ N₀, AnalyticOnNhd ℂ
        (fun t : ℂ × dirichletSubspace (p := p) => b.normalizedCentralPolynomial hp t.2.val t.2.property N t.1)
        (univ ×ˢ U) := by
  obtain ⟨N₀,U,hN₀,ho,hconv,hφ,h0,h⟩ := exists_uniform_analytic_centralBoundaryPolynomials hp φ
  refine ⟨N₀,U,hN₀,ho,hconv,hφ,h0,?_⟩
  intro b N hN t ht
  exact (h b N hN t ht).neg.div_const

/-- Source period-one potentials inherit common joint analyticity of every sufficiently large boundary approximant. -/
theorem exists_uniform_analytic_periodOneBoundaryPolynomials (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ N₀ : ℕ, ∃ U : Set (CoeffPair p), 0 < N₀ ∧ IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ b : BoundaryCondition, ∀ N ≥ N₀, AnalyticOnNhd ℂ
        (fun t : ℂ × CoeffPair p => b.normalizedCentralPolynomial hp (periodOneBoundaryPotential hp hp1 t.2).val
          (periodOneBoundaryPotential hp hp1 t.2).property N t.1) (univ ×ˢ U) := by
  let F := periodOneBoundaryPotential hp hp1
  obtain ⟨N₀,V,hN₀,ho,hconv,hφ,h0,h⟩ := exists_uniform_analytic_normalizedCentralBoundaryPolynomials hp (F φ)
  refine ⟨N₀,F ⁻¹' V,hN₀,ho.preimage F.continuous,
    hconv.linear_preimage (F.restrictScalars ℝ).toLinearMap,hφ,?_,?_⟩
  · simpa only [mem_preimage,map_zero] using h0
  · intro b N hN t ht
    exact AnalyticAt.comp
      (g := fun a : ℂ × dirichletSubspace (p := p) => b.normalizedCentralPolynomial hp a.2.val a.2.property N a.1)
      (f := fun a : ℂ × CoeffPair p => (a.1,F a.2)) (x := t)
      (h b N hN (t.1,F t.2) ⟨mem_univ _,ht.2⟩)
      (analyticAt_fst.prod (AnalyticAt.comp (g := F) (f := fun a : ℂ × CoeffPair p => a.2)
        (x := t) (F.analyticAt t.2) analyticAt_snd))

end NLS.ZakharovShabat
