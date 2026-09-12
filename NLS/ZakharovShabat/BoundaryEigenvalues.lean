import NLS.ZakharovShabat.BoundarySpectralReduction

/-!
# Analytic simple boundary eigenvalues

The intrinsic trace of the bounded boundary contour restriction equals its
unique simple eigenvalue. Analytic projection transport proves analyticity on
the reflected potential space. One neighborhood and cutoff work for both
Dirichlet and Neumann eigenvalues, as in the coefficient form of Lemma 4.5.
Transfer through the physical interval extension remains separate.
-/

noncomputable section
open Complex Metric Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
namespace BoundaryCondition
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] (b : BoundaryCondition)

/-- Intrinsic trace of the boundary spectral restriction on its full contour range. -/
def contourTrace (hp : p ≠ ⊤) (φ : PairSpace p) (c : ℂ) (r : ℝ) : ℂ :=
  ProjectionTrace.trace (contourProjection b hp φ c r) (contourOperator b hp φ c r)

/-- The trace is analytic on reflected potentials wherever the fixed circle is admissible. -/
theorem analyticAt_contourTrace (hp : p ≠ ⊤) (φ : dirichletSubspace (p := p))
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hc : sphere c r ⊆ ZakharovShabat.resolventSet hp φ.val) :
    AnalyticAt ℂ (fun ψ : dirichletSubspace (p := p) => contourTrace b hp ψ.val c r) φ := by
  let : FiniteDimensional ℂ (contourProjection b hp φ.val c r).range :=
    finiteDimensional_range_contourProjection b hp φ.val c r hr hc
  have hi := (dirichletSubspace (p := p)).subtypeL.analyticAt φ
  have hP : AnalyticAt ℂ (fun ψ : dirichletSubspace (p := p) => contourProjection b hp ψ.val c r) φ :=
    (analyticAt_contourProjection b hp φ.val c r hr hc).comp
    (f := fun ψ : dirichletSubspace (p := p) => ψ.val) hi
  have hA : AnalyticAt ℂ (fun ψ : dirichletSubspace (p := p) => contourOperator b hp ψ.val c r) φ :=
    (analyticAt_contourOperator b hp φ.val c r hr hc).comp
    (f := fun ψ : dirichletSubspace (p := p) => ψ.val) hi
  apply ProjectionTrace.analyticAt_trace hP hA (contourProjection_idempotent b hp φ.val φ.property c r hr hc)
  have hcircle : ∀ᶠ ψ : dirichletSubspace (p := p) in 𝓝 φ,
      sphere c r ⊆ ZakharovShabat.resolventSet hp ψ.val :=
    continuous_subtype_val.continuousAt.eventually ((isOpen_resolventCircleDomain hp c r).mem_nhds hc)
  filter_upwards [hcircle] with ψ hψ
  exact ⟨contourProjection_idempotent b hp ψ.val ψ.property c r hr hψ,
    contourOperator_commute_projection b hp ψ.val ψ.property c r hr hψ⟩

/-- For rank one the intrinsic trace is the actual enclosed boundary eigenvalue. -/
theorem contourTrace_eq_of_rank_one (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (c z : ℂ) (r : ℝ)
    (hc : sphere c r ⊆ ZakharovShabat.resolventSet hp φ)
    (hrank : Module.finrank ℂ (contourProjection b hp φ c r).range = 1)
    (hz : z ∈ enclosedSpectrum b hp φ hφ c r) : contourTrace b hp φ c r = z := by
  obtain ⟨hspec, hball⟩ := (mem_enclosedSpectrum b hp φ hφ c z r).mp hz
  have hr := (pos_of_mem_ball hball).le
  let : FiniteDimensional ℂ (contourProjection b hp φ c r).range :=
    finiteDimensional_range_contourProjection b hp φ c r hr hc
  obtain ⟨f, hb, hf, he⟩ := (mem_spectrum_iff_exists_eigenvector b hp φ hφ z).mp hspec
  have hP : contourProjection b hp φ c r (domainInclusion f) = domainInclusion f := by
    rw [← inclusion_contourLift b hp φ c r hr hc,
      contourLift_apply_eigenvector b hp φ c z r hc hball f hb he]
  let x : (contourProjection b hp φ c r).range := ⟨domainInclusion f, ⟨domainInclusion f, hP⟩⟩
  have hx : x ≠ 0 := by
    intro h
    have hz : domainInclusion f = 0 := congrArg Subtype.val h
    exact hf (domainInclusion_injective (hz.trans (map_zero _).symm))
  exact ProjectionTrace.trace_eq_of_finrank_one _ _
    (contourProjection_idempotent b hp φ hφ c r hr hc)
    (contourOperator_commute_projection b hp φ hφ c r hr hc) hrank z x hx
    (contourOperator_apply_eigenvector b hp φ c z r hc hball f hb he)

/-- The high-index boundary eigenvalue, defined intrinsically by the source's trace formula. -/
def eigenvalue (hp : p ≠ ⊤) (φ : PairSpace p) (n : ℤ) : ℂ :=
  contourTrace b hp φ ((Real.pi : ℂ) * n) (Real.pi / 4)

theorem analyticAt_eigenvalue (hp : p ≠ ⊤) (φ : dirichletSubspace (p := p)) (n : ℤ)
    (hc : sphere ((Real.pi : ℂ) * n) (Real.pi / 4) ⊆ ZakharovShabat.resolventSet hp φ.val) :
    AnalyticAt ℂ (fun ψ : dirichletSubspace (p := p) => eigenvalue b hp ψ.val n) φ :=
  analyticAt_contourTrace b hp φ _ _ (by positivity) hc

/-- Both free boundary eigenvalue functions have the signed value `π n`. -/
theorem eigenvalue_zero (hp : p ≠ ⊤) (n : ℤ) : eigenvalue (p := p) b hp 0 n = (Real.pi : ℂ) * n := by
  have hr : 0 < Real.pi / 4 := by positivity
  have hc : sphere ((Real.pi : ℂ) * n) (Real.pi / 4) ⊆ ZakharovShabat.resolventSet (p := p) hp 0 :=
    sphere_subset_resolventSet_of_smallPotential hp 0 n hr le_rfl (by simpa using hr)
  apply contourTrace_eq_of_rank_one b hp 0 (by simp) _ _ _ hc
  · rw [range_contourProjection b hp 0 (by simp) _ _ hr.le hc, finrank_free_contour_boundary]
  · rw [mem_enclosedSpectrum]
    exact ⟨free_index_mem_spectrum b hp n, by simpa using hr⟩

end BoundaryCondition
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace BoundaryCountingData
variable {hp : p ≠ ⊤} {φ : PairSpace p} {hφ : φ ∈ dirichletSubspace} {N : ℕ}

/-- The trace-defined function is exactly the unique simple eigenvalue in the high disk. -/
theorem eigenvalue_spec (h : BoundaryCountingData hp φ hφ N) (b : BoundaryCondition)
    (n : ℤ) (hn : N < n.natAbs) :
    b.enclosedSpectrum hp φ hφ ((Real.pi : ℂ) * n) (Real.pi / 4) = {b.eigenvalue hp φ n} ∧
      b.algebraicMultiplicity hp φ hφ (b.eigenvalue hp φ n) = 1 := by
  obtain ⟨z, hz, hm⟩ := h.disk_spectrum_eq_singleton b n hn
  have hzmem : z ∈ b.enclosedSpectrum hp φ hφ ((Real.pi : ℂ) * n) (Real.pi / 4) := by simp [hz]
  have ht : b.eigenvalue hp φ n = z := BoundaryCondition.contourTrace_eq_of_rank_one b hp φ hφ
    _ z _ (h.periodic.disk_resolvent n hn) (h.disk_rank b n hn) hzmem
  rw [ht]
  exact ⟨hz, hm⟩

theorem eigenvalue_mem_spectrum (h : BoundaryCountingData hp φ hφ N) (b : BoundaryCondition)
    (n : ℤ) (hn : N < n.natAbs) : b.eigenvalue hp φ n ∈ b.spectrum hp φ hφ ∧
      b.eigenvalue hp φ n ∈ ball ((Real.pi : ℂ) * n) (Real.pi / 4) := by
  apply (BoundaryCondition.mem_enclosedSpectrum b hp φ hφ _ _ _).mp
  rw [(h.eigenvalue_spec b n hn).1]
  exact Finset.mem_singleton_self _

/-- The returned scalar has a nonzero eigenfunction in the actual weighted boundary domain. -/
theorem exists_eigenvector_eigenvalue (h : BoundaryCountingData hp φ hφ N) (b : BoundaryCondition)
    (n : ℤ) (hn : N < n.natAbs) : ∃ f : Domain p, f ∈ b.domain ∧ f ≠ 0 ∧
      operator hp φ f = b.eigenvalue hp φ n • domainInclusion f :=
  (BoundaryCondition.mem_spectrum_iff_exists_eigenvector b hp φ hφ _).mp
    (h.eigenvalue_mem_spectrum b n hn).1

end BoundaryCountingData

/-- Lemma 4.5 for reflected coefficient potentials: both simple eigenvalue functions
are analytic on one open convex neighborhood, with the same uniform counting data. -/
theorem exists_uniform_analytic_boundaryEigenvalues (hp : p ≠ ⊤)
    (φ : dirichletSubspace (p := p)) :
    ∃ N₀ : ℕ, ∃ U : Set ↥(dirichletSubspace (p := p)),
      0 < N₀ ∧ IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      (∀ ψ ∈ U, ∀ N : ℕ, N₀ ≤ N → BoundaryCountingData hp ψ.val ψ.property N) ∧
      ∀ b : BoundaryCondition, ∀ n : ℤ, N₀ < n.natAbs →
        AnalyticOnNhd ℂ (fun ψ : dirichletSubspace (p := p) => b.eigenvalue hp ψ.val n) U ∧
        ∀ ψ ∈ U, b.enclosedSpectrum hp ψ.val ψ.property ((Real.pi : ℂ) * n) (Real.pi / 4) =
          {b.eigenvalue hp ψ.val n} ∧ b.algebraicMultiplicity hp ψ.val ψ.property (b.eigenvalue hp ψ.val n) = 1 := by
  obtain ⟨N₀, V, hN₀, ho, hconv, hφ, h0, _, _, hdata⟩ := exists_uniform_boundaryCountingData hp φ.val
  let U : Set ↥(dirichletSubspace (p := p)) := Subtype.val ⁻¹' V
  have hoU : IsOpen U := ho.preimage continuous_subtype_val
  have hconvU : Convex ℝ U := hconv.linear_preimage
    ((dirichletSubspace (p := p)).subtype.restrictScalars ℝ)
  have hU (ψ : dirichletSubspace (p := p)) (hψ : ψ ∈ U) (N : ℕ) (hN : N₀ ≤ N) :
      BoundaryCountingData hp ψ.val ψ.property N := hdata ψ.val hψ ψ.property N hN
  refine ⟨N₀, U, hN₀, hoU, hconvU, hφ, h0, hU, ?_⟩
  intro b n hn
  refine ⟨?_, fun ψ hψ => (hU ψ hψ N₀ le_rfl).eigenvalue_spec b n hn⟩
  intro ψ hψ
  exact BoundaryCondition.analyticAt_eigenvalue b hp ψ n ((hU ψ hψ N₀ le_rfl).periodic.disk_resolvent n hn)

end NLS.ZakharovShabat
