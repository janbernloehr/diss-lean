import NLS.ZakharovShabat.SourceBoundaryContourDomains
import NLS.ZakharovShabat.SourceBoundaryRootSpaces
import NLS.ZakharovShabat.SourceEquation1_4

/-!
# Theorem 1.4: original boundary Riesz ranks and algebraic counts

The actual boundary restrictions of the original contour integrals have ranks
one on high disks and 2N+1 on the central rectangle. These ranks count full
original boundary root spaces. One open convex neighborhood containing the
input and zero supports both signs, analyticity, and every larger cutoff.
The central boxes have height N. This does not assert the separately refuted
all-exponent norm-dependent height printed in Theorem 1.4.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The finite original boundary spectrum in the central box. -/
def sourceBoundaryCentralSpectrum (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .dirichlet) (N : ℕ) : Finset ℂ :=
  b.centralSpectrum hp (CoeffPair.toMax p φ) hφ N

/-- The finite original boundary spectrum in a disk. -/
def sourceBoundaryEnclosedSpectrum (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .dirichlet) (c : ℂ) (r : ℝ) : Finset ℂ :=
  b.enclosedSpectrum hp (CoeffPair.toMax p φ) hφ c r

theorem mem_sourceBoundaryCentralSpectrum (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .dirichlet) (N : ℕ) (z : ℂ) :
    z ∈ sourceBoundaryCentralSpectrum b hp φ hφ N ↔
      z ∈ sourceBoundarySpectrum b hp φ hφ ∧ z ∈ centralSpectralBox N := by
  rw [sourceBoundarySpectrum_eq]
  exact b.mem_centralSpectrum hp (CoeffPair.toMax p φ) hφ N z

theorem mem_sourceBoundaryEnclosedSpectrum (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .dirichlet) (c z : ℂ) (r : ℝ) :
    z ∈ sourceBoundaryEnclosedSpectrum b hp φ hφ c r ↔
      z ∈ sourceBoundarySpectrum b hp φ hφ ∧ z ∈ Metric.ball c r := by
  rw [sourceBoundarySpectrum_eq]
  exact b.mem_enclosedSpectrum hp (CoeffPair.toMax p φ) hφ c z r

/-- The circle restriction counts algebraic multiplicities of the original restricted operator. -/
theorem sourceBoundaryCircleProjection_rank_eq_sum (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .dirichlet) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : Metric.sphere c r ⊆ sourceResolventSet hp φ) :
    Module.finrank ℂ (sourceBoundaryCircleProjection b hp φ c r).range =
      ∑ z ∈ sourceBoundaryEnclosedSpectrum b hp φ hφ c r, sourceBoundaryAlgebraicMultiplicity b hp φ hφ z := by
  simp only [sourceBoundaryAlgebraicMultiplicity_eq,sourceBoundaryEnclosedSpectrum]
  rw [finrank_range_sourceBoundaryCircleProjection b hp φ hφ c r hr hc]
  exact b.finrank_contour_eq_sum_enclosed hp (CoeffPair.toMax p φ) hφ c r hr
    (by rwa [sourceResolventSet_eq] at hc)

/-- The central rectangle counts full original algebraic multiplicities. -/
theorem sourceBoundaryCentralProjection_rank_eq_sum (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : φ ∈ sourceBoundaryBaseSubspace .dirichlet) (N : ℕ)
    (hc : centralRectangleBoundary N ⊆ sourceResolventSet hp φ) :
    Module.finrank ℂ (sourceBoundaryCentralProjection b hp φ N).range =
      ∑ z ∈ sourceBoundaryCentralSpectrum b hp φ hφ N, sourceBoundaryAlgebraicMultiplicity b hp φ hφ z := by
  simp only [sourceBoundaryAlgebraicMultiplicity_eq,sourceBoundaryCentralSpectrum]
  rw [finrank_range_sourceBoundaryCentralProjection b hp φ hφ N hc]
  exact b.finrank_range_centralProjection hp (CoeffPair.toMax p φ) hφ N

/-- Original-norm ranks, with coefficient data retained only after proving root-chain equivalence. -/
structure SourceBoundaryCountingData (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hφ : φ ∈ sourceBoundaryBaseSubspace .dirichlet) (N : ℕ) : Prop where
  coefficient_counts : BoundaryCountingData hp (CoeffPair.toMax p φ) hφ N
  central_rank : ∀ b : BoundaryCondition,
    Module.finrank ℂ (sourceBoundaryCentralProjection b hp φ N).range = 2*N+1
  disk_rank : ∀ b : BoundaryCondition, ∀ n : ℤ, N < n.natAbs →
    Module.finrank ℂ (sourceBoundaryCircleProjection b hp φ ((Real.pi : ℂ)*n) (Real.pi/4)).range = 1

/-- Transport all ranks to the actual original-norm restricted integrals. -/
theorem sourceBoundaryCountingData_of_coefficients (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hφ : φ ∈ sourceBoundaryBaseSubspace .dirichlet) (N : ℕ)
    (h : BoundaryCountingData hp (CoeffPair.toMax p φ) hφ N) : SourceBoundaryCountingData hp φ hφ N := by
  refine ⟨h,?_,?_⟩
  · intro b
    rw [finrank_range_sourceBoundaryCentralProjection b hp φ hφ N
      (by rw [sourceResolventSet_eq]; exact h.periodic.central_boundary)]
    exact h.central_rank b
  · intro b n hn
    rw [finrank_range_sourceBoundaryCircleProjection b hp φ hφ _ _ (by positivity)
      (by rw [sourceResolventSet_eq]; exact h.periodic.disk_resolvent n hn)]
    exact h.disk_rank b n hn

namespace SourceBoundaryCountingData
variable {hp : p ≠ ⊤} {φ : CoeffPair p} {hφ : φ ∈ sourceBoundaryBaseSubspace .dirichlet} {N : ℕ}

theorem central_boundary (h : SourceBoundaryCountingData hp φ hφ N) :
    centralRectangleBoundary N ⊆ sourceResolventSet hp φ := by
  rw [sourceResolventSet_eq]
  exact h.coefficient_counts.periodic.central_boundary

theorem disk_resolvent (h : SourceBoundaryCountingData hp φ hφ N) (n : ℤ) (hn : N < n.natAbs) :
    Metric.sphere ((Real.pi : ℂ)*n) (Real.pi/4) ⊆ sourceResolventSet hp φ := by
  rw [sourceResolventSet_eq]
  exact h.coefficient_counts.periodic.disk_resolvent n hn

theorem spectrum_subset (h : SourceBoundaryCountingData hp φ hφ N) (b : BoundaryCondition) :
    sourceBoundarySpectrum b hp φ hφ ⊆ centralSpectralBox N ∪ highSpectralDisks N (Real.pi/4) := by
  rw [sourceBoundarySpectrum_eq]
  exact h.coefficient_counts.spectrum_subset b

theorem central_multiplicity (h : SourceBoundaryCountingData hp φ hφ N) (b : BoundaryCondition) :
    (∑ z ∈ sourceBoundaryCentralSpectrum b hp φ hφ N, sourceBoundaryAlgebraicMultiplicity b hp φ hφ z) = 2*N+1 := by
  rw [← sourceBoundaryCentralProjection_rank_eq_sum b hp φ hφ N h.central_boundary]
  exact h.central_rank b

theorem disk_multiplicity (h : SourceBoundaryCountingData hp φ hφ N) (b : BoundaryCondition)
    (n : ℤ) (hn : N < n.natAbs) :
    (∑ z ∈ sourceBoundaryEnclosedSpectrum b hp φ hφ ((Real.pi : ℂ)*n) (Real.pi/4),
      sourceBoundaryAlgebraicMultiplicity b hp φ hφ z) = 1 := by
  rw [← sourceBoundaryCircleProjection_rank_eq_sum b hp φ hφ _ _ (by positivity) (h.disk_resolvent n hn)]
  exact h.disk_rank b n hn

/-- Each distant disk contains one spectral point, of original algebraic multiplicity one. -/
theorem disk_unique_simple (h : SourceBoundaryCountingData hp φ hφ N) (b : BoundaryCondition)
    (n : ℤ) (hn : N < n.natAbs) :
    ∃! z : ℂ, z ∈ sourceBoundarySpectrum b hp φ hφ ∧
      z ∈ Metric.ball ((Real.pi : ℂ)*n) (Real.pi/4) ∧ sourceBoundaryAlgebraicMultiplicity b hp φ hφ z = 1 := by
  simp only [sourceBoundaryAlgebraicMultiplicity_eq,sourceBoundarySpectrum_eq]
  exact h.coefficient_counts.disk_unique_simple b n hn

/-- The cutoff excludes the degenerate central rectangle at zero. -/
theorem cutoff_pos (h : SourceBoundaryCountingData hp φ hφ N) : 0 < N :=
  h.coefficient_counts.periodic.cutoff_pos

/-- Every central restriction in the uniform family is an actual finite-rank projection. -/
theorem central_properties (h : SourceBoundaryCountingData hp φ hφ N) (b : BoundaryCondition) :
    IsIdempotentElem (sourceBoundaryCentralProjection b hp φ N) ∧
      FiniteDimensional ℂ (sourceBoundaryCentralProjection b hp φ N).range :=
  sourceBoundaryCentralProjection_properties b hp φ hφ N h.central_boundary

/-- Every high-disk restriction in the uniform family is an actual finite-rank projection. -/
theorem disk_properties (h : SourceBoundaryCountingData hp φ hφ N) (b : BoundaryCondition)
    (n : ℤ) (hn : N < n.natAbs) :
    IsIdempotentElem (sourceBoundaryCircleProjection b hp φ ((Real.pi : ℂ)*n) (Real.pi/4)) ∧
      FiniteDimensional ℂ (sourceBoundaryCircleProjection b hp φ ((Real.pi : ℂ)*n) (Real.pi/4)).range :=
  sourceBoundaryCircleProjection_properties b hp φ hφ _ _ (by positivity) (h.disk_resolvent n hn)

/-- The rank remains 2N+1 for the printed restriction to one-derivative inputs. -/
theorem central_domain_rank (h : SourceBoundaryCountingData hp φ hφ N) (b : BoundaryCondition) :
    Module.finrank ℂ ((sourceBoundaryCentralProjection b hp φ N).comp (sourceBoundaryInclusion b)).range = 2*N+1 := by
  rw [range_sourceBoundaryCentralProjection_comp_inclusion b hp φ hφ N h.central_boundary]
  exact h.central_rank b

/-- The rank remains one for the printed high-disk restriction to one-derivative inputs. -/
theorem disk_domain_rank (h : SourceBoundaryCountingData hp φ hφ N) (b : BoundaryCondition)
    (n : ℤ) (hn : N < n.natAbs) :
    Module.finrank ℂ ((sourceBoundaryCircleProjection b hp φ ((Real.pi : ℂ)*n) (Real.pi/4)).comp
      (sourceBoundaryInclusion b)).range = 1 := by
  rw [range_sourceBoundaryCircleProjection_comp_inclusion b hp φ hφ _ _ (by positivity) (h.disk_resolvent n hn)]
  exact h.disk_rank b n hn

end SourceBoundaryCountingData

/-- One original-input neighborhood supports both analytic restrictions, all ranks,
and all original algebraic counts. Central boxes have height N. -/
theorem exists_uniform_sourceBoundaryCountingData (hp1 : 1 < p) (hp : p ≠ ⊤) (φ : CoeffPair p) :
    ∃ N₀ : ℕ, ∃ U : Set (CoeffPair p), 0 < N₀ ∧ IsOpen U ∧ Convex ℝ U ∧ IsConnected U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ N : ℕ, N₀ ≤ N →
        (∀ b : BoundaryCondition, AnalyticOnNhd ℂ
          (fun ψ => sourceBoundaryCentralProjection b hp (sourceReflectedPotential hp1 hp ψ) N) U) ∧
        (∀ n : ℤ, N < n.natAbs → ∀ b : BoundaryCondition, AnalyticOnNhd ℂ
          (fun ψ => sourceBoundaryCircleProjection b hp (sourceReflectedPotential hp1 hp ψ)
            ((Real.pi : ℂ)*n) (Real.pi/4)) U) ∧
        ∀ ψ ∈ U, SourceBoundaryCountingData hp (sourceReflectedPotential hp1 hp ψ)
          (sourceReflectedPotential_mem hp1 hp ψ) N := by
  let F := sourceReflectedPotentialCLM hp1 hp
  let G : CoeffPair p →L[ℂ] PairSpace p := (CoeffPair.toMax p).toContinuousLinearMap.comp F
  obtain ⟨K,V,hK,hVo,hVc,hφV,h0V,_,_,hdata⟩ := exists_uniform_boundaryCountingData hp (G φ)
  obtain ⟨L,W,hL,hWo,hWc,_,hφW,h0W,ha⟩ := sourceEquation1_4 hp (F φ)
  let U : Set (CoeffPair p) := (F ⁻¹' W) ∩ (G ⁻¹' V)
  have hUconv : Convex ℝ U :=
    (hWc.linear_preimage (F.restrictScalars ℝ).toLinearMap).inter
      (hVc.linear_preimage (G.restrictScalars ℝ).toLinearMap)
  have hU0 : (0 : CoeffPair p) ∈ U := by simpa [U] using And.intro h0W h0V
  have hF (ψ : CoeffPair p) : F ψ = sourceReflectedPotential hp1 hp ψ := sourceReflectedPotentialCLM_apply hp1 hp ψ
  have hG (ψ : CoeffPair p) : G ψ = CoeffPair.toMax p (sourceReflectedPotential hp1 hp ψ) := by
    change CoeffPair.toMax p (F ψ) = _
    rw [hF]
  refine ⟨max K L,U,hK.trans_le (le_max_left _ _),
    (hWo.preimage F.continuous).inter (hVo.preimage G.continuous),hUconv,
    ⟨⟨0,hU0⟩,hUconv.isPreconnected⟩,⟨hφW,hφV⟩,hU0,?_⟩
  intro N hN
  have hKN : K ≤ N := (le_max_left _ _).trans hN
  have hLN : L ≤ N := (le_max_right _ _).trans hN
  have hd (ψ : CoeffPair p) (hψ : ψ ∈ U) :
      SourceBoundaryCountingData hp (sourceReflectedPotential hp1 hp ψ) (sourceReflectedPotential_mem hp1 hp ψ) N := by
    apply sourceBoundaryCountingData_of_coefficients
    have hg : G ψ ∈ dirichletSubspace := by rw [hG]; exact sourceReflectedPotential_mem hp1 hp ψ
    have hh := hdata (G ψ) hψ.2 hg N hKN
    simpa only [hG] using hh
  refine ⟨?_,?_,hd⟩
  · intro b ψ hψ
    have han := ((ha N hLN).1.1 (F ψ) hψ.1).comp (F.analyticAt ψ)
    have han' : AnalyticAt ℂ (fun a => sourceCentralRectangleIntegral hp (sourceReflectedPotential hp1 hp a) N) ψ := by
      simpa only [Function.comp_def,hF] using han
    exact (analyticAt_sourceBoundaryCompression b _).comp
      (f := fun a => sourceCentralRectangleIntegral hp (sourceReflectedPotential hp1 hp a) N) han'
  · intro n hn b ψ hψ
    exact analyticAt_sourceBoundaryCircleProjection b hp1 hp ψ _ _ (by positivity) ((hd ψ hψ).disk_resolvent n hn)

end NLS.ZakharovShabat
