import NLS.ZakharovShabat.SourceAuxiliaryContourRanks
import NLS.ZakharovShabat.SourceEquation1_4

/-!
# Uniform original auxiliary Cauchy–Riesz ranks

The actual original auxiliary restrictions are analytic finite-rank projections
on one open convex connected input neighborhood containing the potential and
zero. Every sufficiently large central rectangle has rank 2N+1 and each high
circle has rank one, for both signs. Restricting inputs to the original
one-derivative domain leaves these ranges and ranks unchanged. The boxes here
have height N; the general printed norm-dependent height remains separate.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
open BoundaryCondition
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Original auxiliary counts together with admissibility of the actual ambient contours. -/
structure SourceAuxiliaryContourData (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hφ : φ ∈ sourceBoundaryBaseSubspace .neumann) (N : ℕ) : Prop where
  counts : SourceAuxiliaryCountingData hp φ hφ N
  central_boundary : centralRectangleBoundary N ⊆ sourceResolventSet hp φ
  disk_resolvent : ∀ n : ℤ, N < n.natAbs →
    Metric.sphere ((Real.pi : ℂ)*n) (Real.pi/4) ⊆ sourceResolventSet hp φ

namespace SourceAuxiliaryContourData
variable {hp : p ≠ ⊤} {φ : CoeffPair p} {hφ : φ ∈ sourceBoundaryBaseSubspace .neumann} {N : ℕ}

/-- The actual central restricted integral has rank 2N+1 for either auxiliary sign. -/
theorem central_rank (h : SourceAuxiliaryContourData hp φ hφ N) (b : BoundaryCondition) :
    Module.finrank ℂ (sourceAuxiliaryCentralProjection b hp φ N).range = 2*N+1 := by
  rw [sourceAuxiliaryCentralProjection_rank_eq_sum b hp φ hφ N h.central_boundary]
  exact h.counts.central_multiplicity b

/-- Every actual high-disk restricted integral has rank one. -/
theorem disk_rank (h : SourceAuxiliaryContourData hp φ hφ N) (b : BoundaryCondition)
    (n : ℤ) (hn : N < n.natAbs) :
    Module.finrank ℂ (sourceAuxiliaryCircleProjection b hp φ ((Real.pi : ℂ)*n) (Real.pi/4)).range = 1 := by
  rw [sourceAuxiliaryCircleProjection_rank_eq_sum b hp φ hφ _ _ (by positivity) (h.disk_resolvent n hn)]
  exact h.counts.disk_multiplicity b n hn

theorem central_properties (h : SourceAuxiliaryContourData hp φ hφ N) (b : BoundaryCondition) :
    IsIdempotentElem (sourceAuxiliaryCentralProjection b hp φ N) ∧
      FiniteDimensional ℂ (sourceAuxiliaryCentralProjection b hp φ N).range :=
  sourceAuxiliaryCentralProjection_properties b hp φ hφ N h.central_boundary

theorem disk_properties (h : SourceAuxiliaryContourData hp φ hφ N) (b : BoundaryCondition)
    (n : ℤ) (hn : N < n.natAbs) :
    IsIdempotentElem (sourceAuxiliaryCircleProjection b hp φ ((Real.pi : ℂ)*n) (Real.pi/4)) ∧
      FiniteDimensional ℂ (sourceAuxiliaryCircleProjection b hp φ ((Real.pi : ℂ)*n) (Real.pi/4)).range :=
  sourceAuxiliaryCircleProjection_properties b hp φ hφ _ _ (by positivity) (h.disk_resolvent n hn)

/-- The printed central restriction to one-derivative inputs retains the same rank. -/
theorem central_domain_rank (h : SourceAuxiliaryContourData hp φ hφ N) (b : BoundaryCondition) :
    Module.finrank ℂ ((sourceAuxiliaryCentralProjection b hp φ N).comp (sourceAuxiliaryInclusion b)).range = 2*N+1 := by
  rw [range_sourceAuxiliaryCentralProjection_comp_inclusion b hp φ hφ N h.central_boundary]
  exact h.central_rank b

/-- The printed high-disk restriction to one-derivative inputs retains rank one. -/
theorem disk_domain_rank (h : SourceAuxiliaryContourData hp φ hφ N) (b : BoundaryCondition)
    (n : ℤ) (hn : N < n.natAbs) :
    Module.finrank ℂ ((sourceAuxiliaryCircleProjection b hp φ ((Real.pi : ℂ)*n) (Real.pi/4)).comp
      (sourceAuxiliaryInclusion b)).range = 1 := by
  rw [range_sourceAuxiliaryCircleProjection_comp_inclusion b hp φ hφ _ _ (by positivity) (h.disk_resolvent n hn)]
  exact h.disk_rank b n hn

end SourceAuxiliaryContourData

/-- One original-input neighborhood supports both analytic restrictions, domain ranks,
and full Jordan counts, simultaneously for every larger cutoff. -/
theorem exists_uniform_sourceAuxiliaryContourData (hp1 : 1 < p) (hp : p ≠ ⊤) (φ : CoeffPair p) :
    ∃ N₀ : ℕ, ∃ U : Set (CoeffPair p), 0 < N₀ ∧ IsOpen U ∧ Convex ℝ U ∧ IsConnected U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ N : ℕ, N₀ ≤ N →
        (∀ b : BoundaryCondition, AnalyticOnNhd ℂ
          (fun ψ => sourceAuxiliaryCentralProjection b hp (sourceAuxiliaryReflectedPotential hp1 hp ψ) N) U) ∧
        (∀ n : ℤ, N < n.natAbs → ∀ b : BoundaryCondition, AnalyticOnNhd ℂ
          (fun ψ => sourceAuxiliaryCircleProjection b hp (sourceAuxiliaryReflectedPotential hp1 hp ψ)
            ((Real.pi : ℂ)*n) (Real.pi/4)) U) ∧
        ∀ ψ ∈ U, SourceAuxiliaryContourData hp (sourceAuxiliaryReflectedPotential hp1 hp ψ)
          (sourceAuxiliaryReflectedPotential_mem hp1 hp ψ) N := by
  let F := sourceAuxiliaryReflectedPotentialCLM hp1 hp
  obtain ⟨K,V,hK,hVo,hVc,_,hφV,h0V,hdata⟩ := exists_uniform_sourceAuxiliaryCountingData hp1 hp φ
  obtain ⟨L,W,hL,hWo,hWc,_,hφW,h0W,ha⟩ := sourceEquation1_4 hp (F φ)
  let U : Set (CoeffPair p) := V ∩ (F ⁻¹' W)
  have hUconv : Convex ℝ U := hVc.inter (hWc.linear_preimage (F.restrictScalars ℝ).toLinearMap)
  have hU0 : (0 : CoeffPair p) ∈ U := by simpa [U] using And.intro h0V h0W
  have hF (ψ : CoeffPair p) : F ψ = sourceAuxiliaryReflectedPotential hp1 hp ψ :=
    sourceAuxiliaryReflectedPotentialCLM_apply hp1 hp ψ
  refine ⟨max K L,U,hK.trans_le (le_max_left _ _),hVo.inter (hWo.preimage F.continuous),hUconv,
    ⟨⟨0,hU0⟩,hUconv.isPreconnected⟩,⟨hφV,hφW⟩,hU0,?_⟩
  intro N hN
  have hKN : K ≤ N := (le_max_left _ _).trans hN
  have hLN : L ≤ N := (le_max_right _ _).trans hN
  have hd (ψ : CoeffPair p) (hψ : ψ ∈ U) :
      SourceAuxiliaryContourData hp (sourceAuxiliaryReflectedPotential hp1 hp ψ)
        (sourceAuxiliaryReflectedPotential_mem hp1 hp ψ) N := by
    refine ⟨hdata ψ hψ.1 N hKN,?_,?_⟩
    · simpa only [hF] using ((ha N hLN).1.2 (F ψ) hψ.2).1
    · intro n hn
      simpa only [hF] using ((ha N hLN).2 n hn).2 (F ψ) hψ.2 |>.1
  refine ⟨?_,?_,hd⟩
  · intro b ψ hψ
    have han := ((ha N hLN).1.1 (F ψ) hψ.2).comp (F.analyticAt ψ)
    have han' : AnalyticAt ℂ (fun a => sourceCentralRectangleIntegral hp (sourceAuxiliaryReflectedPotential hp1 hp a) N) ψ := by
      simpa only [Function.comp_def,hF] using han
    exact (analyticAt_sourceAuxiliaryCompression b _).comp
      (f := fun a => sourceCentralRectangleIntegral hp (sourceAuxiliaryReflectedPotential hp1 hp a) N) han'
  · intro n hn b ψ hψ
    exact analyticAt_sourceAuxiliaryCircleProjection b hp1 hp ψ _ _ (by positivity) ((hd ψ hψ).disk_resolvent n hn)

end NLS.ZakharovShabat
