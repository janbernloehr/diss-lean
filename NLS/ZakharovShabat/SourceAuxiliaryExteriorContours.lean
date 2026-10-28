import NLS.ZakharovShabat.SourceAuxiliaryContourCounting
import NLS.ZakharovShabat.SourceCorollary3_5

/-! # A common neighborhood for the entire auxiliary contour argument

The exterior resolvent and both auxiliary contour families share one open
convex connected neighborhood of the original interval input and zero, valid
at every larger cutoff. This makes the quantifiers in the proof of
Proposition 5.2 explicit. The boxes have height N; the unrestricted printed
norm-dependent height remains refuted.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Actual auxiliary counts and contours, together with the full ambient exterior resolvent. -/
structure SourceAuxiliaryExteriorContourData (hp : p ≠ ⊤) (φ : CoeffPair p)
    (hφ : φ ∈ sourceBoundaryBaseSubspace .neumann) (N : ℕ) : Prop
    extends SourceAuxiliaryContourData hp φ hφ N where
  exterior_resolvent : spectralExterior N (Real.pi/4) ⊆ sourceResolventSet hp φ

namespace SourceAuxiliaryExteriorContourData
variable {hp : p ≠ ⊤} {φ : CoeffPair p}
    {hφ : φ ∈ sourceBoundaryBaseSubspace .neumann} {N : ℕ}

/-- Analyticity in the spectral parameter throughout the full box-and-disk exterior. -/
theorem analytic_exterior (h : SourceAuxiliaryExteriorContourData hp φ hφ N) :
    AnalyticOnNhd ℂ (sourceResolvent hp φ) (spectralExterior N (Real.pi/4)) :=
  (analyticOnNhd_sourceResolvent hp φ).mono h.exterior_resolvent

/-- The same exterior excludes the full ambient spectrum, not just the restricted spectra. -/
theorem ambient_spectrum_subset (h : SourceAuxiliaryExteriorContourData hp φ hφ N) :
    (sourceResolventSet hp φ)ᶜ ⊆ centralSpectralBox N ∪ highSpectralDisks N (Real.pi/4) := by
  intro z hz
  by_contra hout
  exact hz (h.exterior_resolvent hout)

end SourceAuxiliaryExteriorContourData

/-- One original-input neighborhood supports spectral-parameter analyticity,
both analytic auxiliary projection families and all counted ranks, simultaneously
for every larger cutoff. -/
theorem exists_uniform_sourceAuxiliaryExteriorContourData (hp1 : 1 < p) (hp : p ≠ ⊤)
    (φ : CoeffPair p) :
    ∃ N₀ : ℕ, ∃ U : Set (CoeffPair p),
      0 < N₀ ∧ IsOpen U ∧ Convex ℝ U ∧ IsConnected U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ N : ℕ, N₀ ≤ N →
        (∀ b : BoundaryCondition, AnalyticOnNhd ℂ
          (fun ψ => sourceAuxiliaryCentralProjection b hp (sourceAuxiliaryReflectedPotential hp1 hp ψ) N) U) ∧
        (∀ n : ℤ, N < n.natAbs → ∀ b : BoundaryCondition, AnalyticOnNhd ℂ
          (fun ψ => sourceAuxiliaryCircleProjection b hp (sourceAuxiliaryReflectedPotential hp1 hp ψ)
            ((Real.pi : ℂ)*n) (Real.pi/4)) U) ∧
        ∀ ψ ∈ U, SourceAuxiliaryExteriorContourData hp (sourceAuxiliaryReflectedPotential hp1 hp ψ)
          (sourceAuxiliaryReflectedPotential_mem hp1 hp ψ) N := by
  let F := sourceAuxiliaryReflectedPotentialCLM hp1 hp
  obtain ⟨K,V,hK,hVo,hVc,_,hφV,h0V,hdata⟩ := exists_uniform_sourceAuxiliaryContourData hp1 hp φ
  obtain ⟨L,W,_,hWo,hWc,_,hφW,h0W,hext⟩ := sourceCorollary3_5_all_larger hp (F φ)
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
  refine ⟨?_,?_,?_⟩
  · intro b
    exact ((hdata N hKN).1 b).mono Set.inter_subset_left
  · intro n hn b
    exact ((hdata N hKN).2.1 n hn b).mono Set.inter_subset_left
  · intro ψ hψ
    refine ⟨(hdata N hKN).2.2 ψ hψ.1,?_⟩
    simpa only [hF] using (hext N hLN (F ψ) hψ.2).1

end NLS.ZakharovShabat
