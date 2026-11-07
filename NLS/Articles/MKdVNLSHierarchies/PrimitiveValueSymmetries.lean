import NLS.Articles.MKdVNLSHierarchies.InvariantSpectralDomain
import NLS.ZakharovShabat.SourceAbelianPrimitiveFilledSymmetries
import NLS.ZakharovShabat.SourcePrimitiveCollapsedDomain

/-! # Corollary 8 for the same actual full primitive on an invariant neighborhood

Value identities include all collapsed cuts. The source-gradient identities
use the open joint cut complement, where the actual Frechet derivative has
been proved. A checked zero-source obstruction prevents treating the larger
filled fixed-source spectral domain as an open source domain.
-/
noncomputable section
open Set Complex MeasureTheory Filter Topology NLS.ZakharovShabat
namespace NLS.Articles.MKdVNLSHierarchies

theorem exists_corollary8_corrected :
    ∃ A V : Set (CoeffPair 2), IsOpen V ∧ IsConnected V ∧ realTypeSourceLocus 2 ⊆ V ∧
      MapsTo sourceComponentSwap V V ∧ MapsTo sourceMidpointReflection V V ∧
      (∀ α : ℝ, MapsTo (sourcePhaseRotation α) V V) ∧
      (∀ φ ∈ V, ∀ z ∈ sourceCanonicalRootDomain (by simp) (by norm_num) φ,
        ∀ j : ℤ, ∀ h : CoeffPair 2,
          (fderiv ℂ (fun χ => sourceFullAbelianPrimitive (by simp) (by norm_num) A j (z,χ)) φ) h =
            ∫ x in (0:ℝ)..1,
              (sourceFullAbelianPhysicalGradient φ z x).1*(sourcePhysicalL2 h).ofLp.1 x+
              (sourceFullAbelianPhysicalGradient φ z x).2*(sourcePhysicalL2 h).ofLp.2 x) ∧
      (∀ φ ∈ V, ∀ α : ℝ, ∀ z ∈ sourceOpenGapComplement (by simp) (by norm_num) φ,
        sourceFullAbelianPrimitive (by simp) (by norm_num) A 0 (z,φ) =
            -sourceFullAbelianPrimitive (by simp) (by norm_num) A 0 (-z,sourceComponentSwap φ) ∧
        sourceFullAbelianPrimitive (by simp) (by norm_num) A 0 (z,φ) =
            -sourceFullAbelianPrimitive (by simp) (by norm_num) A 0 (-z,sourceMidpointReflection φ) ∧
        sourceFullAbelianPrimitive (by simp) (by norm_num) A 0 (z,φ) =
            sourceFullAbelianPrimitive (by simp) (by norm_num) A 0 (z,sourcePhaseRotation α φ)) ∧
      (∀ φ ∈ V, ∀ α : ℝ, ∀ z ∈ sourceCanonicalRootDomain (by simp) (by norm_num) φ,
        -z ∈ sourceCanonicalRootDomain (by simp) (by norm_num) (sourceComponentSwap φ) ∧
        -z ∈ sourceCanonicalRootDomain (by simp) (by norm_num) (sourceMidpointReflection φ) ∧
        z ∈ sourceCanonicalRootDomain (by simp) (by norm_num) (sourcePhaseRotation α φ) ∧
        ∀ x : ℝ,
          sourceFullAbelianPhysicalGradient (sourceComponentSwap φ) (-z) x =
              (-(sourceFullAbelianPhysicalGradient φ z x).2,-(sourceFullAbelianPhysicalGradient φ z x).1) ∧
          sourceFullAbelianPhysicalGradient (sourceMidpointReflection φ) (-z) x =
              -sourceFullAbelianPhysicalGradient φ z (1-x) ∧
          sourceFullAbelianPhysicalGradient (sourcePhaseRotation α φ) z x =
              ((exp ((α:ℂ)*I))⁻¹*(sourceFullAbelianPhysicalGradient φ z x).1,
               exp ((α:ℂ)*I)*(sourceFullAbelianPhysicalGradient φ z x).2)) := by
  obtain ⟨A,V,hV,hconn,hreal,hP,hT,hR,_,_,D⟩ := theorem6_invariant_root_primitive_neighborhood
  refine ⟨A,V,hV,hconn,hreal,hP,hT,hR,?_,?_,?_⟩
  · intro φ hφ z hz j h
    exact sourceFullAbelianPrimitive_fderiv_eq_physical_integral D j φ h hφ z hz
  · intro φ hφ α z hz
    refine ⟨?_,?_,?_⟩
    · rw [D.primitive_componentSwap_filled hconn hP φ hφ z hz,neg_neg]
    · rw [D.primitive_midpointReflection_filled hconn hT φ hφ z hz,neg_neg]
    · exact (D.primitive_circleRotation_filled hconn (Circle.exp α) (hR α) φ hφ z hz).symm
  · intro φ _ α z hz
    refine ⟨(sourceCanonicalRootDomain_componentSwap (by simp) (by norm_num) φ z).mpr hz,
      (sourceCanonicalRootDomain_midpointReflection (by simp) (by norm_num) φ z).mpr hz,?_,
      fun x => corollary8_physical_gradient_symmetries φ α z x⟩
    change z ∈ sourceCanonicalRootDomain (by simp) (by norm_num) (sourceReciprocalScaling (exp ((α:ℂ)*I)) φ)
    rwa [sourceCanonicalRootDomain_reciprocalScaling _ _ _ (exp_ne_zero _)]

/-- Filling the free collapsed spectral point does not give an open source
slice there. A source-gradient clause needs an actual joint-domain qualification. -/
theorem corollary8_collapsed_source_domain_obstruction :
    (0:ℂ) ∈ sourceOpenGapComplement (by simp) (by norm_num) (0 : CoeffPair 2) ∧
      {φ : CoeffPair 2 | (0:ℂ) ∈ sourceOpenGapComplement (by simp) (by norm_num) φ} ∉ 𝓝 (0 : CoeffPair 2) :=
  ⟨source_filled_primitive_zero_slice_contains_zero (p := 2) (by simp) (by norm_num),
   source_filled_primitive_zero_slice_not_nhds (p := 2) (by simp) (by norm_num)⟩

end NLS.Articles.MKdVNLSHierarchies
