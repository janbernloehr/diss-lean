import NLS.ZakharovShabat.SourceInvariantNeighborhood
import NLS.ZakharovShabat.SourceHigherActionCotangentSymmetries
import NLS.ZakharovShabat.L2WeightedActionGradient
import NLS.ZakharovShabat.L2PhysicalCotangentSymmetries

/-! # Full Lemma 10(i) on the original complex Hilbert source domain

The natural level r denotes the printed level r+1. Both components are
actual continuous physical representatives of the original unconjugated
Frechet derivative, tested in every original Hilbert direction.
-/
noncomputable section
open Set Complex NLS.LinearVolterra NLS.ZakharovShabat
namespace NLS.Articles.MKdVNLSHierarchies

theorem lemma10_i : ∃ U : Set (CoeffPair 2), IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus 2 ⊆ U ∧
    MapsTo sourceComponentSwap U U ∧ MapsTo sourceMidpointReflection U U ∧
    (∀ α : ℝ, MapsTo (sourceCircleRotation (Circle.exp α)) U U) ∧
    ∀ φ ∈ U, ∀ n : ℤ, ∀ r : ℕ,
      SourcePhysicalGradientRepresents
        (fderiv ℂ (sourceIndexedHigherAction (by simp) (by norm_num) n r) φ)
        (sourceHigherActionPhysicalGradientCurve φ n r) ∧
      sourceHigherActionPhysicalGradientCurve φ n r ⟨1,by norm_num⟩ =
        sourceHigherActionPhysicalGradientCurve φ n r ⟨0,by norm_num⟩ ∧
      ∀ x : Icc (0:ℝ) 1,
        sourceHigherActionPhysicalGradientCurve φ n r x = (-1:ℂ)^r •
          ((sourceHigherActionPhysicalGradientCurve (sourceComponentSwap φ) (-n) r x).2,
           (sourceHigherActionPhysicalGradientCurve (sourceComponentSwap φ) (-n) r x).1) ∧
        sourceHigherActionPhysicalGradientCurve φ n r x = (-1:ℂ)^r •
          sourceHigherActionPhysicalGradientCurve (sourceMidpointReflection φ) (-n) r
            ⟨1-x.val,by constructor <;> linarith [x.property.1,x.property.2]⟩ ∧
        ∀ α : ℝ, sourceHigherActionPhysicalGradientCurve φ n r x =
          (Circle.exp α*(sourceHigherActionPhysicalGradientCurve (sourceCircleRotation (Circle.exp α) φ) n r x).1,
           (Circle.exp α:ℂ)⁻¹*(sourceHigherActionPhysicalGradientCurve (sourceCircleRotation (Circle.exp α) φ) n r x).2) := by
  obtain ⟨V,hV,hrV,Hg⟩ := exists_sourceHigherActionPhysicalGradients
  obtain ⟨A,hA,hrA,_,_,_,Hc⟩ := exists_sourceIndexedHigherAction_cotangent_symmetries
    (p := 2) (by simp) (by norm_num)
  have hrVA : realTypeSourceLocus 2 ⊆ V ∩ A := fun φ hφ => ⟨hrV hφ,hrA hφ⟩
  let U := sourceConnectedSymmetryCore (V ∩ A)
  have hUV : U ⊆ V ∩ A := sourceConnectedSymmetryCore_subset _
  have hP : MapsTo sourceComponentSwap U U := sourceConnectedSymmetryCore_componentSwap _ hrVA
  have hT : MapsTo sourceMidpointReflection U U := sourceConnectedSymmetryCore_midpointReflection _ hrVA
  have hR : ∀ c : Circle, MapsTo (sourceCircleRotation c) U U := by
    intro c φ hφ
    exact sourceConnectedSymmetryCore_circleRotation _ hrVA c hφ
  have hrep (φ : CoeffPair 2) (hφ : φ ∈ U) (n : ℤ) (r : ℕ) :
      SourcePhysicalGradientRepresents
        (fderiv ℂ (sourceIndexedHigherAction (by simp) (by norm_num) n r) φ)
        (sourceHigherActionPhysicalGradientCurve φ n r) := by
    obtain ⟨c,R,_,_,H⟩ := Hg φ (hUV hφ).1 n
    exact (H r).1
  refine ⟨U,isOpen_sourceConnectedSymmetryCore _ (hV.inter hA),
    isConnected_sourceConnectedSymmetryCore _ hrVA,
    realTypeSourceLocus_subset_sourceConnectedSymmetryCore _ hrVA,
    hP,hT,fun α => hR (Circle.exp α),?_⟩
  intro φ hφ n r
  have hp : sourceHigherActionPhysicalGradientCurve φ n r ⟨1,by norm_num⟩ =
      sourceHigherActionPhysicalGradientCurve φ n r ⟨0,by norm_num⟩ := by
    obtain ⟨c,R,hR,hc,H⟩ := Hg φ (hUV hφ).1 n
    rw [(H r).2]
    exact sourceWeightedPhysicalGradientCurve_endpoints φ _ c R hR.le (by fun_prop) hc
  refine ⟨hrep φ hφ n r,hp,?_⟩
  intro x
  have hcP := (Hc (sourceComponentSwap φ) (hUV (hP hφ)).2 (-n) r).1
  simp only [sourceComponentSwap_involutive,neg_neg] at hcP
  have hcT := (Hc (sourceMidpointReflection φ) (hUV (hT hφ)).2 (-n) r).2.1
  simp only [sourceMidpointReflection_involutive,neg_neg] at hcT
  refine ⟨(hrep _ (hP hφ) (-n) r).componentSwap (hrep φ hφ n r) _ hcP x,
    (hrep _ (hT hφ) (-n) r).midpointReflection (hrep φ hφ n r) _ hcT x,?_⟩
  intro α
  exact (hrep φ hφ n r).reciprocalScaling
    (hrep _ (hR (Circle.exp α) hφ) n r) _ ((Hc φ (hUV hφ).2 n r).2.2 (Circle.exp α)) x

end NLS.Articles.MKdVNLSHierarchies
