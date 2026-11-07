import NLS.ZakharovShabat.SourceHigherActionCircleSymmetries
import NLS.ZakharovShabat.SourceIndexedHigherActionAnalytic
import NLS.ZakharovShabat.SourceSymmetryCore

/-! # Lemma 10(i) at the actual full source-cotangent level

Every index and every positive printed level is included. The source is
complex, and every complex direction is tested. Circle transport proves
the value identities before the chain rule is applied.
-/
noncomputable section
open Set Metric Filter Topology Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem cotangent_of_value_symmetry (f g : CoeffPair p → ℂ)
    (A : CoeffPair p →L[ℂ] CoeffPair p) (a : ℂ) (φ : CoeffPair p)
    (hf : DifferentiableAt ℂ f φ) (hg : DifferentiableAt ℂ g (A φ))
    (he : (fun ψ => g (A ψ)) =ᶠ[𝓝 φ] (fun ψ => a*f ψ)) :
    (fderiv ℂ g (A φ)).comp A = a • fderiv ℂ f φ := by
  have hl := hg.hasFDerivAt.comp φ A.hasFDerivAt
  have hr := hf.hasFDerivAt.const_mul a
  exact hl.unique (hr.congr_of_eventuallyEq he)

namespace SourceSection11ContourData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

theorem periodCircle_nonempty (H : SourceSection11ContourData hp hp1 W)
    (φ : CoeffPair p) (hφ : φ ∈ W) (n : ℤ) :
    Nonempty (SourceCriticalRootPeriodCircle hp hp1 φ n) := by
  obtain ⟨U,_,_,hφU,_,D,c,hD,C,_⟩ := H.neighborhoods φ hφ
  exact ⟨C.periodCircle hD φ hφU n⟩

theorem cotangent_componentSwap (H : SourceSection11ContourData hp hp1 W) (hW : IsOpen W)
    (φ : CoeffPair p) (hφ : φ ∈ W) (hP : sourceComponentSwap φ ∈ W) (n : ℤ) (k : ℕ) :
    (fderiv ℂ (sourceIndexedHigherAction hp hp1 (-n) k) (sourceComponentSwap φ)).comp
      sourceComponentSwap.toContinuousLinearEquiv.toContinuousLinearMap =
        (-1:ℂ)^k • fderiv ℂ (sourceIndexedHigherAction hp hp1 n k) φ := by
  refine cotangent_of_value_symmetry (sourceIndexedHigherAction hp hp1 n k)
    (sourceIndexedHigherAction hp hp1 (-n) k)
    sourceComponentSwap.toContinuousLinearEquiv.toContinuousLinearMap ((-1:ℂ)^k) φ
    (H.analytic_indexedHigherAction hW n k φ hφ).differentiableAt
    (H.analytic_indexedHigherAction hW (-n) k _ hP).differentiableAt ?_
  filter_upwards [hW.mem_nhds hφ] with ψ hψ
  obtain ⟨C⟩ := H.periodCircle_nonempty ψ hψ n
  exact sourceIndexedHigherAction_componentSwap hp hp1 ψ n C k

theorem cotangent_midpointReflection (H : SourceSection11ContourData hp hp1 W) (hW : IsOpen W)
    (φ : CoeffPair p) (hφ : φ ∈ W) (hT : sourceMidpointReflection φ ∈ W) (n : ℤ) (k : ℕ) :
    (fderiv ℂ (sourceIndexedHigherAction hp hp1 (-n) k) (sourceMidpointReflection φ)).comp
      sourceMidpointReflection.toContinuousLinearEquiv.toContinuousLinearMap =
        (-1:ℂ)^k • fderiv ℂ (sourceIndexedHigherAction hp hp1 n k) φ := by
  refine cotangent_of_value_symmetry (sourceIndexedHigherAction hp hp1 n k)
    (sourceIndexedHigherAction hp hp1 (-n) k)
    sourceMidpointReflection.toContinuousLinearEquiv.toContinuousLinearMap ((-1:ℂ)^k) φ
    (H.analytic_indexedHigherAction hW n k φ hφ).differentiableAt
    (H.analytic_indexedHigherAction hW (-n) k _ hT).differentiableAt ?_
  filter_upwards [hW.mem_nhds hφ] with ψ hψ
  obtain ⟨C⟩ := H.periodCircle_nonempty ψ hψ n
  exact sourceIndexedHigherAction_midpointReflection hp hp1 ψ n C k

theorem cotangent_circleRotation (H : SourceSection11ContourData hp hp1 W) (hW : IsOpen W)
    (c : Circle) (φ : CoeffPair p) (hφ : φ ∈ W) (hR : sourceCircleRotation c φ ∈ W)
    (n : ℤ) (k : ℕ) :
    (fderiv ℂ (sourceIndexedHigherAction hp hp1 n k) (sourceCircleRotation c φ)).comp
      (sourceReciprocalScaling (c:ℂ)) = fderiv ℂ (sourceIndexedHigherAction hp hp1 n k) φ := by
  have hc : (c:ℂ) ≠ 0 := by
    intro he
    have hn := Circle.norm_coe c
    rw [he,norm_zero] at hn
    norm_num at hn
  have h := cotangent_of_value_symmetry
    (sourceIndexedHigherAction hp hp1 n k) (sourceIndexedHigherAction hp hp1 n k)
    (sourceReciprocalScaling (c:ℂ)) 1 φ
    (H.analytic_indexedHigherAction hW n k φ hφ).differentiableAt
    (H.analytic_indexedHigherAction hW n k _ hR).differentiableAt (by
      filter_upwards [hW.mem_nhds hφ] with ψ hψ
      obtain ⟨C⟩ := H.periodCircle_nonempty ψ hψ n
      simpa only [one_mul] using sourceIndexedHigherAction_reciprocalScaling hp hp1 (c:ℂ) hc ψ n C k)
  simpa only [sourceCircleRotation,one_smul] using! h

end SourceSection11ContourData

/-- A single invariant open neighborhood of every real source supports all
three actual higher-action cotangent identities, with no real-type restriction. -/
theorem exists_sourceIndexedHigherAction_cotangent_symmetries (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ realTypeSourceLocus p ⊆ U ∧
      MapsTo sourceComponentSwap U U ∧ MapsTo sourceMidpointReflection U U ∧
      (∀ c : Circle, MapsTo (sourceCircleRotation c) U U) ∧
      ∀ φ ∈ U, ∀ n : ℤ, ∀ k : ℕ,
        (fderiv ℂ (sourceIndexedHigherAction hp hp1 (-n) k) (sourceComponentSwap φ)).comp
            sourceComponentSwap.toContinuousLinearEquiv.toContinuousLinearMap =
          (-1:ℂ)^k • fderiv ℂ (sourceIndexedHigherAction hp hp1 n k) φ ∧
        (fderiv ℂ (sourceIndexedHigherAction hp hp1 (-n) k) (sourceMidpointReflection φ)).comp
            sourceMidpointReflection.toContinuousLinearEquiv.toContinuousLinearMap =
          (-1:ℂ)^k • fderiv ℂ (sourceIndexedHigherAction hp hp1 n k) φ ∧
        ∀ c : Circle, (fderiv ℂ (sourceIndexedHigherAction hp hp1 n k) (sourceCircleRotation c φ)).comp
          (sourceReciprocalScaling (c:ℂ)) = fderiv ℂ (sourceIndexedHigherAction hp hp1 n k) φ := by
  obtain ⟨W,hW,_,hr,H⟩ := sourceSection11Contours hp hp1
  let U := sourceSymmetryCore W
  have hU := isOpen_sourceSymmetryCore W hW
  have hUW : U ⊆ W := sourceSymmetryCore_subset W
  have hP : MapsTo sourceComponentSwap U U := sourceSymmetryCore_componentSwap W
  have hT : MapsTo sourceMidpointReflection U U := sourceSymmetryCore_midpointReflection W
  have hR : ∀ c : Circle, MapsTo (sourceCircleRotation c) U U := by
    intro c φ hφ
    exact sourceSymmetryCore_circleRotation W φ hφ c
  refine ⟨U,hU,realTypeSourceLocus_subset_sourceSymmetryCore W hr,hP,hT,hR,?_⟩
  intro φ hφ n k
  exact ⟨H.cotangent_componentSwap hW φ (hUW hφ) (hUW (hP hφ)) n k,
    H.cotangent_midpointReflection hW φ (hUW hφ) (hUW (hT hφ)) n k,
    fun c => H.cotangent_circleRotation hW c φ (hUW hφ) (hUW (hR c hφ)) n k⟩

end NLS.ZakharovShabat
