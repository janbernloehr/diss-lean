import NLS.ZakharovShabat.SourceWeightedPrimitiveCircleGradient
import NLS.ZakharovShabat.SourceIndexedHigherActionAnalytic

/-! # Actual higher-action derivatives on the full complex source domain

The real-type restriction in the earlier circle-gradient theorem is removed
using the established joint differential of the actual full primitive.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace SourceSection11ContourData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {V W U : Set (CoeffPair p)}

theorem exists_complex_gradient_circle (H : SourceSection11ContourData hp hp1 V)
    (hV : IsOpen V) (D : SourceFullAbelianDifferentialData hp hp1 W U)
    (φ : CoeffPair p) (hφV : φ ∈ V) (hφU : φ ∈ U) (n : ℤ) :
    ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧ sphere c R ⊆ sourceCanonicalRootDomain hp hp1 φ ∧
      ∀ k : ℕ, AnalyticAt ℂ (sourceIndexedHigherAction hp hp1 n k) φ ∧
        ∀ v : CoeffPair p, (fderiv ℂ (sourceIndexedHigherAction hp hp1 n k) φ) v =
          -(Real.pi:ℂ)⁻¹ * ∮ z in C(c,R),
            z^k*((sourceCanonicalRoot hp hp1 φ z)⁻¹*sourceDiscriminantCotangent hp z φ v) := by
  obtain ⟨B,hB,_,hφB,_,E,c,hE,C,_⟩ := H.neighborhoods φ hφV
  have hR : 0 < C.radius n := (C.inner_pos n).trans (C.inner_lt n)
  have hc := (C.periodCircle hE φ hφB n).sphere_subset_rootDomain
  refine ⟨C.center n,C.radius n,hR,hc,?_⟩
  intro k
  refine ⟨H.analytic_indexedHigherAction hV n k φ hφV,?_⟩
  intro v
  have he : sourceIndexedHigherAction hp hp1 n k =ᶠ[𝓝 φ]
      (fun ψ => sourceWeightedPrimitiveCircle hp hp1 W 0 ψ (C.center n:ℂ) (C.radius n) (fun z => z^k)) := by
    filter_upwards [(hB.inter D.source_open).mem_nhds ⟨hφB,hφU⟩] with ψ hψ
    obtain ⟨chart⟩ := D.charts ψ hψ.2
    exact sourceIndexedHigherAction_eq_primitive (C.periodCircle hE ψ hψ.1 n) chart k 0
  rw [he.fderiv_eq]
  exact D.fderiv_weightedPrimitiveCircle 0 φ hφU _ _ hR.le hc (fun z => z^k)
    univ isOpen_univ (fun _ _ => analyticAt_id.pow k) (fun _ _ => mem_univ _) v

end SourceSection11ContourData

/-- One common open neighborhood of the entire original real locus supports
all actual indexed higher-action derivatives in every complex direction. -/
theorem exists_sourceIndexedHigherAction_complex_gradients (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ realTypeSourceLocus p ⊆ V ∧
      ∀ φ ∈ V, ∀ n : ℤ, ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧
        sphere c R ⊆ sourceCanonicalRootDomain hp hp1 φ ∧
        ∀ k : ℕ, AnalyticAt ℂ (sourceIndexedHigherAction hp hp1 n k) φ ∧
          ∀ v : CoeffPair p, (fderiv ℂ (sourceIndexedHigherAction hp hp1 n k) φ) v =
            -(Real.pi:ℂ)⁻¹ * ∮ z in C(c,R),
              z^k*((sourceCanonicalRoot hp hp1 φ z)⁻¹*sourceDiscriminantCotangent hp z φ v) := by
  obtain ⟨V,hV,_,hreal,H⟩ := sourceSection11Contours hp hp1
  obtain ⟨W,U,_,D⟩ := exists_sourceFullAbelianDifferentialData hp hp1
  exact ⟨V ∩ U,hV.inter D.source_open,fun φ hφ => ⟨hreal hφ,D.real_subset hφ⟩,
    fun φ hφ n => H.exists_complex_gradient_circle hV D φ hφ.1 hφ.2 n⟩

end NLS.ZakharovShabat
