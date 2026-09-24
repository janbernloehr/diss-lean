import NLS.ZakharovShabat.SourceCriticalRootRatioCircleComplexNeighborhoodZero
import NLS.ZakharovShabat.SourceCriticalRootRatioCollapsedContour

/-!
# Local fixed-circle vanishing at open and collapsed gaps

For a real-type source, the chosen periodic gap is either open or
collapsed. The open-gap contour calculation and the analytic
removability at a collapsed gap give the same zero integral. Uniqueness
from the real-type source locus then extends it to nearby complex
sources, without an open-gap hypothesis at the base point.
-/

noncomputable section
open Set Metric Filter Complex
open NLS.ComplexAnalysis
open scoped ENNReal Topology
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Around any real-type source, whether the selected gap is open or
collapsed, one fixed gap-enclosing circle has zero critical-root
quotient integral for every source in a complex neighborhood. -/
theorem exists_local_sourceCriticalRootRatio_circleIntegral_zero_allGaps
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧
        (∀ ψ ∈ V,
          sourcePeriodicSegment hp hp1 ψ n ⊆ ball c R ∧
          closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n) ∧
        (∀ ψ ∈ V,
          (∮ z in C(c,R), sourceCriticalRootRatioJoint hp hp1 (z,ψ)) = 0) := by
  obtain ⟨V₀,hV₀open,hφV₀,c,R,hR,hgeom,hdiff⟩ :=
    exists_local_sourceCriticalRootRatio_circleIntegral_differentiableOn
      hp hp1 φ hφ n
  obtain ⟨W,hWopen,hrealW,hcollapsed⟩ :=
    exists_global_sourceCriticalRootRatio_circleIntegral_zero_of_zeroGap hp hp1
  let V₁ := V₀ ∩ W
  have hV₁open : IsOpen V₁ := hV₀open.inter hWopen
  have hφV₁ : φ ∈ V₁ := ⟨hφV₀,hrealW hφ⟩
  let F : CoeffPair p → ℂ := fun ψ =>
    ∮ z in C(c,R), sourceCriticalRootRatioJoint hp hp1 (z,ψ)
  have hrealzero : ∀ ψ ∈ V₁, IsRealType (CoeffPair.toMax p ψ) → F ψ = 0 := by
    intro ψ hψ hψreal
    obtain ⟨hseg,hother⟩ := hgeom ψ hψ.1
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    by_cases hopen : l.re < r.re
    · change (∮ z in C(c,R),
        deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
          sourceCanonicalRoot hp hp1 ψ z) = 0
      exact sourceCriticalRootRatio_enclosingCircleIntegral_eq_zero_of_realType
        hp hp1 ψ hψreal n hopen c R hR hseg hother
    · have hle : l.re ≤ r.re :=
        re_le_of_complexLexLE
          ((canonicalPeriodicEndpoints_spec hp hp1 (periodOnePotential ψ)
            (periodOnePotential_mem ψ)).2.1 n)
      have hre : l.re = r.re := le_antisymm hle (le_of_not_gt hopen)
      obtain ⟨hlim,hrim⟩ :=
        canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1
          (periodOnePotential ψ) (periodOnePotential_mem ψ)
          (isRealType_periodOnePotential ψ hψreal) n
      have he : l = r := Complex.ext hre (hlim.trans hrim.symm)
      have hgap : sourcePeriodicGapDisplacement hp hp1 ψ n = 0 := by
        rw [sourcePeriodicGapDisplacement_apply]
        change r - l = 0
        exact sub_eq_zero.mpr he.symm
      have hboundary : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ :=
        sourceCanonicalRootDomain_of_enclosingCircle hp hp1 ψ n c R hseg hother
      change (∮ z in C(c,R),
        deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
          sourceCanonicalRoot hp hp1 ψ z) = 0
      exact hcollapsed ψ hψ.2 n hgap c R hR.le hother hboundary
  have hlocal : ∀ᶠ ψ in 𝓝 φ, F ψ = 0 :=
    NLS.ComplexAnalysis.DifferentiableOn.eventually_eq_zero_of_real_form
      (realTypeSourceLocus p) φ hφ
      (by
        intro x y hx hy
        change IsRealType (CoeffPair.toMax p (x + y))
        rw [map_add]
        exact hx.add hy)
      (by
        intro t x hx
        change IsRealType (CoeffPair.toMax p ((t:ℂ) • x))
        rw [map_smul]
        exact hx.ofReal_smul t)
      sourceRealPart sourceImagPart
      sourceRealPart_realType sourceImagPart_realType
      (fun v => (sourceRealPart_add_I_smul_sourceImagPart v).symm)
      (norm_sourceRealPart_le hp) (norm_sourceImagPart_le hp)
      V₁ hV₁open hφV₁ F (hdiff.mono inter_subset_left) hrealzero
  obtain ⟨U,hUsub,hUopen,hφU⟩ := _root_.mem_nhds_iff.mp hlocal
  refine ⟨V₁ ∩ U,hV₁open.inter hUopen,⟨hφV₁,hφU⟩,c,R,hR,?_,?_⟩
  · intro ψ hψ
    exact hgeom ψ hψ.1.1
  · intro ψ hψ
    exact hUsub hψ.2

end NLS.ZakharovShabat
