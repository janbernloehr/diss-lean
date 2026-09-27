import NLS.ZakharovShabat.SourceCriticalRootRatioCircleAllGaps
import NLS.ZakharovShabat.SourceCriticalRootRatioJointAnalytic
import NLS.ComplexAnalysis.ParametricCircleIntegral

/-!
# Vanishing on a prescribed isolating circle

The fixed-circle vanishing theorem is strengthened to a circle supplied
by another construction, in particular an indexed action ball chart.
For each real-type source on the neighborhood, the open-gap boundary
calculation or collapsed-gap removability gives zero. Joint source
analyticity and the real-form identity principle extend this equality
to nearby complex sources.
-/

noncomputable section
open Set Metric Filter Complex Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The unweighted critical-root quotient has zero integral on any
fixed isolating circle that stays valid on an open source neighborhood,
after shrinking that neighborhood around a real-type source. -/
theorem exists_local_sourceCriticalRootRatio_circleIntegral_zero_on_givenCircle
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) (V₀ : Set (CoeffPair p))
    (hV₀open : IsOpen V₀) (hφV₀ : φ ∈ V₀)
    (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hgeom : ∀ ψ ∈ V₀,
      sourcePeriodicSegment hp hp1 ψ n ⊆ ball c R ∧
      closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧ V ⊆ V₀ ∧
      ∀ ψ ∈ V,
        (∮ z in C(c,R), sourceCriticalRootRatioJoint hp hp1 (z,ψ)) = 0 := by
  obtain ⟨W,_,_,hrealW,hDopen,hquot⟩ :=
    exists_global_sourceCriticalRootRatio_jointAnalytic hp hp1
  let F := sourceCriticalRootRatioJoint hp hp1
  let D := sourceCanonicalRootJointDomain hp hp1 W
  have hcircle (z : ℂ) (hz : z ∈ sphere c R) : (z,φ) ∈ D := by
    have hgeometry := hgeom φ hφV₀
    exact ⟨hrealW hφ,
      sourceCanonicalRootDomain_of_enclosingCircle hp hp1 φ n c R
        hgeometry.1 hgeometry.2 hz⟩
  obtain ⟨V₁,hV₁open,hφV₁,M,_,hbound⟩ :=
    NLS.ComplexAnalysis.exists_uniform_joint_fderiv_bound_on_circle
      F D hDopen hquot c R φ hcircle
  obtain ⟨W₂,hW₂open,hreal₂,hcollapsed⟩ :=
    exists_global_sourceCriticalRootRatio_circleIntegral_zero_of_zeroGap hp hp1
  let V₂ := (V₀ ∩ V₁) ∩ W₂
  have hV₂open : IsOpen V₂ := (hV₀open.inter hV₁open).inter hW₂open
  have hφV₂ : φ ∈ V₂ := ⟨⟨hφV₀,hφV₁⟩,hreal₂ hφ⟩
  let G : CoeffPair p → ℂ := fun ψ =>
    ∮ z in C(c,R), F (z,ψ)
  have hdiff : DifferentiableOn ℂ G V₂ := by
    intro ψ hψ
    have hd := NLS.ComplexAnalysis.differentiableAt_circleIntegral_of_jointAnalytic
      F D hDopen hquot c R hR.le V₂ hV₂open ψ hψ M
      (fun b hb θ => (hbound (circleMap c R θ)
        (circleMap_mem_sphere c hR.le θ) b hb.1.2).1)
      (fun b hb θ => (hbound (circleMap c R θ)
        (circleMap_mem_sphere c hR.le θ) b hb.1.2).2)
    exact hd.differentiableWithinAt
  have hrealzero : ∀ ψ ∈ V₂,
      IsRealType (CoeffPair.toMax p ψ) → G ψ = 0 := by
    intro ψ hψ hψreal
    obtain ⟨hseg,hother⟩ := hgeom ψ hψ.1.1
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
  have hlocal : ∀ᶠ ψ in 𝓝 φ, G ψ = 0 :=
    NLS.ComplexAnalysis.DifferentiableOn.eventually_eq_zero_of_real_form
      (realTypeSourceLocus p) φ hφ
      (by
        intro x y hx hy
        change IsRealType (CoeffPair.toMax p (x+y))
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
      V₂ hV₂open hφV₂ G hdiff hrealzero
  obtain ⟨U,hUsub,hUopen,hφU⟩ := _root_.mem_nhds_iff.mp hlocal
  refine ⟨V₂ ∩ U,hV₂open.inter hUopen,⟨hφV₂,hφU⟩,?_,?_⟩
  · intro ψ hψ
    exact hψ.1.1.1
  · intro ψ hψ
    exact hUsub hψ.2

end NLS.ZakharovShabat
