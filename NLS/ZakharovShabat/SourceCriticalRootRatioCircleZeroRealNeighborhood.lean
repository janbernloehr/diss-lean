import NLS.ZakharovShabat.SourceCriticalRootRatioCircleSourceDifferentiable
import NLS.ZakharovShabat.SourceCriticalRootRatioEnclosingCircleVanishing

/-!
# A holomorphic contour integral vanishing on the real-type locus

Near an open real-type source gap, one fixed enclosing circle works for
all nearby complex source potentials. Its integral is holomorphic in
the source and vanishes at every nearby real-type source.
-/

noncomputable section
open Set Metric Filter Complex
open scoped ENNReal Topology
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Near an open real-type gap, the fixed enclosing-circle integral
is holomorphic in the source and zero throughout the real-type part
of the neighborhood. -/
theorem exists_local_sourceCriticalRootRatio_circleIntegral_zero_on_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential φ)
      (periodOnePotential_mem φ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ)
        (periodOnePotential_mem φ) n).re) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧
        (∀ ψ ∈ V,
          sourcePeriodicSegment hp hp1 ψ n ⊆ ball c R ∧
          closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n) ∧
        DifferentiableOn ℂ
          (fun ψ : CoeffPair p =>
            ∮ z in C(c,R), sourceCriticalRootRatioJoint hp hp1 (z,ψ)) V ∧
        (∀ ψ ∈ V, IsRealType (CoeffPair.toMax p ψ) →
          (∮ z in C(c,R), sourceCriticalRootRatioJoint hp hp1 (z,ψ)) = 0) := by
  obtain ⟨V₀,hV₀open,hφV₀,c,R,hR,hgeom,hdiff⟩ :=
    exists_local_sourceCriticalRootRatio_circleIntegral_differentiableOn
      hp hp1 φ hφ n
  let gap : CoeffPair p → ℝ := fun ψ =>
    (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re -
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re
  have hL : ContinuousAt
      (fun ψ : CoeffPair p =>
        (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) n).re) φ :=
    continuous_re.continuousAt.comp
      (continuousAt_canonicalPeriodicLeft_periodOne_of_realType
        hp hp1 φ hφ n)
  have hRt : ContinuousAt
      (fun ψ : CoeffPair p =>
        (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) n).re) φ :=
    continuous_re.continuousAt.comp
      (continuousAt_canonicalPeriodicRight_periodOne_of_realType
        hp hp1 φ hφ n)
  have hgap : ContinuousAt gap φ := hRt.sub hL
  have hgapPos : 0 < gap φ := sub_pos.mpr hopen
  have hnear : ∀ᶠ ψ in 𝓝 φ, 0 < gap ψ :=
    hgap.eventually (isOpen_Ioi.mem_nhds hgapPos)
  obtain ⟨U,hUsub,hUopen,hφU⟩ := _root_.mem_nhds_iff.mp hnear
  let V := V₀ ∩ U
  have hVopen : IsOpen V := hV₀open.inter hUopen
  have hφV : φ ∈ V := ⟨hφV₀,hφU⟩
  refine ⟨V,hVopen,hφV,c,R,hR,?_,?_,?_⟩
  · intro ψ hψ
    exact hgeom ψ hψ.1
  · exact hdiff.mono inter_subset_left
  · intro ψ hψ hreal
    have hopenψ :
        (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) n).re <
        (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) n).re :=
      sub_pos.mp (hUsub hψ.2)
    obtain ⟨hseg,hother⟩ := hgeom ψ hψ.1
    change (∮ z in C(c,R),
      deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
        sourceCanonicalRoot hp hp1 ψ z) = 0
    exact sourceCriticalRootRatio_enclosingCircleIntegral_eq_zero_of_realType
      hp hp1 ψ hreal n hopenψ c R hR hseg hother

end NLS.ZakharovShabat
