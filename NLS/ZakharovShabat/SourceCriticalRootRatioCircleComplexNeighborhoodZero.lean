import NLS.ZakharovShabat.SourceCriticalRootRatioCircleZeroRealNeighborhood
import NLS.ZakharovShabat.SourceRealTypeDecomposition
import NLS.ComplexAnalysis.RealFormIdentity

/-!
# Vanishing of the fixed gap-circle integral for complex sources

The fixed contour integral near an open real-type gap is holomorphic in
the full complex source space and zero on its real-type locus. The
norm-controlled real-type decomposition and the real-form identity
principle make it zero throughout a complex neighborhood.
-/

noncomputable section
open Set Filter Complex
open scoped ENNReal Topology
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A single gap-enclosing circle works for every nearby complex source,
and its critical-root quotient integral vanishes throughout that
complex source neighborhood. -/
theorem exists_local_sourceCriticalRootRatio_circleIntegral_zero
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
          sourcePeriodicSegment hp hp1 ψ n ⊆ Metric.ball c R ∧
          Metric.closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n) ∧
        (∀ ψ ∈ V,
          (∮ z in C(c,R), sourceCriticalRootRatioJoint hp hp1 (z,ψ)) = 0) := by
  obtain ⟨V₀,hV₀open,hφV₀,c,R,hR,hgeom,hdiff,hrealzero⟩ :=
    exists_local_sourceCriticalRootRatio_circleIntegral_zero_on_realType
      hp hp1 φ hφ n hopen
  let F : CoeffPair p → ℂ := fun ψ =>
    ∮ z in C(c,R), sourceCriticalRootRatioJoint hp hp1 (z,ψ)
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
      V₀ hV₀open hφV₀ F hdiff hrealzero
  obtain ⟨U,hUsub,hUopen,hφU⟩ := _root_.mem_nhds_iff.mp hlocal
  refine ⟨V₀ ∩ U,hV₀open.inter hUopen,⟨hφV₀,hφU⟩,c,R,hR,?_,?_⟩
  · intro ψ hψ
    exact hgeom ψ hψ.1
  · intro ψ hψ
    exact hUsub hψ.2

end NLS.ZakharovShabat
