import NLS.ZakharovShabat.SourceRealActionLocalAgreement
import NLS.ZakharovShabat.SourceRealTypeDecomposition
import NLS.ComplexAnalysis.RealFormIdentity

/-!
# Compatibility of local action extensions

The real-type source locus is a norm-controlled real form of the
complex coefficient-pair space. Its identity principle makes two
complex-differentiable extensions equal near any real-type point where
they agree on real-type sources. Consequently, locally chosen circle
actions representing the same indexed action define a unique germ.
-/

noncomputable section
open Set Filter Complex
open scoped ENNReal Topology
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Two complex-differentiable source functions that agree on the
real-type part of an overlap agree on a complex neighborhood of each
real-type point of that overlap. -/
theorem exists_local_eqOn_of_eqOn_realType
    (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (V₀ V₁ : Set (CoeffPair p))
    (hV₀open : IsOpen V₀) (hV₁open : IsOpen V₁)
    (hφV₀ : φ ∈ V₀) (hφV₁ : φ ∈ V₁)
    (F G : CoeffPair p → ℂ)
    (hFdiff : DifferentiableOn ℂ F V₀)
    (hGdiff : DifferentiableOn ℂ G V₁)
    (hreal : ∀ ψ ∈ V₀ ∩ V₁,
      IsRealType (CoeffPair.toMax p ψ) → F ψ = G ψ) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧
      U ⊆ V₀ ∩ V₁ ∧ EqOn F G U := by
  let V := V₀ ∩ V₁
  have hVopen : IsOpen V := hV₀open.inter hV₁open
  have hφV : φ ∈ V := ⟨hφV₀,hφV₁⟩
  let H : CoeffPair p → ℂ := fun ψ => F ψ - G ψ
  have hHdiff : DifferentiableOn ℂ H V :=
    (hFdiff.mono inter_subset_left).sub
      (hGdiff.mono inter_subset_right)
  have hHzero : ∀ ψ ∈ V,
      IsRealType (CoeffPair.toMax p ψ) → H ψ = 0 := by
    intro ψ hψ hψreal
    exact sub_eq_zero.mpr (hreal ψ hψ hψreal)
  have hlocal : ∀ᶠ ψ in 𝓝 φ, H ψ = 0 :=
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
      V hVopen hφV H hHdiff hHzero
  obtain ⟨U₀,hU₀sub,hU₀open,hφU₀⟩ := _root_.mem_nhds_iff.mp hlocal
  let U := V ∩ U₀
  refine ⟨U,hVopen.inter hU₀open,⟨hφV,hφU₀⟩,inter_subset_left,?_⟩
  intro ψ hψ
  exact sub_eq_zero.mp (hU₀sub hψ.2)

/-- Any two local fixed-circle extensions of the same indexed real
action have identical germs at every real-type source in their common
domain. -/
theorem exists_local_sourceActionCircle_eq_of_realAction_agreement
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) (c₀ c₁ : ℂ) (R₀ R₁ : ℝ)
    (V₀ V₁ : Set (CoeffPair p))
    (hV₀open : IsOpen V₀) (hV₁open : IsOpen V₁)
    (hφV₀ : φ ∈ V₀) (hφV₁ : φ ∈ V₁)
    (hdiff₀ : DifferentiableOn ℂ
      (fun ψ : CoeffPair p => sourceActionCircle hp hp1 ψ c₀ R₀) V₀)
    (hdiff₁ : DifferentiableOn ℂ
      (fun ψ : CoeffPair p => sourceActionCircle hp hp1 ψ c₁ R₁) V₁)
    (hreal₀ : ∀ ψ ∈ V₀, ∀ hψ : IsRealType (CoeffPair.toMax p ψ),
      sourceRealAction hp hp1 ψ hψ n =
        sourceActionCircle hp hp1 ψ c₀ R₀)
    (hreal₁ : ∀ ψ ∈ V₁, ∀ hψ : IsRealType (CoeffPair.toMax p ψ),
      sourceRealAction hp hp1 ψ hψ n =
        sourceActionCircle hp hp1 ψ c₁ R₁) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧
      U ⊆ V₀ ∩ V₁ ∧
      ∀ ψ ∈ U,
        sourceActionCircle hp hp1 ψ c₀ R₀ =
          sourceActionCircle hp hp1 ψ c₁ R₁ := by
  apply exists_local_eqOn_of_eqOn_realType hp φ hφ V₀ V₁
    hV₀open hV₁open hφV₀ hφV₁
    (fun ψ => sourceActionCircle hp hp1 ψ c₀ R₀)
    (fun ψ => sourceActionCircle hp hp1 ψ c₁ R₁)
    hdiff₀ hdiff₁
  intro ψ hψ hψreal
  exact (hreal₀ ψ hψ.1 hψreal).symm.trans
    (hreal₁ ψ hψ.2 hψreal)

end NLS.ZakharovShabat
