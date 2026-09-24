import NLS.ZakharovShabat.SourceRealActionLocalOverlap
import Mathlib.Analysis.Convex.PathConnected

/-!
# Agreement across convex overlaps

Local equality near a real-type source propagates through a convex
overlap. On each affine complex line from the source to another point
of the overlap, complex differentiability becomes one-variable
analyticity. The identity principle then gives equality at that point.
-/

noncomputable section
open Set Filter Complex
open scoped ENNReal Topology
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Complex-differentiable source functions agreeing on real-type
sources agree everywhere on a convex common domain containing a
real-type source. -/
theorem eqOn_convex_overlap_of_eqOn_realType
    (hp : p ≠ ⊤)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (V₀ V₁ : Set (CoeffPair p))
    (hV₀open : IsOpen V₀) (hV₁open : IsOpen V₁)
    (hV₀conv : Convex ℝ V₀) (hV₁conv : Convex ℝ V₁)
    (hφV₀ : φ ∈ V₀) (hφV₁ : φ ∈ V₁)
    (F G : CoeffPair p → ℂ)
    (hFdiff : DifferentiableOn ℂ F V₀)
    (hGdiff : DifferentiableOn ℂ G V₁)
    (hreal : ∀ ψ ∈ V₀ ∩ V₁,
      IsRealType (CoeffPair.toMax p ψ) → F ψ = G ψ) :
    EqOn F G (V₀ ∩ V₁) := by
  obtain ⟨U₀,hU₀open,hφU₀,_,hU₀eq⟩ :=
    exists_local_eqOn_of_eqOn_realType hp φ hφ V₀ V₁
      hV₀open hV₁open hφV₀ hφV₁ F G hFdiff hGdiff hreal
  let V := V₀ ∩ V₁
  have hVopen : IsOpen V := hV₀open.inter hV₁open
  have hVconv : Convex ℝ V := hV₀conv.inter hV₁conv
  intro ψ hψ
  let h : CoeffPair p := ψ-φ
  let a : ℂ → CoeffPair p := fun t => φ+t•h
  have ha : Differentiable ℂ a := by
    dsimp [a]
    fun_prop
  let U : Set ℂ := a ⁻¹' V
  have hUopen : IsOpen U := hVopen.preimage ha.continuous
  have h0 : (0:ℂ) ∈ U := by
    simpa [U,a] using (show φ ∈ V from ⟨hφV₀,hφV₁⟩)
  have h1 : (1:ℂ) ∈ U := by
    have ha1 : a 1 = ψ := by dsimp [a,h]; module
    change a 1 ∈ V
    rw [ha1]
    exact hψ
  have hUconv : Convex ℝ U := by
    intro z hz w hw α β hα hβ hab
    have hcomb := hVconv hz hw hα hβ hab
    change a (α • z + β • w) ∈ V
    convert hcomb using 1
    dsimp [a]
    have habC : (α:ℂ)+(β:ℂ)=1 := by exact_mod_cast hab
    have hφeq : φ = (α:ℂ) • φ + (β:ℂ) • φ := by
      rw [← add_smul, habC, one_smul]
    conv_lhs => rw [hφeq]
    module
  have hFline : DifferentiableOn ℂ (fun t => F (a t)) U := by
    intro t ht
    exact (((hFdiff (a t) ht.1).differentiableAt
      (hV₀open.mem_nhds ht.1)).comp t (ha t)).differentiableWithinAt
  have hGline : DifferentiableOn ℂ (fun t => G (a t)) U := by
    intro t ht
    exact (((hGdiff (a t) ht.2).differentiableAt
      (hV₁open.mem_nhds ht.2)).comp t (ha t)).differentiableWithinAt
  have hfg : (fun t => F (a t)) =ᶠ[𝓝 (0:ℂ)] (fun t => G (a t)) := by
    have hevent : ∀ᶠ t in 𝓝 (0:ℂ), a t ∈ U₀ :=
      ha.continuous.continuousAt.eventually
        (hU₀open.mem_nhds (by simpa [a] using hφU₀))
    filter_upwards [hevent] with t ht
    exact hU₀eq ht
  have hEq := (hFline.analyticOnNhd hUopen).eqOn_of_preconnected_of_eventuallyEq
    (hGline.analyticOnNhd hUopen) hUconv.isPreconnected h0 hfg
  simpa [a,h] using hEq h1

/-- Two fixed-circle formulas for the indexed action coincide on
their entire convex overlap, provided each agrees with the real
action and is complex differentiable there. -/
theorem sourceActionCircle_eqOn_convex_overlap
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) (c₀ c₁ : ℂ) (R₀ R₁ : ℝ)
    (V₀ V₁ : Set (CoeffPair p))
    (hV₀open : IsOpen V₀) (hV₁open : IsOpen V₁)
    (hV₀conv : Convex ℝ V₀) (hV₁conv : Convex ℝ V₁)
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
    ∀ ψ ∈ V₀ ∩ V₁,
      sourceActionCircle hp hp1 ψ c₀ R₀ =
        sourceActionCircle hp hp1 ψ c₁ R₁ := by
  apply eqOn_convex_overlap_of_eqOn_realType hp φ hφ V₀ V₁
    hV₀open hV₁open hV₀conv hV₁conv hφV₀ hφV₁
    (fun ψ => sourceActionCircle hp hp1 ψ c₀ R₀)
    (fun ψ => sourceActionCircle hp hp1 ψ c₁ R₁)
    hdiff₀ hdiff₁
  intro ψ hψ hψreal
  exact (hreal₀ ψ hψ.1 hψreal).symm.trans
    (hreal₁ ψ hψ.2 hψreal)

end NLS.ZakharovShabat
