import NLS.ComplexAnalysis.PiecewiseLoopPullback
import NLS.ComplexAnalysis.LocalHolomorphicPathPullback

/-! Actual piecewise smooth loops can be mapped by a function smooth
only on their domain. Path.map' supplies the local continuity; the
holomorphic chain rule retains exact integrability and actual integrals. -/
noncomputable section
open Set Metric Complex
namespace NLS.ComplexAnalysis
namespace PiecewiseC1Loop

def mapOn (Γ : PiecewiseC1Loop) (T : ℂ → ℂ) (U : Set ℂ)
    (hT : ContDiffOn ℝ 1 T U) (hΓ : Γ.Inside U) : PiecewiseC1Loop where
  count := Γ.count
  vertex := fun k => T (Γ.vertex k)
  edge := fun i => (Γ.edge i).map' (hT.continuousOn.mono (by
    rintro z ⟨t,rfl⟩
    exact hΓ i t))
  smooth := by
    intro i
    change ContDiffOn ℝ 1 (T ∘ (Γ.edge i).extend) (Icc 0 1)
    apply hT.comp (Γ.smooth i)
    intro t ht
    simpa only [Path.extend_apply (Γ.edge i) ht] using hΓ i ⟨t,ht⟩
  closed := congrArg T Γ.closed

theorem mapOn_edge_extend (Γ : PiecewiseC1Loop) (T : ℂ → ℂ) (U : Set ℂ)
    (hT : ContDiffOn ℝ 1 T U) (hΓ : Γ.Inside U) (i : Fin Γ.count) (t : ℝ) :
    ((Γ.mapOn T U hT hΓ).edge i).extend t = T ((Γ.edge i).extend t) := rfl

theorem inside_mapOn_iff (Γ : PiecewiseC1Loop) (T : ℂ → ℂ) (U V : Set ℂ)
    (hT : ContDiffOn ℝ 1 T U) (hΓ : Γ.Inside U) :
    (Γ.mapOn T U hT hΓ).Inside V ↔ Γ.Inside (T ⁻¹' V) := Iff.rfl

theorem integral_mapOn_of_holomorphic_pullback
    (Γ : PiecewiseC1Loop) (T : ℂ → ℂ) (U : Set ℂ)
    (hT : ContDiffOn ℝ 1 T U) (hΓ : Γ.Inside U) (dT f g : ℂ → ℂ)
    (hdT : ∀ z ∈ U, HasDerivAt T (dT z) z)
    (hpull : ∀ z ∈ U, f (T z)*dT z = g z) :
    (Γ.mapOn T U hT hΓ).integral f = Γ.integral g := by
  unfold integral
  apply Finset.sum_congr rfl
  intro i _
  exact (holomorphicPathPullback_of_extend_eq f g T dT (Γ.edge i)
    ((Γ.mapOn T U hT hΓ).edge i) (Γ.smooth i) (fun _ => rfl)
    (fun t ht => hdT _ (by
      simpa only [Path.extend_apply (Γ.edge i) (Ioo_subset_Icc_self ht)] using hΓ i ⟨t,Ioo_subset_Icc_self ht⟩))
    (fun t ht => hpull _ (by
      simpa only [Path.extend_apply (Γ.edge i) (Ioo_subset_Icc_self ht)] using hΓ i ⟨t,Ioo_subset_Icc_self ht⟩))).2

end PiecewiseC1Loop
end NLS.ComplexAnalysis
