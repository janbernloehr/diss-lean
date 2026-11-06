import NLS.ComplexAnalysis.PiecewiseC1Loop
import NLS.ComplexAnalysis.HolomorphicPathPullback

/-! # Exact pullback of actual finite piecewise C1 loop integrals -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
namespace NLS.ComplexAnalysis
namespace PiecewiseC1Loop

def map (Γ : PiecewiseC1Loop) (T : ℂ → ℂ) (hT : ContDiff ℝ 1 T) : PiecewiseC1Loop where
  count := Γ.count
  vertex := fun k => T (Γ.vertex k)
  edge := fun i => (Γ.edge i).map hT.continuous
  smooth := fun i => hT.comp_contDiffOn (Γ.smooth i)
  closed := congrArg T Γ.closed

theorem inside_map_iff (Γ : PiecewiseC1Loop) (T : ℂ → ℂ) (hT : ContDiff ℝ 1 T) (D : Set ℂ) :
    (Γ.map T hT).Inside D ↔ Γ.Inside (T ⁻¹' D) := Iff.rfl

theorem integral_map_of_holomorphic_pullback
    (Γ : PiecewiseC1Loop) (T : ℂ → ℂ) (hT : ContDiff ℝ 1 T)
    (dT f g : ℂ → ℂ) (U : Set ℂ) (hΓ : Γ.Inside U)
    (hdT : ∀ z ∈ U, HasDerivAt T (dT z) z)
    (hpull : ∀ z ∈ U, f (T z)*dT z = g z) :
    (Γ.map T hT).integral f = Γ.integral g := by
  unfold integral
  apply Finset.sum_congr rfl
  intro i _
  exact (holomorphicPathPullback_integral_and_integrability f g T dT hT.continuous
    (Γ.edge i) (Γ.smooth i) (fun t ht => hdT _ (by
      simpa only [Path.extend_apply (Γ.edge i) (Ioo_subset_Icc_self ht)] using hΓ i ⟨t,Ioo_subset_Icc_self ht⟩))
    (fun t ht => hpull _ (by
      simpa only [Path.extend_apply (Γ.edge i) (Ioo_subset_Icc_self ht)] using hΓ i ⟨t,Ioo_subset_Icc_self ht⟩))).2

end PiecewiseC1Loop
end NLS.ComplexAnalysis
