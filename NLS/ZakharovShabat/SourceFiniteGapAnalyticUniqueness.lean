import NLS.ZakharovShabat.SourceFiniteGapDensity
import NLS.ZakharovShabat.SourceRealActionLocalOverlap
import Mathlib.Analysis.Analytic.Uniqueness

/-! # Analytic uniqueness from actual finite-gap sources

Density extends a finite-gap identity to the real source locus. The
real-form identity principle and connectedness then extend it to the
whole complex domain, for every finite source exponent above one.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Analytic source functions agreeing at all actual real finite-gap
sources agree on their connected almost-real domain. -/
theorem eqOn_of_analytic_of_sourceFiniteGap
    (hp : p ≠ ⊤) (hp1 : 1 < p) {U : Set (CoeffPair p)}
    (hU : IsOpen U) (hUc : IsConnected U) (hreal : realTypeSourceLocus p ⊆ U)
    {F G : CoeffPair p → ℂ} (hF : AnalyticOnNhd ℂ F U) (hG : AnalyticOnNhd ℂ G U)
    (hfinite : ∀ φ : realTypeSourceLocus p, φ ∈ sourceFiniteGapLocus hp hp1 → F φ.val = G φ.val) :
    EqOn F G U := by
  have hrealEq (φ : realTypeSourceLocus p) : F φ.val = G φ.val := by
    apply sub_eq_zero.mp
    apply eq_of_continuousOn_of_sourceFiniteGap hp hp1 isOpen_univ
      (U := Set.univ) (H := fun ψ => F ψ.val-G ψ.val) ?_ 0
      (fun ψ _ hψ => sub_eq_zero.mpr (hfinite ψ hψ)) φ (mem_univ φ)
    exact ((hF.continuousOn.sub hG.continuousOn).comp continuous_subtype_val.continuousOn
      (fun ψ _ => hreal ψ.property))
  have hzero : (0 : CoeffPair p) ∈ realTypeSourceLocus p := by simp [realTypeSourceLocus]
  obtain ⟨T,hT,hzeroT,_,heq⟩ := exists_local_eqOn_of_eqOn_realType hp 0 hzero U U
    hU hU (hreal hzero) (hreal hzero) F G hF.differentiableOn hG.differentiableOn
    (fun ψ _ hψ => hrealEq ⟨ψ,hψ⟩)
  exact hF.eqOn_of_preconnected_of_eventuallyEq hG hUc.isPreconnected (hreal hzero)
    (Filter.eventually_of_mem (hT.mem_nhds hzeroT) heq)

end NLS.ZakharovShabat
