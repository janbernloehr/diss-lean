import NLS.ZakharovShabat.SmoothSourceGaugeObstruction
import NLS.ZakharovShabat.SourceSection22Higher

noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceSection20Data
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
  {W₀ W V Wa B U : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
  {D : SourceSection17OriginalData hp hp1 W₀ W V s}
  {A : SourceAbelianMomentAtlas hp hp1 Wa s} (Q : SourceSection20Data D A B U)
include Q

/-- Corollary 22.2(iii) extends to every target exponent at least one, including
infinity, using the retained original family's local renormalized solutions. -/
theorem smooth_source_nonextension_all
    {q : ℝ≥0∞} [Fact (1 ≤ q)] (h2p : 2 ≤ p) (T : ℝ) (hT : 0 < T)
    (φ : realTypeSourceSubmodule p) (hφ : φ ∉ sourceHilbertLocus h2p)
    (F : realTypeSourceSubmodule p → C(Icc (0 : ℝ) T,realTypeSourceSubmodule q))
    (hF : AgreesWithSmoothClassicalNLS (Icc (0 : ℝ) T) F) : ¬ ContinuousAt F φ :=
  smooth_source_nonextension_of_local_renormalized hp hp1 h2p
    Q.local_analytic_wellposedness T hT φ hφ F hF

/-- The same endpoint-inclusive obstruction on symmetric compact time intervals. -/
theorem smooth_source_nonextension_all_symmetric
    {q : ℝ≥0∞} [Fact (1 ≤ q)] (h2p : 2 ≤ p) (T : ℝ) (hT : 0 < T)
    (φ : realTypeSourceSubmodule p) (hφ : φ ∉ sourceHilbertLocus h2p)
    (F : realTypeSourceSubmodule p → C(Icc (-T) T,realTypeSourceSubmodule q))
    (hF : AgreesWithSmoothClassicalNLS (Icc (-T) T) F) : ¬ ContinuousAt F φ := by
  intro hcont
  let r : C(Icc (0 : ℝ) T,Icc (-T) T) :=
    ⟨fun τ => ⟨τ.val,by constructor; linarith [τ.property.1]; exact τ.property.2⟩,
      by fun_prop⟩
  exact Q.smooth_source_nonextension_all h2p T hT φ hφ
    (fun ψ => (F ψ).comp r) (fun f τ => hF f (r τ))
    ((ContinuousMap.continuous_precomp r).continuousAt.comp hcont)

end NLS.ZakharovShabat.SourceSection20Data
