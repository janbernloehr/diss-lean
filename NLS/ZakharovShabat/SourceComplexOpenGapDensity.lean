import NLS.ComplexAnalysis.AnalyticFiniteNonvanishing
import NLS.ZakharovShabat.SourceOpenGapDensity

/-! Real gap-opening witnesses and analytic squared gaps give density
of simultaneous open gaps in the full complex source neighborhood. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1≤p)]

theorem subset_closure_complex_finite_open_gaps
    (hp : p≠⊤) (hp1 : 1<p) (U : Set (CoeffPair p)) (hU : IsOpen U)
    (hconn : IsConnected U) (φ : realTypeSourceSubmodule p) (hφ : φ.val∈U)
    (hγ : ∀ n : ℤ, AnalyticOnNhd ℂ (fun ψ =>
      (sourcePeriodicGapDisplacement hp hp1 ψ n)^2) U) (S : Finset ℤ) :
    U⊆closure {ψ∈U | ∀ n∈S, sourcePeriodicGapDisplacement hp hp1 ψ n≠0} := by
  let V : Set (realTypeSourceSubmodule p) := Subtype.val ⁻¹' U
  have hV : IsOpen V := hU.preimage continuous_subtype_val
  obtain ⟨θ,hθ,hθV,_hclose⟩ := exists_mem_sourceFiniteOpenGapRealLocus_mem_open
    hp hp1 S V hV φ hφ 1 (by norm_num)
  have hn (n : ℤ) (hn : n∈S) : (sourcePeriodicGapDisplacement hp hp1 θ.val n)^2≠0 := by
    apply pow_ne_zero
    simpa only [sourcePeriodicGapDisplacement_apply,sourceOpenGapRealLocus,Set.mem_ofPred_eq] using hθ n hn
  have hd := NLS.ComplexAnalysis.subset_closure_finite_analytic_nonzero hU hconn S
    (fun n ψ => (sourcePeriodicGapDisplacement hp hp1 ψ n)^2) (fun n _ => hγ n) θ.val hθV hn
  have he : {ψ∈U | ∀ n∈S, (sourcePeriodicGapDisplacement hp hp1 ψ n)^2≠0}=
      {ψ∈U | ∀ n∈S, sourcePeriodicGapDisplacement hp hp1 ψ n≠0} := by
    ext ψ
    constructor
    · intro hψ
      refine ⟨hψ.1,?_⟩
      intro n hn hz
      exact hψ.2 n hn (by rw [hz]; norm_num)
    · intro hψ
      exact ⟨hψ.1,fun n hn => pow_ne_zero 2 (hψ.2 n hn)⟩
  rwa [he] at hd

end NLS.ZakharovShabat
