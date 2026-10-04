import NLS.SequenceSpaces.QuadraticActionsExponent
import NLS.ZakharovShabat.SourceHilbertActionSequence

/-! # Actual spectral action sequences beyond the Hilbert exponent

The analytic Birkhoff map and its exact action-radius identity assemble
the original actions in the Banach half-exponent space. The derivative
coordinates remain the derivatives of the original spectral actions.
-/
noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q]

/-- The sequence of quadratic Birkhoff actions at the half exponent. -/
def sourceActionSequence (hp : p ≠ ⊤) (hp1 : 1 < p)
    (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n) (φ : CoeffPair p) : Coeff q :=
  quadraticActionsExponent (sourceBirkhoffMap hp hp1 s φ)

namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Every sequence coordinate equals its original spectral action. -/
theorem actionSequence_apply (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (φ : CoeffPair p) (hφ : φ ∈ W) (n : ℤ) :
    sourceActionSequence (q := q) hp hp1 s φ n = sourceComplexAction hp hp1 n φ := by
  rw [sourceActionSequence,quadraticActionsExponent_apply,D.action_radius φ hφ n]
  ring

/-- The full spectral action sequence is analytic in the target norm. -/
theorem actionSequence_analytic (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) :
    AnalyticOnNhd ℂ (sourceActionSequence (q := q) hp hp1 s) W := by
  intro φ hφ
  exact (analyticOnNhd_quadraticActionsExponent _ (mem_univ _)).comp (D.analytic φ hφ)

/-- One bound controls every action coordinate simultaneously. -/
theorem actionSequence_locally_bounded (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (φ : CoeffPair p) (hφ : φ ∈ W) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ U ⊆ W ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ ψ ∈ U, ‖sourceActionSequence (q := q) hp hp1 s ψ‖ ≤ M := by
  obtain ⟨U,hU,hφU,hUW,M,hM,hbound⟩ := D.locally_bounded φ hφ
  refine ⟨U,hU,hφU,hUW,M^2,sq_nonneg _,?_⟩
  intro ψ hψ
  apply (norm_quadraticActionsExponent_le (q := q) _).trans
  exact pow_le_pow_left₀ (norm_nonneg _) (hbound ψ hψ) 2

/-- Evaluating the Banach derivative recovers each scalar action derivative. -/
theorem actionSequence_fderiv_apply (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (φ : CoeffPair p) (hφ : φ ∈ W) (h : CoeffPair p) (n : ℤ) :
    (fderiv ℂ (sourceActionSequence (q := q) hp hp1 s) φ h) n =
      (fderiv ℂ (sourceComplexAction hp hp1 n) φ) h := by
  let ev := lp.evalCLM ℂ (fun _ : ℤ => ℂ) q n
  have hd := (ev.hasFDerivAt.comp φ
    (D.actionSequence_analytic (q := q) φ hφ).differentiableAt.hasFDerivAt).fderiv
  have he : (fun ψ => ev (sourceActionSequence (q := q) hp hp1 s ψ)) =ᶠ[𝓝 φ]
      sourceComplexAction hp hp1 n := by
    filter_upwards [D.source_open.mem_nhds hφ] with ψ hψ
    exact D.actionSequence_apply ψ hψ n
  have hh := he.fderiv_eq.symm.trans hd
  exact (congrArg (fun L : CoeffPair p →L[ℂ] ℂ => L h) hh).symm

end SourceBirkhoffMapComplexData

/-- Construct the analytic action sequence without assuming a Birkhoff family. -/
theorem exists_sourceActionSequence_analytic (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ F : CoeffPair p → Coeff q, ∃ W : Set (CoeffPair p),
      IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      AnalyticOnNhd ℂ F W ∧ AnalyticOnNhd ℝ F W ∧
      ∀ φ ∈ W, ∀ n, F φ n = sourceComplexAction hp hp1 n φ := by
  obtain ⟨W₀,B,W,s,D⟩ := exists_sourceBirkhoffMap_complex_analytic hp hp1
  exact ⟨sourceActionSequence hp hp1 s,W,D.source_open,D.real_subset,
    D.actionSequence_analytic,D.actionSequence_analytic.restrictScalars,D.actionSequence_apply⟩

/-- The generalized action sequence preserves the original Hilbert map. -/
theorem sourceActionSequence_two
    (s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n) (φ : CoeffPair 2) :
    sourceActionSequence (q := 1) (by simp) (by norm_num) s φ =
      sourceHilbertActionSequence s φ := rfl

end NLS.ZakharovShabat
