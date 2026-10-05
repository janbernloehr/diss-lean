import NLS.SequenceSpaces.ExponentEmbedding
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! # Derivatives of analytic action corrections in a refined target

An exact coordinate identity in a smaller sequence target gives an exact
factorization of bounded derivatives. The inclusion is used only as a
bounded operator; no compactness of sequence inclusions is asserted.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {q r : ℝ≥0∞} [Fact (1 ≤ q)] [Fact (1 ≤ r)]

/-- Differentiate the correction identity as an equality of bounded operators. -/
theorem actionCorrection_fderiv_factorization (hrq : r ≤ q)
    (V : Set (Coeff q)) (hV : IsOpen V) (F : Coeff q → Coeff q) (H : Coeff q → Coeff r)
    (hF : AnalyticOnNhd ℂ F V) (hH : AnalyticOnNhd ℂ H V)
    (he : ∀ b ∈ V, ∀ n, H b n = F b n+2*b n) (b : Coeff q) (hb : b ∈ V) :
    fderiv ℂ F b + (2 : ℂ) • ContinuousLinearMap.id ℂ (Coeff q) =
      (exponentInclusion hrq).comp (fderiv ℂ H b) := by
  have hlocal : (fun c => exponentInclusion hrq (H c)) =ᶠ[𝓝 b]
      (fun c => F c+(2 : ℂ) • c) := by
    filter_upwards [hV.mem_nhds hb] with c hc
    ext n
    exact he c hc n
  have hleft := (exponentInclusion hrq).hasFDerivAt.comp b (hH b hb).differentiableAt.hasFDerivAt
  have hright := (hF b hb).differentiableAt.hasFDerivAt.add
    ((hasFDerivAt_id b).const_smul (2 : ℂ))
  exact hright.fderiv.symm.trans (hlocal.fderiv_eq.symm.trans hleft.fderiv)

/-- The same identity applies to each direction and retains the refined
operator norm bound before the inclusion into the original target. -/
theorem actionCorrection_fderiv_apply_bound (hrq : r ≤ q)
    (V : Set (Coeff q)) (hV : IsOpen V) (F : Coeff q → Coeff q) (H : Coeff q → Coeff r)
    (hF : AnalyticOnNhd ℂ F V) (hH : AnalyticOnNhd ℂ H V)
    (he : ∀ b ∈ V, ∀ n, H b n = F b n+2*b n) (b : Coeff q) (hb : b ∈ V) (v : Coeff q) :
    (∀ n, (fderiv ℂ H b v) n = (fderiv ℂ F b v) n+2*v n) ∧
    ‖fderiv ℂ F b v+(2 : ℂ) • v‖ ≤ ‖fderiv ℂ H b‖*‖v‖ := by
  have hd := congrArg (fun L : Coeff q →L[ℂ] Coeff q => L v)
    (actionCorrection_fderiv_factorization hrq V hV F H hF hH he b hb)
  change fderiv ℂ F b v+(2 : ℂ) • v = exponentInclusion hrq (fderiv ℂ H b v) at hd
  refine ⟨?_,?_⟩
  · intro n
    exact (congrArg (fun c : Coeff q => c n) hd).symm
  · rw [hd]
    exact (norm_exponentInclusion_le hrq _).trans ((fderiv ℂ H b).le_opNorm v)

end NLS.Coeff
