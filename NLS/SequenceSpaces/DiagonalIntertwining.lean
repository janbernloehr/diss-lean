import NLS.SequenceSpaces.Multiplier
import NLS.SequenceSpaces.OperatorBasisExt

/-! # Bounded diagonal intertwining and inverse columns

Matrix identities on coordinate vectors extend to actual bounded maps.
Intertwining passes to two-sided inverses without applying an unbounded
weight to an arbitrary coefficient vector.
-/
noncomputable section
open scoped ENNReal
namespace NLS.Coeff

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem multiplierCLM_single (d : Coeff ⊤) (n : ℤ) :
    multiplierCLM (p := p) d (lp.single p n 1) = d n • lp.single p n 1 := by
  ext m
  by_cases hmn : m = n <;>
    simp [multiplierCLM_apply,multiplier_apply,lp.single_apply,hmn]

theorem intertwine_diagonal_of_entries (hp : p ≠ ⊤) (d : Coeff ⊤)
    (T S : Coeff p →L[ℂ] Coeff p)
    (h : ∀ m n : ℤ, d n*(T (lp.single p n 1)) m = d m*(S (lp.single p n 1)) m) :
    T.comp (multiplierCLM d) = (multiplierCLM d).comp S := by
  apply continuousLinearMap_eq_of_single hp
  intro n
  ext m
  rw [ContinuousLinearMap.comp_apply,multiplierCLM_single,map_smul]
  exact h m n

theorem inverse_intertwine_diagonal (d : Coeff ⊤)
    (T S R Q : Coeff p →L[ℂ] Coeff p)
    (h : T.comp (multiplierCLM d) = (multiplierCLM d).comp S)
    (hRT : R.comp T = ContinuousLinearMap.id ℂ (Coeff p))
    (hSQ : S.comp Q = ContinuousLinearMap.id ℂ (Coeff p)) :
    R.comp (multiplierCLM d) = (multiplierCLM d).comp Q := by
  apply ContinuousLinearMap.ext
  intro x
  have hh := congrArg (fun L : Coeff p →L[ℂ] Coeff p => L (Q x)) h
  have hs := congrArg (fun L : Coeff p →L[ℂ] Coeff p => L x) hSQ
  have hr := congrArg (fun L : Coeff p →L[ℂ] Coeff p => L (multiplierCLM d (Q x))) hRT
  change S (Q x) = x at hs
  change R (T (multiplierCLM d (Q x))) = multiplierCLM d (Q x) at hr
  change T (multiplierCLM d (Q x)) = multiplierCLM d (S (Q x)) at hh
  rw [hs] at hh
  rw [hh] at hr
  exact hr

theorem inverse_diagonal_entries (d : Coeff ⊤)
    (T S R Q : Coeff p →L[ℂ] Coeff p)
    (h : T.comp (multiplierCLM d) = (multiplierCLM d).comp S)
    (hRT : R.comp T = ContinuousLinearMap.id ℂ (Coeff p))
    (hSQ : S.comp Q = ContinuousLinearMap.id ℂ (Coeff p)) (m n : ℤ) :
    d n*(R (lp.single p n 1)) m = d m*(Q (lp.single p n 1)) m := by
  have he := congrArg (fun L : Coeff p →L[ℂ] Coeff p => L (lp.single p n 1) m)
    (inverse_intertwine_diagonal d T S R Q h hRT hSQ)
  change R (multiplierCLM d (lp.single p n 1)) m = _ at he
  rw [multiplierCLM_single,map_smul] at he
  exact he

end NLS.Coeff
