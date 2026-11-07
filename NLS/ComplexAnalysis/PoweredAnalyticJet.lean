import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Basic
import NLS.FunctionalAnalysis.PencilRootChains

/-! # Vanishing finite jets of powered Banach-valued analytic germs -/
noncomputable section
open Set Filter Topology
namespace NLS.ComplexAnalysis
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Multiplication by the Nth monomial kills every derivative of smaller order,
also for functions with values in an arbitrary complex normed space. -/
theorem iteratedDeriv_pow_smul_zero {g : ℂ → F} (hg : AnalyticAt ℂ g 0)
    (N k : ℕ) (hk : k < N) :
    iteratedDeriv k (fun t : ℂ => t^N • g t) 0 = 0 := by
  have hp : ContDiffAt ℂ k (fun t : ℂ => t^N) 0 := (analyticAt_id.pow N).contDiffAt
  have he := iteratedDerivWithin_smul (𝕜 := ℂ) (𝔸 := ℂ)
    (mem_univ (0:ℂ)) uniqueDiffOn_univ hp.contDiffWithinAt
      (hg.contDiffAt (n := k)).contDiffWithinAt
  simp only [iteratedDerivWithin_univ, Pi.smul_def'] at he
  rw [he]
  apply Finset.sum_eq_zero
  intro i hi
  have hiN : i < N := lt_of_le_of_lt (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) hk
  rw [iteratedDeriv_fun_pow_zero, if_neg (ne_of_lt hiN)]
  simp

/-- An analytic powered remainder gives zero derivatives of the entire equal germ
through every order strictly below its power. -/
theorem iteratedDeriv_eq_zero_of_powered_germ {f g : ℂ → F}
    (hg : AnalyticAt ℂ g 0) (N : ℕ)
    (he : f =ᶠ[𝓝 0] fun t : ℂ => t^N • g t) (k : ℕ) (hk : k < N) :
    iteratedDeriv k f 0 = 0 :=
  (he.iteratedDeriv_eq k).trans (iteratedDeriv_pow_smul_zero hg N k hk)

/-- Ordinary finite polynomial coefficients are recovered by their spectral
derivatives with the exact factorial normalization, for Banach-valued data. -/
theorem iteratedDeriv_chainPolynomial (N : ℕ) (v : Fin N → F) (k : Fin N) :
    iteratedDeriv k.val (NLS.FunctionalAnalysis.pencilChainPolynomial N v) 0 =
      (k.val.factorial:ℂ) • v k := by
  classical
  unfold NLS.FunctionalAnalysis.pencilChainPolynomial
  rw [iteratedDeriv_fun_sum (fun j _ =>
    ((analyticAt_id.pow j.val).smul (analyticAt_const (v := v j))).contDiffAt)]
  calc
    (∑ j : Fin N, iteratedDeriv k.val (fun t : ℂ => t^j.val • v j) 0) =
        ∑ j : Fin N, if k = j then (k.val.factorial:ℂ) • v j else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [iteratedDeriv_smul_const ((analyticAt_id.pow j.val).contDiffAt),
        iteratedDeriv_fun_pow_zero]
      by_cases h : k = j
      · subst j
        simp
      · have hne : k.val ≠ j.val := fun he => h (Fin.ext he)
        rw [if_neg hne, if_neg h]
        simp
    _ = _ := by simp

/-- A finite domain polynomial with a powered analytic germ beyond its degree
has every retained coefficient zero. -/
theorem chainPolynomial_eq_zero_of_powered_germ (N : ℕ) (v : Fin N → F)
    {g : ℂ → F} (hg : AnalyticAt ℂ g 0)
    (he : NLS.FunctionalAnalysis.pencilChainPolynomial N v =ᶠ[𝓝 0]
      fun t : ℂ => t^N • g t) : v = 0 := by
  funext k
  have hd := iteratedDeriv_eq_zero_of_powered_germ hg N he k.val k.isLt
  rw [iteratedDeriv_chainPolynomial] at hd
  exact (smul_eq_zero.mp hd).resolve_left (by exact_mod_cast Nat.factorial_ne_zero k.val)

end NLS.ComplexAnalysis
