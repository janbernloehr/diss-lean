import NLS.FunctionalAnalysis.ResolventRootSpace
import Mathlib.Algebra.Ring.Idempotent

/-!
# Commuting idempotents on full algebraic root spaces

An idempotent which annihilates an eigenspace annihilates every finite root
chain at that value. Applying this to its complement gives the identity
version. No finite dimensionality or semisimplicity is required.
-/
noncomputable section
namespace NLS.FunctionalAnalysis
variable {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- Annihilation of ordinary eigenvectors extends to every finite root chain. -/
theorem idempotent_eq_zero_on_genEigenspace_nat (P T : Module.End ℂ E)
    (hP : IsIdempotentElem P) (hPT : Commute P T) (μ : ℂ)
    (hzero : ∀ x : E, T x = μ • x → P x = 0) (n : ℕ)
    (x : E) (hx : x ∈ T.genEigenspace μ n) : P x = 0 := by
  have hcomm (y : E) : P (T y) = T (P y) :=
    congrArg (fun S : Module.End ℂ E => S y) hPT.eq
  have hid (y : E) : P (P y) = P y :=
    congrArg (fun S : Module.End ℂ E => S y) hP
  induction n generalizing x with
  | zero =>
    have hx0 : x = 0 := by simpa using hx
    rw [hx0, map_zero]
  | succ n ih =>
    have hy := ih ((T-μ • 1) x) ((mem_genEigenspace_succ_iff T μ n x).mp hx)
    have he : T (P x) = μ • P x := by
      change P (T x-μ • x) = 0 at hy
      rw [map_sub, map_smul, hcomm, sub_eq_zero] at hy
      exact hy
    exact (hid x).symm.trans (hzero (P x) he)

/-- Annihilation of an eigenspace extends to its entire algebraic root space. -/
theorem idempotent_eq_zero_on_genEigenspace_top (P T : Module.End ℂ E)
    (hP : IsIdempotentElem P) (hPT : Commute P T) (μ : ℂ)
    (hzero : ∀ x : E, T x = μ • x → P x = 0)
    (x : E) (hx : x ∈ T.genEigenspace μ ⊤) : P x = 0 := by
  obtain ⟨n, hn⟩ := Module.End.mem_genEigenspace_top.mp hx
  exact idempotent_eq_zero_on_genEigenspace_nat P T hP hPT μ hzero n x
    (Module.End.mem_genEigenspace_nat.mpr hn)

/-- Identity on an eigenspace extends to its entire algebraic root space. -/
theorem idempotent_eq_self_on_genEigenspace_top (P T : Module.End ℂ E)
    (hP : IsIdempotentElem P) (hPT : Commute P T) (μ : ℂ)
    (hfix : ∀ x : E, T x = μ • x → P x = x)
    (x : E) (hx : x ∈ T.genEigenspace μ ⊤) : P x = x := by
  have hcomm : Commute (1-P) T := by
    change (1-P)*T = T*(1-P)
    rw [sub_mul, mul_sub, one_mul, mul_one, hPT.eq]
  have hz := idempotent_eq_zero_on_genEigenspace_top (1-P) T hP.one_sub hcomm μ
    (fun y hy => by change y-P y = 0; rw [hfix y hy, sub_self]) x hx
  change x-P x = 0 at hz
  exact (sub_eq_zero.mp hz).symm

end NLS.FunctionalAnalysis
