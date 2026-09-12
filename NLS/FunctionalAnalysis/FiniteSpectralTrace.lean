import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Analytic.Constructions

/-!
# Two-dimensional spectral traces

Trace and the centered second trace recover the midpoint and squared gap of
an eigenvalue pair, including a repeated eigenvalue and nontrivial Jordan blocks.
These finite-dimensional identities underlie Lemma 3.7, printed page 27.
-/

noncomputable section
open Polynomial

namespace NLS.FiniteSpectralTrace

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- In dimension two, the eigenvalue support determines the roots with multiplicity,
provided both listed values occur. Repetition is allowed. -/
theorem roots_eq_pair (A : Module.End ℂ V) (hdim : Module.finrank ℂ V = 2) (a b : ℂ)
    (ha : A.HasEigenvalue a) (hb : A.HasEigenvalue b)
    (honly : ∀ z : ℂ, A.HasEigenvalue z → z = a ∨ z = b) : A.charpoly.roots = {a, b} := by
  have hs : A.charpoly.Splits := IsAlgClosed.splits _
  have hcard : A.charpoly.roots.card = 2 := by
    rw [← hs.natDegree_eq_card_roots, A.charpoly_natDegree, hdim]
  have hmem (z : ℂ) : z ∈ A.charpoly.roots ↔ A.HasEigenvalue z := by
    rw [Polynomial.mem_roots A.charpoly_monic.ne_zero,
      ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
  obtain ⟨u, v, huv⟩ := Multiset.card_eq_two.mp hcard
  have hauv : a = u ∨ a = v := by simpa [huv] using (hmem a).mpr ha
  have hbuv : b = u ∨ b = v := by simpa [huv] using (hmem b).mpr hb
  have hua : u = a ∨ u = b := honly u ((hmem u).mp (by simp [huv]))
  have hva : v = a ∨ v = b := honly v ((hmem v).mp (by simp [huv]))
  by_cases hab : a = b
  · subst b
    have hu : u = a := hua.elim id id
    have hv : v = a := hva.elim id id
    simpa [hu, hv] using huv
  · rcases hauv with rfl | rfl <;> rcases hbuv with rfl | rfl
    · exact False.elim (hab rfl)
    · exact huv
    · simpa only [Multiset.pair_comm b a] using huv
    · exact False.elim (hab rfl)

/-- The characteristic polynomial retains the double root in the coincident case. -/
theorem charpoly_eq_pair (A : Module.End ℂ V) (hdim : Module.finrank ℂ V = 2) (a b : ℂ)
    (ha : A.HasEigenvalue a) (hb : A.HasEigenvalue b)
    (honly : ∀ z : ℂ, A.HasEigenvalue z → z = a ∨ z = b) :
    A.charpoly = (X - C a) * (X - C b) := by
  have hs : A.charpoly.Splits := IsAlgClosed.splits _
  rw [hs.eq_prod_roots, A.charpoly_monic.leadingCoeff, map_one, one_mul,
    roots_eq_pair A hdim a b ha hb honly]
  simp

/-- First and second traces are the corresponding power sums of the two eigenvalues. -/
theorem trace_pair (A : Module.End ℂ V) (hdim : Module.finrank ℂ V = 2) (a b : ℂ)
    (ha : A.HasEigenvalue a) (hb : A.HasEigenvalue b)
    (honly : ∀ z : ℂ, A.HasEigenvalue z → z = a ∨ z = b) :
    LinearMap.trace ℂ V A = a + b ∧ LinearMap.trace ℂ V (A ^ 2) = a ^ 2 + b ^ 2 := by
  have ht : LinearMap.trace ℂ V A = a + b := by
    rw [Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _),
      roots_eq_pair A hdim a b ha hb honly]
    simp
  refine ⟨ht, ?_⟩
  have hpoly : A.charpoly = X ^ 2 - C (a+b) * X + C (a*b) := by
    rw [charpoly_eq_pair A hdim a b ha hb honly, map_add, map_mul]
    ring
  have hCH := A.aeval_self_charpoly
  rw [hpoly] at hCH
  have hrel : A ^ 2 - (a+b) • A + (a*b) • (1 : Module.End ℂ V) = 0 := by
    simpa only [map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C,
      Algebra.algebraMap_eq_smul_one, add_smul, add_mul, smul_mul_assoc, one_mul, smul_smul] using hCH
  have htr := congrArg (LinearMap.trace ℂ V) hrel
  simp only [map_add, map_sub, map_smul, map_zero, LinearMap.trace_one, hdim, Nat.cast_ofNat,
    smul_eq_mul, ht] at htr
  linear_combination htr

/-- The trace of a centered square, without a diagonalizability assumption. -/
theorem trace_centered_square (A : Module.End ℂ V) (t : ℂ) :
    LinearMap.trace ℂ V ((A - t • 1) ^ 2) = LinearMap.trace ℂ V (A ^ 2) -
      2 * t * LinearMap.trace ℂ V A + t ^ 2 * (Module.finrank ℂ V : ℂ) := by
  simp only [pow_two, sub_mul, mul_sub, mul_smul_comm, smul_mul_assoc,
    one_mul, mul_one, map_sub, map_smul, LinearMap.trace_one, smul_eq_mul]
  ring

/-- The midpoint and squared gap are symmetric trace expressions, also at a double root. -/
theorem midpoint_gap_eq (A : Module.End ℂ V) (hdim : Module.finrank ℂ V = 2) (a b : ℂ)
    (ha : A.HasEigenvalue a) (hb : A.HasEigenvalue b)
    (honly : ∀ z : ℂ, A.HasEigenvalue z → z = a ∨ z = b) :
    LinearMap.trace ℂ V A / 2 = (a+b)/2 ∧
      2 * LinearMap.trace ℂ V (A ^ 2) - (LinearMap.trace ℂ V A) ^ 2 = (a-b)^2 ∧
      LinearMap.trace ℂ V ((A - (LinearMap.trace ℂ V A / 2) • 1)^2) = (a-b)^2/2 := by
  obtain ⟨h₁, h₂⟩ := trace_pair A hdim a b ha hb honly
  rw [trace_centered_square, h₁, h₂, hdim]
  norm_num only [Nat.cast_ofNat]
  constructor
  · trivial
  constructor <;> ring

section Analytic

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- Trace as a bounded linear functional on the finite-dimensional operator space. -/
def traceCLM : (E →L[ℂ] E) →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap ((LinearMap.trace ℂ E).comp (ContinuousLinearMap.coeLM ℂ))

@[simp] theorem traceCLM_apply (A : E →L[ℂ] E) : traceCLM E A = LinearMap.trace ℂ E A.toLinearMap := rfl

variable {E} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- Analyticity of finite-dimensional traces follows from bounded linearity. -/
theorem analyticAt_trace {A : X → E →L[ℂ] E} {x : X} (hA : AnalyticAt ℂ A x) :
    AnalyticAt ℂ (fun y => LinearMap.trace ℂ E (A y).toLinearMap) x :=
  (traceCLM E).analyticAt _ |>.comp (f := A) hA

/-- The second trace is analytic as well, including across eigenvalue collisions. -/
theorem analyticAt_trace_square {A : X → E →L[ℂ] E} {x : X} (hA : AnalyticAt ℂ A x) :
    AnalyticAt ℂ (fun y => LinearMap.trace ℂ E ((A y).toLinearMap ^ 2)) x := by
  have h := analyticAt_trace (hA.pow 2)
  exact h

end Analytic

end NLS.FiniteSpectralTrace
