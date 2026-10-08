import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! # Differential polynomials in two scalar fields

The variable `(false,k)` denotes the kth derivative of the first field and
`(true,k)` that of the second. The spatial derivation shifts each jet by one.
Support propagation tracks individual monomials, including their two field
counts and their total number of derivatives.
-/
noncomputable section
open MvPolynomial
open scoped ContDiff
namespace NLS.DifferentialPolynomial

abbrev Jet := Bool × ℕ
abbrev Polynomial := MvPolynomial Jet ℂ
abbrev Monomial := Jet →₀ ℕ

def nextJet (v : Jet) : Jet := (v.1,v.2+1)

def spatialDerivative : Derivation ℂ Polynomial Polynomial :=
  MvPolynomial.mkDerivation ℂ (fun v => X (nextJet v))

@[simp] theorem spatialDerivative_X (v : Jet) : spatialDerivative (X v) = X (nextJet v) :=
  MvPolynomial.mkDerivation_X _ _ _

/-- Every nonzero monomial satisfies the stated combinatorial condition. -/
def Supported (P : Monomial → Prop) (p : Polynomial) : Prop :=
  ∀ m ∈ p.support, P m

namespace Supported
variable {P Q : Monomial → Prop} {p q : Polynomial}

theorem zero : Supported P 0 := by simp [Supported]

theorem mono (hp : Supported P p) (h : ∀ m, P m → Q m) : Supported Q p :=
  fun m hm => h m (hp m hm)

theorem add (hp : Supported P p) (hq : Supported P q) : Supported P (p+q) := by
  intro m hm
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  · exact hp m h
  · exact hq m h

theorem neg (hp : Supported P p) : Supported P (-p) := by
  intro m hm
  apply hp m
  simpa only [MvPolynomial.mem_support_iff,MvPolynomial.coeff_neg,neg_ne_zero] using hm

theorem sum {ι : Type*} (S : Finset ι) (f : ι → Polynomial)
    (hf : ∀ i ∈ S, Supported P (f i)) : Supported P (∑ i ∈ S, f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (zero (P := P))
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem monomial (m : Monomial) (c : ℂ) (h : P m) : Supported P (MvPolynomial.monomial m c) := by
  intro d hd
  have he := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hd)
  simpa only [he] using h

theorem X (v : Jet) (h : P (Finsupp.single v 1)) : Supported P (MvPolynomial.X v) :=
  monomial _ _ h

theorem mul {R : Monomial → Prop} (hp : Supported P p) (hq : Supported Q q)
    (h : ∀ a b, P a → Q b → R (a+b)) : Supported R (p*q) := by
  intro m hm
  obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul p q hm)
  exact h a b (hp a ha) (hq b hb)

/-- Differentiation moves one occurrence of a jet to the next derivative. -/
theorem spatialDerivative (hp : Supported P p)
    (h : ∀ m, P m → ∀ v ∈ m.support,
      Q (m-Finsupp.single v 1+Finsupp.single (nextJet v) 1)) :
    Supported Q (DifferentialPolynomial.spatialDerivative p) := by
  classical
  conv => arg 2; rw [p.as_sum]
  rw [map_sum]
  apply sum
  intro m hm
  have he : DifferentialPolynomial.spatialDerivative (MvPolynomial.monomial m (p.coeff m)) =
      ∑ v ∈ m.support, MvPolynomial.monomial
        (m-Finsupp.single v 1+Finsupp.single (nextJet v) 1) (p.coeff m * (m v : ℂ)) := by
    simp [DifferentialPolynomial.spatialDerivative,MvPolynomial.mkDerivation_monomial,
      Finsupp.sum,Algebra.smul_def,MvPolynomial.X,Finset.mul_sum,MvPolynomial.monomial_mul,MvPolynomial.C_mul_monomial]
  rw [he]
  exact sum _ _ (fun v hv => monomial _ _ (h m (hp m hm) v hv))
end Supported

/-- A shifted monomial changes its weight by the prescribed derivative increment. -/
theorem weight_spatial_shift (w : Jet → ℤ) (δ : ℤ)
    (hw : ∀ v, w (nextJet v) = w v+δ) (m : Monomial) (v : Jet) (hv : v ∈ m.support) :
    Finsupp.weight w (m-Finsupp.single v 1+Finsupp.single (nextJet v) 1) =
      Finsupp.weight w m+δ := by
  have h := Finsupp.weight_sub_single_add (w := w) (Finsupp.mem_support_iff.mp hv)
  rw [map_add,Finsupp.weight_single,one_nsmul,hw]
  omega

/-- Differentiation shifts a homogeneous grading whenever each jet has that shift. -/
theorem homogeneous_spatialDerivative (w : Jet → ℤ) (δ d : ℤ)
    (hw : ∀ v, w (nextJet v) = w v+δ) {p : Polynomial}
    (hp : p.IsWeightedHomogeneous w d) :
    (spatialDerivative p).IsWeightedHomogeneous w (d+δ) := by
  have hs : Supported (fun m => Finsupp.weight w m = d) p :=
    fun _ hm => hp (MvPolynomial.mem_support_iff.mp hm)
  have ht := hs.spatialDerivative (Q := fun m => Finsupp.weight w m = d+δ)
    (fun m hm v hv => by rw [weight_spatial_shift w δ hw m v hv,hm])
  exact fun _ hm => ht _ (MvPolynomial.mem_support_iff.mpr hm)

/-- Evaluation on the actual derivatives of smooth scalar functions. -/
def evaluate (a b : ℝ → ℂ) (p : Polynomial) (x : ℝ) : ℂ :=
  MvPolynomial.eval (fun v => iteratedDeriv v.2 (if v.1 then b else a) x) p

@[simp] theorem evaluate_C (a b : ℝ → ℂ) (c : ℂ) : evaluate a b (C c) = fun _ => c := by
  funext x
  simp [evaluate]

@[simp] theorem evaluate_add (a b : ℝ → ℂ) (p q : Polynomial) :
    evaluate a b (p+q) = evaluate a b p+evaluate a b q := by
  funext x
  simp [evaluate]

@[simp] theorem evaluate_mul (a b : ℝ → ℂ) (p q : Polynomial) :
    evaluate a b (p*q) = evaluate a b p*evaluate a b q := by
  funext x
  simp [evaluate]

@[simp] theorem evaluate_neg (a b : ℝ → ℂ) (p : Polynomial) :
    evaluate a b (-p) = -evaluate a b p := by
  funext x
  simp [evaluate]

@[simp] theorem evaluate_X (a b : ℝ → ℂ) (v : Jet) :
    evaluate a b (X v) = iteratedDeriv v.2 (if v.1 then b else a) := by
  funext x
  simp [evaluate]

/-- Formal spatial differentiation agrees with actual differentiation. -/
theorem hasDerivAt_evaluate (a b : ℝ → ℂ) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (p : Polynomial) (x : ℝ) :
    HasDerivAt (evaluate a b p) (evaluate a b (spatialDerivative p) x) x := by
  have hj (v : Jet) : HasDerivAt
      (fun y => iteratedDeriv v.2 (if v.1 then b else a) y)
      (iteratedDeriv (v.2+1) (if v.1 then b else a) x) x := by
    rw [iteratedDeriv_succ]
    have hc : ContDiff ℝ ∞ (if v.1 then b else a) := by split <;> assumption
    exact (hc.differentiable_iteratedDeriv v.2 (by exact_mod_cast (WithTop.coe_lt_top (a := v.2))) x).hasDerivAt
  induction p using MvPolynomial.induction_on with
  | C c => simpa only [MvPolynomial.derivation_C,evaluate_C,show (0 : Polynomial) = C 0 from (map_zero C).symm] using hasDerivAt_const x c
  | add p q hp hq => simpa only [map_add,evaluate_add,Pi.add_apply] using hp.add hq
  | mul_X p v hp =>
    convert! hp.mul (hj v) using 1 <;>
      simp [Derivation.leibniz,smul_eq_mul,nextJet,mul_comm,add_comm]

theorem evaluate_spatialDerivative (a b : ℝ → ℂ) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (p : Polynomial) : evaluate a b (spatialDerivative p) = deriv (evaluate a b p) := by
  funext x
  exact (hasDerivAt_evaluate a b ha hb p x).deriv.symm

end NLS.DifferentialPolynomial
