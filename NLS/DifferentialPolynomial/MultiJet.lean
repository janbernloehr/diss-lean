import NLS.DifferentialPolynomial.JetAlgebra
import NLS.FunctionalAnalysis.PeriodicIntegrationByParts

/-! # Differential polynomials with an arbitrary family of scalar fields

Additional jet families let arbitrary variations be independent variables.
Evolutionary differentiation commutes with spatial differentiation because
the variation of each jet is the corresponding derivative of its field variation.
-/
noncomputable section
open MvPolynomial
open scoped ContDiff
namespace NLS.DifferentialPolynomial

abbrev MultiJetPolynomial (σ : Type*) := MvPolynomial (σ × ℕ) ℂ

def multiSpatialDerivative (σ : Type*) :
    Derivation ℂ (MultiJetPolynomial σ) (MultiJetPolynomial σ) :=
  MvPolynomial.mkDerivation ℂ (fun v => X (v.1,v.2+1))

@[simp] theorem multiSpatialDerivative_X {σ : Type*} (v : σ × ℕ) :
    multiSpatialDerivative σ (X v) = X (v.1,v.2+1) := MvPolynomial.mkDerivation_X _ _ _

@[simp] theorem iterate_multiSpatialDerivative_X {σ : Type*} (i : σ) (j n : ℕ) :
    ((multiSpatialDerivative σ : MultiJetPolynomial σ → MultiJetPolynomial σ)^[n]) (X (i,j)) =
      X (i,j+n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', ih, multiSpatialDerivative_X]; congr 1

def evolutionaryDerivative {σ : Type*} (V : σ → MultiJetPolynomial σ) :
    Derivation ℂ (MultiJetPolynomial σ) (MultiJetPolynomial σ) :=
  MvPolynomial.mkDerivation ℂ
    (fun v => ((multiSpatialDerivative σ : MultiJetPolynomial σ → MultiJetPolynomial σ)^[v.2]) (V v.1))

@[simp] theorem evolutionaryDerivative_X {σ : Type*} (V : σ → MultiJetPolynomial σ) (v : σ × ℕ) :
    evolutionaryDerivative V (X v) =
      ((multiSpatialDerivative σ : MultiJetPolynomial σ → MultiJetPolynomial σ)^[v.2]) (V v.1) :=
  MvPolynomial.mkDerivation_X _ _ _

theorem evolutionaryDerivative_commute {σ : Type*} (V : σ → MultiJetPolynomial σ)
    (p : MultiJetPolynomial σ) :
    evolutionaryDerivative V (multiSpatialDerivative σ p) =
      multiSpatialDerivative σ (evolutionaryDerivative V p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [Derivation.leibniz, smul_eq_mul, map_add, multiSpatialDerivative_X,
      evolutionaryDerivative_X, hp, Function.iterate_succ_apply']
    ring

def renameFields {σ τ : Type*} (f : σ → τ) : MultiJetPolynomial σ →ₐ[ℂ] MultiJetPolynomial τ :=
  MvPolynomial.rename (fun v => (f v.1,v.2))

theorem renameFields_spatialDerivative {σ τ : Type*} (f : σ → τ) (p : MultiJetPolynomial σ) :
    renameFields f (multiSpatialDerivative σ p) = multiSpatialDerivative τ (renameFields f p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [renameFields]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp [Derivation.leibniz, smul_eq_mul, renameFields]
    exact hp

def evaluateMulti {σ : Type*} (f : σ → ℝ → ℂ) (p : MultiJetPolynomial σ) (x : ℝ) : ℂ :=
  MvPolynomial.eval (fun v => iteratedDeriv v.2 (f v.1) x) p

@[simp] theorem evaluateMulti_C {σ : Type*} (f : σ → ℝ → ℂ) (c : ℂ) :
    evaluateMulti f (C c) = fun _ => c := by funext x; simp [evaluateMulti]

@[simp] theorem evaluateMulti_add {σ : Type*} (f : σ → ℝ → ℂ) (p q : MultiJetPolynomial σ) :
    evaluateMulti f (p+q) = evaluateMulti f p+evaluateMulti f q := by
  funext x; simp [evaluateMulti]

@[simp] theorem evaluateMulti_mul {σ : Type*} (f : σ → ℝ → ℂ) (p q : MultiJetPolynomial σ) :
    evaluateMulti f (p*q) = evaluateMulti f p*evaluateMulti f q := by
  funext x; simp [evaluateMulti]

@[simp] theorem evaluateMulti_X {σ : Type*} (f : σ → ℝ → ℂ) (v : σ × ℕ) :
    evaluateMulti f (X v) = iteratedDeriv v.2 (f v.1) := by funext x; simp [evaluateMulti]

@[simp] theorem evaluateMulti_sub {σ : Type*} (f : σ → ℝ → ℂ) (p q : MultiJetPolynomial σ) :
    evaluateMulti f (p-q) = evaluateMulti f p-evaluateMulti f q := by
  funext x; simp [evaluateMulti]

theorem hasDerivAt_evaluateMulti {σ : Type*} (f : σ → ℝ → ℂ)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (p : MultiJetPolynomial σ) (x : ℝ) :
    HasDerivAt (evaluateMulti f p) (evaluateMulti f (multiSpatialDerivative σ p) x) x := by
  have hj (v : σ × ℕ) : HasDerivAt (iteratedDeriv v.2 (f v.1))
      (iteratedDeriv (v.2+1) (f v.1) x) x := by
    rw [iteratedDeriv_succ]
    exact ((hf v.1).differentiable_iteratedDeriv v.2
      (by exact_mod_cast (WithTop.coe_lt_top (a := v.2))) x).hasDerivAt
  induction p using MvPolynomial.induction_on with
  | C c => simpa only [MvPolynomial.derivation_C,
      show (0 : MultiJetPolynomial σ) = C 0 from (map_zero C).symm, evaluateMulti_C] using hasDerivAt_const x c
  | add p q hp hq => simpa only [map_add, evaluateMulti_add, Pi.add_apply] using hp.add hq
  | mul_X p v hp =>
    convert! hp.mul (hj v) using 1 <;>
      simp [Derivation.leibniz, smul_eq_mul, mul_comm, add_comm]

theorem periodic_evaluateMulti {σ : Type*} (f : σ → ℝ → ℂ)
    (hf : ∀ i, Function.Periodic (f i) 1) (p : MultiJetPolynomial σ) :
    Function.Periodic (evaluateMulti f p) 1 := by
  intro x
  unfold evaluateMulti
  apply congrArg (fun F : (σ × ℕ) → ℂ => MvPolynomial.eval F p)
  funext v
  exact NLS.FunctionalAnalysis.periodic_iteratedDeriv _ 1 (hf v.1) v.2 x

theorem continuous_evaluateMulti {σ : Type*} (f : σ → ℝ → ℂ)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (p : MultiJetPolynomial σ) : Continuous (evaluateMulti f p) :=
  continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_evaluateMulti f hf p x).continuousAt)

theorem integral_evaluateMulti_spatialDerivative {σ : Type*} (f : σ → ℝ → ℂ)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (hp : ∀ i, Function.Periodic (f i) 1)
    (p : MultiJetPolynomial σ) :
    (∫ x in (0 : ℝ)..1, evaluateMulti f (multiSpatialDerivative σ p) x) = 0 := by
  have hc : Continuous (evaluateMulti f (multiSpatialDerivative σ p)) :=
    continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_evaluateMulti f hf _ x).continuousAt)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_evaluateMulti f hf p x) (hc.intervalIntegrable 0 1)]
  have he := periodic_evaluateMulti f hp p 0
  have hend : evaluateMulti f p 1 = evaluateMulti f p 0 := by simpa using he
  rw [hend, sub_self]

end NLS.DifferentialPolynomial
