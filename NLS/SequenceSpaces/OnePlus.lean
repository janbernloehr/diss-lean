import NLS.SequenceSpaces.Basic

/-!
# The intersection of all finite sequence exponents above one

`CoeffOnePlus` is the algebraic sequence space denoted `ℓ^(1+)`:
complex sequences that belong to every finite `ℓq` with `q > 1`.
Its coordinate-preserving projections to each `Coeff q` make the
simultaneous-exponent statement explicit. A projective-limit topology
can be added separately when needed.
-/

noncomputable section
open scoped ENNReal
namespace NLS

/-- The algebraic intersection of all finite `ℓq(ℤ, ℂ)` spaces with
`q > 1`. -/
def onePlusSubmodule : Submodule ℂ (PreLp (fun _ : ℤ => ℂ)) where
  carrier := {a | ∀ (q : ℝ≥0∞), 1 < q → q ≠ ⊤ → Memℓp a q}
  zero_mem' := by
    intro q _ _
    exact zero_memℓp
  add_mem' := by
    intro a b ha hb q hq1 hq
    exact (ha q hq1 hq).add (hb q hq1 hq)
  smul_mem' := by
    intro c a ha q hq1 hq
    exact (ha q hq1 hq).const_smul c

/-- `ℓ^(1+)` sequences, with their algebraic complex-vector-space
structure. -/
abbrev CoeffOnePlus := onePlusSubmodule

namespace CoeffOnePlus

/-- The canonical coordinate-preserving projection into a finite
Banach sequence exponent above one. -/
def toCoeff (q : ℝ≥0∞) (_hq1 : 1 < q) (_hq : q ≠ ⊤)
    (a : CoeffOnePlus) : Coeff q :=
  ⟨fun n => a.1 n, a.2 q _hq1 _hq⟩

@[simp] theorem toCoeff_apply (q : ℝ≥0∞) (hq1 : 1 < q) (hq : q ≠ ⊤)
    (a : CoeffOnePlus) (n : ℤ) :
    toCoeff q hq1 hq a n = a.1 n := rfl

/-- Each finite-exponent projection is complex-linear. -/
def toCoeffLinear (q : ℝ≥0∞) (hq1 : 1 < q) (hq : q ≠ ⊤) :
    CoeffOnePlus →ₗ[ℂ] Coeff q where
  toFun := toCoeff q hq1 hq
  map_add' := by
    intro a b
    ext n
    rfl
  map_smul' := by
    intro c a
    ext n
    rfl

@[simp] theorem toCoeffLinear_apply (q : ℝ≥0∞) (hq1 : 1 < q)
    (hq : q ≠ ⊤) (a : CoeffOnePlus) (n : ℤ) :
    toCoeffLinear q hq1 hq a n = a.1 n := rfl

end CoeffOnePlus
end NLS
