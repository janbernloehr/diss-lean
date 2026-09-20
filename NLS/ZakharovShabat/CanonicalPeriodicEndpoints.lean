import NLS.ZakharovShabat.OrderedPeriodicUniqueness

/-!
# Canonical ordered periodic endpoints

Existence chooses one complete ordered endpoint sequence. Uniqueness
makes its two coordinates independent of all central cutoffs and finite
enumerations. They exhaust the original spectrum, retain the labeling's
exact multiplicities, and have lp displacements.
-/

noncomputable section
open Set Complex
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- One admissible cutoff witnessing the canonical periodic endpoints. -/
def canonicalPeriodicCutoff (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) : ℕ :=
  (exists_ordered_periodicEndpointLabeling hp hp1 φ hφ).choose

/-- The first canonical periodic endpoint at each signed index. -/
def canonicalPeriodicLeft (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) : ℤ → ℂ :=
  (exists_ordered_periodicEndpointLabeling hp hp1 φ hφ).choose_spec.choose

/-- The second canonical periodic endpoint at each signed index. -/
def canonicalPeriodicRight (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) : ℤ → ℂ :=
  (exists_ordered_periodicEndpointLabeling hp hp1 φ hφ).choose_spec.choose_spec.choose

/-- The canonical coordinates form a complete globally ordered endpoint labeling. -/
theorem canonicalPeriodicEndpoints_spec (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) :
    PeriodicEndpointLabeling hp φ (canonicalPeriodicCutoff hp hp1 φ hφ)
      (canonicalPeriodicLeft hp hp1 φ hφ) (canonicalPeriodicRight hp hp1 φ hφ) ∧
      (∀ n, complexLexLE (canonicalPeriodicLeft hp hp1 φ hφ n) (canonicalPeriodicRight hp hp1 φ hφ n)) ∧
      ∀ i j : ℤ, i < j → complexLexLE (canonicalPeriodicRight hp hp1 φ hφ i) (canonicalPeriodicLeft hp hp1 φ hφ j) :=
  (exists_ordered_periodicEndpointLabeling hp hp1 φ hφ).choose_spec.choose_spec.choose_spec

/-- Every complete ordered labeling agrees with the canonical endpoints, at any admissible cutoff. -/
theorem PeriodicEndpointLabeling.eq_canonicalPeriodicEndpoints {hp : p ≠ ⊤} {φ : PairSpace p}
    {N : ℕ} {ξ η : ℤ → ℂ} (h : PeriodicEndpointLabeling hp φ N ξ η) (hp1 : 1 < p)
    (hφ : φ ∈ pairParitySubspace 0) (hw : ∀ n, complexLexLE (ξ n) (η n))
    (hc : ∀ i j : ℤ, i < j → complexLexLE (η i) (ξ j)) :
    ξ = canonicalPeriodicLeft hp hp1 φ hφ ∧ η = canonicalPeriodicRight hp hp1 φ hφ :=
  h.ordered_unique (canonicalPeriodicEndpoints_spec hp hp1 φ hφ).1 hw hc
    (canonicalPeriodicEndpoints_spec hp hp1 φ hφ).2.1 (canonicalPeriodicEndpoints_spec hp hp1 φ hφ).2.2

/-- The canonical endpoints enumerate all and only original periodic eigenvalues. -/
theorem canonicalPeriodicEndpoints_exhaustive (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (z : ℂ) :
    z ∈ periodicSpectrum hp φ ↔ ∃ n : ℤ,
      canonicalPeriodicLeft hp hp1 φ hφ n = z ∨ canonicalPeriodicRight hp hp1 φ hφ n = z :=
  (canonicalPeriodicEndpoints_spec hp hp1 φ hφ).1.exhaustive z

/-- Both canonical coordinates at every index are actual periodic eigenvalues. -/
theorem canonicalPeriodicEndpoints_mem_spectrum (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (n : ℤ) :
    canonicalPeriodicLeft hp hp1 φ hφ n ∈ periodicSpectrum hp φ ∧
      canonicalPeriodicRight hp hp1 φ hφ n ∈ periodicSpectrum hp φ :=
  ⟨(canonicalPeriodicEndpoints_exhaustive hp hp1 φ hφ _).mpr ⟨n,Or.inl rfl⟩,
    (canonicalPeriodicEndpoints_exhaustive hp hp1 φ hφ _).mpr ⟨n,Or.inr rfl⟩⟩

/-- The first canonical endpoint displacement, as an lp coefficient. -/
def canonicalPeriodicLeftDisplacement (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) : Coeff p :=
  ⟨fun n => canonicalPeriodicLeft hp hp1 φ hφ n-(Real.pi : ℂ)*n,
    (canonicalPeriodicEndpoints_spec hp hp1 φ hφ).1.left_displacement⟩

/-- The second canonical endpoint displacement, as an lp coefficient. -/
def canonicalPeriodicRightDisplacement (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) : Coeff p :=
  ⟨fun n => canonicalPeriodicRight hp hp1 φ hφ n-(Real.pi : ℂ)*n,
    (canonicalPeriodicEndpoints_spec hp hp1 φ hφ).1.right_displacement⟩

@[simp] theorem canonicalPeriodicLeftDisplacement_apply (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (n : ℤ) :
    canonicalPeriodicLeftDisplacement hp hp1 φ hφ n = canonicalPeriodicLeft hp hp1 φ hφ n-(Real.pi : ℂ)*n := rfl

@[simp] theorem canonicalPeriodicRightDisplacement_apply (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (n : ℤ) :
    canonicalPeriodicRightDisplacement hp hp1 φ hφ n = canonicalPeriodicRight hp hp1 φ hφ n-(Real.pi : ℂ)*n := rfl

/-- Canonical periodic endpoints are real at real-type potentials. -/
theorem canonicalPeriodicEndpoints_im_eq_zero_of_realType (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ) (n : ℤ) :
    (canonicalPeriodicLeft hp hp1 φ hφ n).im = 0 ∧ (canonicalPeriodicRight hp hp1 φ hφ n).im = 0 :=
  (canonicalPeriodicEndpoints_spec hp hp1 φ hφ).1.roots_im_eq_zero_of_realType hreal n

end NLS.ZakharovShabat
