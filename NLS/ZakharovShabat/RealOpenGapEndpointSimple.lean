import NLS.ZakharovShabat.CanonicalCriticalInterlacing

/-! # Noncritical endpoints of every open real periodic gap

The unique critical point in an open gap is strictly inside it. Neither
endpoint can be critical. Thus the sheet vector has nonzero acceleration
at either endpoint, without a cutoff or a simplicity hypothesis supplied
by the caller.
-/

noncomputable section
open Set Complex
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Both endpoint derivatives of the actual discriminant are nonzero
at every open real gap, including central indices. -/
theorem deriv_discriminant_ne_zero_at_open_gap_endpoints
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    (heven : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ) (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 φ heven n).re <
      (canonicalPeriodicRight hp hp1 φ heven n).re) :
    deriv (canonicalDiscriminant hp φ) (canonicalPeriodicLeft hp hp1 φ heven n) ≠ 0 ∧
    deriv (canonicalDiscriminant hp φ) (canonicalPeriodicRight hp hp1 φ heven n) ≠ 0 := by
  have hc := canonicalCriticalPoints_between_of_open_gap hp hp1 φ heven hreal n hopen
  constructor
  · intro hz
    have he := critical_eq_canonicalCriticalPoints_of_mem_gap hp hp1 φ heven hreal n _ hz
      ⟨le_rfl,hopen.le⟩
    have hre := congrArg Complex.re he
    linarith [hc.1]
  · intro hz
    have he := critical_eq_canonicalCriticalPoints_of_mem_gap hp hp1 φ heven hreal n _ hz
      ⟨hopen.le,le_rfl⟩
    have hre := congrArg Complex.re he
    linarith [hc.2]

end NLS.ZakharovShabat
