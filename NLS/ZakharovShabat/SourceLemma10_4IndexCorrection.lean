import NLS.ZakharovShabat.SourceStandardRootRealExteriorSign
import NLS.ZakharovShabat.SourceCriticalRootRatioGapSideIntegral
import NLS.ZakharovShabat.SourceFloquetGapOpeningWitness

/-!
# The root index in the proof of Lemma 10.4

The printed statement and proof use w_m on the n-th gap, with m unbound.
The substitution in that proof uses the side values of w_n. This file
refutes the wrong-index midpoint kernel on actual noncollapsed real gaps.
It does not claim to refute every possible wrong-index integral inequality.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The wrong-index affine kernel is real at the selected real gap midpoint. -/
theorem sourceStandardRoot_wrongIndex_midpoint_kernel_im {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p ψ)) {m n : ℤ} (hmn : m ≠ n) :
    (sourceStandardRootHalfGap hp hp1 ψ n /
      sourceStandardRoot hp hp1 ψ m (sourceStandardRootMidpoint hp hp1 ψ n)).im = 0 := by
  have hmid : sourceStandardRootMidpoint hp hp1 ψ n =
      (realGapAffinePoint hp hp1 ψ n 0 : ℂ) := by
    simpa only [sourceCanonicalRootGapPoint, Complex.ofReal_zero, mul_zero, add_zero] using
      sourceCanonicalRootGapPoint_eq_ofReal_realGapAffinePoint hp hp1 ψ hreal n 0
  have ho := NLS.ComplexAnalysis.re_le_of_complexLexLE
    ((canonicalPeriodicEndpoints_spec hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)).2.1 n)
  have hx : realGapAffinePoint hp hp1 ψ n 0 ∈ Icc
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re := by
    dsimp only [realGapAffinePoint]
    constructor <;> nlinarith
  have hr := sourceStandardRoot_im_eq_zero_off_selected_realGap_closedGap hp hp1 ψ hreal hmn hx
  rw [hmid, sourceStandardRootHalfGap_eq_ofReal_affineJacobian hp hp1 ψ hreal n,
    Complex.div_im, hr]
  simp

/-- Hence it cannot equal either of the signed imaginary kernels in the printed proof. -/
theorem sourceStandardRoot_wrongIndex_midpoint_kernel_ne {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p ψ)) {m n : ℤ} (hmn : m ≠ n) (upper : Bool) :
    sourceStandardRootHalfGap hp hp1 ψ n /
      sourceStandardRoot hp hp1 ψ m (sourceStandardRootMidpoint hp hp1 ψ n) ≠
      (if upper then Complex.I else -Complex.I) := by
  intro h
  have him := congrArg Complex.im h
  rw [sourceStandardRoot_wrongIndex_midpoint_kernel_im hp hp1 ψ hreal hmn] at him
  cases upper <;> norm_num at him

/-- Actual noncollapsed real gaps witness failure of the printed wrong-index kernel. -/
theorem sourceLemma10_4_printed_kernel_counterexample {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    ∃ ψ : CoeffPair p, IsRealType (CoeffPair.toMax p ψ) ∧
      canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0 ∧
      ∀ m : ℤ, m ≠ n → ∀ upper : Bool,
        sourceStandardRootHalfGap hp hp1 ψ n /
          sourceStandardRoot hp hp1 ψ m (sourceStandardRootMidpoint hp hp1 ψ n) ≠
          (if upper then Complex.I else -Complex.I) := by
  obtain ⟨ψ,hψ⟩ := exists_real_sourceFloquetGapOpening_ne_zero hp hp1 n
  refine ⟨ψ.val,ψ.property,?_,fun m hmn upper =>
    sourceStandardRoot_wrongIndex_midpoint_kernel_ne hp hp1 ψ.val ψ.property hmn upper⟩
  intro hgap
  exact hψ (sourceFloquetGapOpening_eq_zero_of_closed_gap hp hp1 n ψ.val ψ.property hgap)

end NLS.ZakharovShabat
