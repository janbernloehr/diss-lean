import NLS.Poisson.SourceBracket

/-! # Actual Hamiltonian directions in the source coefficient space

The cotangent coefficients are square summable for exponents at least
two. Frequency reflection and the original cross-component Poisson sign
produce a Hilbert direction, then the actual source exponent inclusion
places it in the source space. Every source cotangent evaluates on this
direction to exactly its source bivector pairing with the Hamiltonian
cotangent. No flow existence theorem is asserted here.
-/

noncomputable section
open Complex
open scoped ENNReal
namespace NLS.Poisson

/-- Frequency reversal and the original Poisson signs on a Hilbert
cotangent pair, with the dissertation's actual source-pair norm. -/
def hilbertPairHamiltonianDirection : (Coeff 2 × Coeff 2) →L[ℂ] CoeffPair 2 :=
  (CoeffPair.toMax 2).symm.toContinuousLinearMap.comp
    (((-I) • (Coeff.reflection.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (ContinuousLinearMap.snd ℂ (Coeff 2) (Coeff 2)))).prod
      (I • (Coeff.reflection.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (ContinuousLinearMap.fst ℂ (Coeff 2) (Coeff 2)))))

@[simp] theorem hilbertPairHamiltonianDirection_fst (a : Coeff 2 × Coeff 2) :
    (hilbertPairHamiltonianDirection a).fst = (-I) • Coeff.reflection a.2 := rfl

@[simp] theorem hilbertPairHamiltonianDirection_snd (a : Coeff 2 × Coeff 2) :
    (hilbertPairHamiltonianDirection a).snd = I • Coeff.reflection a.1 := rfl

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual bounded linear operation taking a source cotangent to
its Hamiltonian direction in the same source space. -/
def sourceHamiltonianDirection (h2p : (2 : ℝ≥0∞) ≤ p) :
    (CoeffPair p →L[ℂ] ℂ) →L[ℂ] CoeffPair p :=
  (CoeffPair.exponentInclusion h2p).comp
    (hilbertPairHamiltonianDirection.comp (CoeffPair.cotangentCoefficients h2p))

/-- This identity fixes the direction's sign by the actual source
bivector and holds for arbitrary source cotangents. -/
theorem apply_sourceHamiltonianDirection (h2p : (2 : ℝ≥0∞) ≤ p)
    (L M : CoeffPair p →L[ℂ] ℂ) :
    L (sourceHamiltonianDirection h2p M) = sourceBivector h2p L M := by
  change L (CoeffPair.exponentInclusion h2p
    (hilbertPairHamiltonianDirection (CoeffPair.cotangentCoefficients h2p M))) = _
  rw [← CoeffPair.dualPairing_cotangentCoefficients h2p L]
  simp only [hilbertPairHamiltonianDirection_fst,hilbertPairHamiltonianDirection_snd,
    map_smul,smul_eq_mul]
  change -I*reflectedHilbertPairing (CoeffPair.cotangentCoefficients h2p L).1
      (CoeffPair.cotangentCoefficients h2p M).2+
    I*reflectedHilbertPairing (CoeffPair.cotangentCoefficients h2p L).2
      (CoeffPair.cotangentCoefficients h2p M).1 = _
  change _ = -I*(reflectedHilbertPairing (CoeffPair.cotangentCoefficients h2p L).1
      (CoeffPair.cotangentCoefficients h2p M).2-
    reflectedHilbertPairing (CoeffPair.cotangentCoefficients h2p L).2
      (CoeffPair.cotangentCoefficients h2p M).1)
  ring

/-- The Hamiltonian direction of an actual scalar functional. -/
def sourceHamiltonianVector (h2p : (2 : ℝ≥0∞) ≤ p)
    (G : CoeffPair p → ℂ) (φ : CoeffPair p) : CoeffPair p :=
  sourceHamiltonianDirection h2p (fderiv ℂ G φ)

/-- Every bracket is the actual derivative of its first functional
evaluated on the actual Hamiltonian direction of its second functional. -/
theorem fderiv_apply_sourceHamiltonianVector (h2p : (2 : ℝ≥0∞) ≤ p)
    (F G : CoeffPair p → ℂ) (φ : CoeffPair p) :
    (fderiv ℂ F φ) (sourceHamiltonianVector h2p G φ) = sourceBracket h2p F G φ :=
  apply_sourceHamiltonianDirection h2p _ _

/-- Changing the source exponent commutes with the actual Hamiltonian
direction when the Hamiltonian cotangent is restricted along the inclusion. -/
theorem sourceHamiltonianDirection_restrict_exponent
    {q : ℝ≥0∞} [Fact (1 ≤ q)] (h2p : (2 : ℝ≥0∞) ≤ p) (hpq : p ≤ q)
    (M : CoeffPair q →L[ℂ] ℂ) :
    CoeffPair.exponentInclusion hpq
      (sourceHamiltonianDirection h2p (M.comp (CoeffPair.exponentInclusion hpq))) =
        sourceHamiltonianDirection (h2p.trans hpq) M := by
  change CoeffPair.exponentInclusion hpq (CoeffPair.exponentInclusion h2p
    (hilbertPairHamiltonianDirection
      (CoeffPair.cotangentCoefficients h2p (M.comp (CoeffPair.exponentInclusion hpq))))) = _
  rw [CoeffPair.exponentInclusion_trans,cotangentCoefficients_restrict_exponent]
  rfl

end NLS.Poisson
