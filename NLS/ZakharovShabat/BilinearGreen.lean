import NLS.SequenceSpaces.ReflectedTestSymmetry
import NLS.ZakharovShabat.WeightedDomainPotential

/-!
# A bilinear Green identity at every finite Banach exponent

The pairing is the unconjugated cross-component Fourier integral. A derivative
on the second input supplies `ℓ¹` tests, so the potential transpose identity
holds for general `ℓᵖ` potentials. This avoids a Hilbert-exponent restriction.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The symmetric cross-component bilinear integral, with a derivative-domain test input. -/
def greenPairing (hp : p ≠ ⊤) (a : PairSpace p) (f : Domain p) : ℂ :=
  Coeff.testPairing a.1 (Coeff.reflection (WeightedCoeff.sobolevToL1CLM p hp f.2)) +
    Coeff.testPairing a.2 (Coeff.reflection (WeightedCoeff.sobolevToL1CLM p hp f.1))

/-- The pairing is linear in its coefficient input. -/
theorem greenPairing_add_left (hp : p ≠ ⊤) (a b : PairSpace p) (f : Domain p) :
    greenPairing hp (a+b) f = greenPairing hp a f + greenPairing hp b f := by
  simp only [greenPairing, ← Coeff.testDualityCLM_apply, Prod.fst_add, Prod.snd_add, map_add, add_apply]
  ring

theorem greenPairing_sub_left (hp : p ≠ ⊤) (a b : PairSpace p) (f : Domain p) :
    greenPairing hp (a-b) f = greenPairing hp a f - greenPairing hp b f := by
  simp only [greenPairing, ← Coeff.testDualityCLM_apply, Prod.fst_sub, Prod.snd_sub, map_sub, sub_apply]
  ring

/-- Multiplication by an arbitrary complex off-diagonal potential is symmetric for this pairing. -/
theorem greenPairing_potential_symm (hp : p ≠ ⊤) (φ : PairSpace p) (f g : Domain p) :
    greenPairing hp (potentialOperator hp φ f) g = greenPairing hp (potentialOperator hp φ g) f := by
  change Coeff.testPairing (Coeff.convolution φ.1 (WeightedCoeff.sobolevToL1CLM p hp f.2))
      (Coeff.reflection (WeightedCoeff.sobolevToL1CLM p hp g.2)) +
    Coeff.testPairing (Coeff.convolution φ.2 (WeightedCoeff.sobolevToL1CLM p hp f.1))
      (Coeff.reflection (WeightedCoeff.sobolevToL1CLM p hp g.1)) = _
  exact congrArg₂ (fun x y : ℂ => x + y)
    (Coeff.testPairing_convolution_reflection_symm φ.1
      (WeightedCoeff.sobolevToL1CLM p hp f.2) (WeightedCoeff.sobolevToL1CLM p hp g.2))
    (Coeff.testPairing_convolution_reflection_symm φ.2
      (WeightedCoeff.sobolevToL1CLM p hp f.1) (WeightedCoeff.sobolevToL1CLM p hp g.1))

/-- The same unweighted bilinear integral on the actual weighted base and derivative domain. -/
def weightedGreenPairing (hp : p ≠ ⊤) (w : SpectralWeight)
    (a : WeightedCoeffPair w.toWeight p) (f : WeightedDomain w.toWeight p) : ℂ :=
  greenPairing hp (weightedBaseToPair w a) (weightedDomainToDomain w f)

/-- The weight does not alter the original cross-component Fourier integral. -/
theorem weightedGreenPairing_apply (hp : p ≠ ⊤) (w : SpectralWeight)
    (a : WeightedCoeffPair w.toWeight p) (f : WeightedDomain w.toWeight p) :
    weightedGreenPairing hp w a f = (∑' k : ℤ, a.fst.val k * f.snd.val (-k)) +
      ∑' k : ℤ, a.snd.val k * f.fst.val (-k) := by
  simp only [weightedGreenPairing, greenPairing, Coeff.testPairing, Coeff.reflection_apply,
    WeightedCoeff.sobolevToL1CLM_apply, weightedBaseToPair_fst, weightedBaseToPair_snd,
    weightedDomainToDomain_fst, weightedDomainToDomain_snd]

theorem weightedGreenPairing_sub_left (hp : p ≠ ⊤) (w : SpectralWeight)
    (a b : WeightedCoeffPair w.toWeight p) (f : WeightedDomain w.toWeight p) :
    weightedGreenPairing hp w (a-b) f = weightedGreenPairing hp w a f - weightedGreenPairing hp w b f := by
  simp only [weightedGreenPairing, map_sub, greenPairing_sub_left]

/-- The free differential pencil is symmetric for the bilinear pairing at the same complex parameter. -/
theorem weightedGreenPairing_pencil_symm (hp : p ≠ ⊤) (w : SpectralWeight)
    (z : ℂ) (f g : WeightedDomain w.toWeight p) :
    weightedGreenPairing hp w (weightedFreePencil w.toWeight z f) g =
      weightedGreenPairing hp w (weightedFreePencil w.toWeight z g) f := by
  simp only [weightedGreenPairing_apply, weightedFreePencil_fst, weightedFreePencil_snd]
  rw [Coeff.tsum_reflected_linear_symm f.fst.val g.snd.val z (Real.pi : ℂ),
    ← Coeff.tsum_reflected_linear_symm g.fst.val f.snd.val z (Real.pi : ℂ)]
  exact add_comm _ _

/-- The potential transpose identity holds on every weighted derivative domain. -/
theorem weightedGreenPairing_potential_symm (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (f g : WeightedDomain w.toWeight p) :
    weightedGreenPairing hp w (weightedDomainPotential hp w φ f) g =
      weightedGreenPairing hp w (weightedDomainPotential hp w φ g) f := by
  simp only [weightedGreenPairing, weightedDomainPotential_eq_original]
  exact greenPairing_potential_symm hp _ _ _

/-- Green's identity for the full weighted differential pencil, without a reality condition on the potential. -/
theorem weightedGreenPairing_residual_symm (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (z : ℂ) (f g : WeightedDomain w.toWeight p) :
    weightedGreenPairing hp w (weightedFreePencil w.toWeight z f - weightedDomainPotential hp w φ f) g =
      weightedGreenPairing hp w (weightedFreePencil w.toWeight z g - weightedDomainPotential hp w φ g) f := by
  rw [weightedGreenPairing_sub_left, weightedGreenPairing_sub_left,
    weightedGreenPairing_pencil_symm, weightedGreenPairing_potential_symm]

end NLS.ZakharovShabat
