import NLS.ZakharovShabat.SourceQEquation
import NLS.ZakharovShabat.BilinearGreen

/-! # Direct transpose identities in the proof of Lemma 6.7

The complementary inverse, each potential Neumann term, and the full corrected
potential are symmetric for the unconjugated cross-component Fourier pairing.
The second input lies in the actual derivative domain; its one derivative
supplies the l1 test needed for every finite Banach exponent. These are
well-defined transpose identities for the pp.40-41 argument, without assuming
a reality sign or asserting a Hilbert adjoint on a general lᵖ space.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The pairing is additive in its derivative-domain input. -/
theorem weightedGreenPairing_add_right (hp : p ≠ ⊤) (w : SpectralWeight)
    (a : WeightedCoeffPair w.toWeight p) (f g : WeightedDomain w.toWeight p) :
    weightedGreenPairing hp w a (f+g) =
      weightedGreenPairing hp w a f + weightedGreenPairing hp w a g := by
  simp only [weightedGreenPairing,greenPairing,map_add,Prod.fst_add,Prod.snd_add,
    ← Coeff.testDualityCLM_apply]
  ring

/-- The actual complementary inverse is transpose symmetric, including at free centers. -/
theorem weightedGreenPairing_complementaryInverse_symm (hp : p ≠ ⊤) (w : SpectralWeight)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (a b : WeightedCoeffPair w.toWeight p) :
    weightedGreenPairing hp w a (complementaryFreeDomainInverse w.toWeight n z hz b) =
      weightedGreenPairing hp w b (complementaryFreeDomainInverse w.toWeight n z hz a) := by
  simp only [weightedGreenPairing_apply,complementaryFreeDomainInverse_fst,
    complementaryFreeDomainInverse_snd,neg_neg]
  rw [add_comm]
  congr 1
  all_goals
    rw [← (Equiv.neg ℤ).tsum_eq]
    apply tsum_congr
    intro k
    simp only [Equiv.neg_apply,neg_neg]
    ring

/-- The complementary projection transfers to the derivative-domain test with the same index. -/
theorem weightedGreenPairing_complementaryProjection (hp : p ≠ ⊤) (w : SpectralWeight) (n : ℤ)
    (a : WeightedCoeffPair w.toWeight p) (f : WeightedDomain w.toWeight p) :
    weightedGreenPairing hp w (complementaryProjection w.toWeight n a) f =
      weightedGreenPairing hp w a (complementaryProjection w.toWeight.oneDerivative n f) := by
  simp only [weightedGreenPairing_apply]
  congr 1
  all_goals
    apply tsum_congr
    intro k
    simp [neg_eq_iff_eq_neg]

/-- Transposing T=Phi R reverses the actual potential and complementary inverse. -/
theorem weightedGreenPairing_potentialInverse_transfer (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ a : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (f : WeightedDomain w.toWeight p) :
    weightedGreenPairing hp w (weightedPotentialInverse hp w φ n z hz a) f =
      weightedGreenPairing hp w a (complementaryFreeDomainInverse w.toWeight n z hz
        (weightedDomainPotential hp w φ f)) := by
  rw [← weightedDomainPotential_complementaryInverse,
    weightedGreenPairing_potential_symm,weightedGreenPairing_complementaryInverse_symm]

/-- Every term T^j Phi is transpose symmetric before any contraction assumption. -/
theorem weightedGreenPairing_powerPotential_symm (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (j : ℕ) (f g : WeightedDomain w.toWeight p) :
    weightedGreenPairing hp w ((weightedPotentialInverse hp w φ n z hz ^ j)
      (weightedDomainPotential hp w φ f)) g =
      weightedGreenPairing hp w ((weightedPotentialInverse hp w φ n z hz ^ j)
        (weightedDomainPotential hp w φ g)) f := by
  induction j generalizing f g with
  | zero => simpa using weightedGreenPairing_potential_symm hp w φ f g
  | succ j ih =>
    rw [pow_succ',mul_apply_eq_comp,weightedGreenPairing_potentialInverse_transfer,ih,
      weightedDomainPotential_complementaryInverse]
    rw [← mul_apply_eq_comp, ← pow_succ, ← pow_succ']

/-- The full corrected potential is transpose symmetric whenever the shifted square is small. -/
theorem weightedGreenPairing_correctedPotential_symm (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1)
    (f g : WeightedDomain w.toWeight p) :
    weightedGreenPairing hp w (weightedCorrection hp w φ n z hz h
      (weightedDomainPotential hp w φ f)) g =
      weightedGreenPairing hp w (weightedCorrection hp w φ n z hz h
        (weightedDomainPotential hp w φ g)) f := by
  have he := weightedGreenPairing_potential_symm hp w φ
    (f+weightedQSolution hp w φ n z hz h f)
    (g+weightedQSolution hp w φ n z hz h g)
  rw [weightedQSolution_total_potential,weightedQSolution_total_potential,
    weightedGreenPairing_add_right,weightedGreenPairing_add_right] at he
  have hs := weightedGreenPairing_complementaryInverse_symm hp w n z hz
    (weightedCorrection hp w φ n z hz h (weightedDomainPotential hp w φ f))
    (weightedCorrection hp w φ n z hz h (weightedDomainPotential hp w φ g))
  exact add_right_cancel (he.trans (congrArg _ hs.symm))

/-- The unconjugated cross-component pairing in the original source spaces. -/
def sourceGreenPairing (hp : p ≠ ⊤) (a : CoeffPair p)
    (f : WeightedCoeffPair (Weight.sobolev 1) p) : ℂ :=
  weightedGreenPairing hp SpectralWeight.one (unitWeightedPairEquiv a)
    (sourceUnitDomainEquiv.symm f)

/-- Unit-weight transport preserves the original cross-component pairing. -/
theorem sourceGreenPairing_unitInput (hp : p ≠ ⊤)
    (a : WeightedCoeffPair SpectralWeight.one.toWeight p)
    (f : WeightedDomain SpectralWeight.one.toWeight p) :
    sourceGreenPairing hp (sourceWeightedPeriodTwoInput SpectralWeight.one a)
      (sourceUnitDomainEquiv f) = weightedGreenPairing hp SpectralWeight.one a f := by
  unfold sourceGreenPairing
  rw [ContinuousLinearEquiv.symm_apply_apply,unitWeightedPairEquiv_sourceWeightedInput]
  congr 1
  apply weightedPair_ext <;> intro k <;> simp

/-- The source pairing is exactly the two unconjugated reflected Fourier sums. -/
theorem sourceGreenPairing_apply (hp : p ≠ ⊤) (a : CoeffPair p)
    (f : WeightedCoeffPair (Weight.sobolev 1) p) :
    sourceGreenPairing hp a f = (∑' k : ℤ, a.fst k * f.snd.val (-k)) +
      ∑' k : ℤ, a.snd k * f.fst.val (-k) := by
  obtain ⟨f,rfl⟩ := (sourceUnitDomainEquiv (p := p)).surjective f
  unfold sourceGreenPairing
  rw [ContinuousLinearEquiv.symm_apply_apply]
  simp only [weightedGreenPairing_apply,unitWeightedPairEquiv_fst,unitWeightedPairEquiv_snd,
    sourceUnitDomainEquiv_apply,sourceWeightedDomainInput_fst,sourceWeightedDomainInput_snd]

/-- The full corrected potential is transpose symmetric on the original derivative domain. -/
theorem sourceCorrectedPotential_transpose (hp : p ≠ ⊤) (φ : CoeffPair p)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (hs : ‖(sourcePotentialInverse hp φ n z hz).comp (sourcePotentialInverse hp φ n z hz)‖ < 1)
    (f g : WeightedCoeffPair (Weight.sobolev 1) p) :
    sourceGreenPairing hp
      (sourceComplementaryCorrection hp φ n z hz hs (sourceOperator hp φ f-sourceOperator hp 0 f)) g =
    sourceGreenPairing hp
      (sourceComplementaryCorrection hp φ n z hz hs (sourceOperator hp φ g-sourceOperator hp 0 g)) f := by
  obtain ⟨f,rfl⟩ := (sourceUnitDomainEquiv (p := p)).surjective f
  obtain ⟨g,rfl⟩ := (sourceUnitDomainEquiv (p := p)).surjective g
  have h : ‖weightedPotentialSquareInShift hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz‖ < 1 := by
    rwa [sourcePotentialInverse_square_norm] at hs
  have hs' : ‖(sourcePotentialInverse hp (sourceWeightedPeriodTwoInput SpectralWeight.one
      (unitWeightedPairEquiv φ)) n z hz).comp (sourcePotentialInverse hp
        (sourceWeightedPeriodTwoInput SpectralWeight.one (unitWeightedPairEquiv φ)) n z hz)‖ < 1 := by
    simpa only [sourceWeightedInput_unitWeightedPairEquiv] using hs
  have ht (u : WeightedDomain SpectralWeight.one.toWeight p) :
      sourceComplementaryCorrection hp φ n z hz hs
        (sourceOperator hp φ (sourceUnitDomainEquiv u)-sourceOperator hp 0 (sourceUnitDomainEquiv u)) =
      sourceWeightedPeriodTwoInput SpectralWeight.one
        (weightedCorrection hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz h
          (weightedDomainPotential hp SpectralWeight.one (unitWeightedPairEquiv φ) u)) := by
    have he := sourceComplementaryCorrection_weightedInput hp SpectralWeight.one
      (unitWeightedPairEquiv φ) n z hz h hs'
      (weightedDomainPotential hp SpectralWeight.one (unitWeightedPairEquiv φ) u)
    rw [sourceWeightedDomainPotential_eq] at he
    simpa only [sourceWeightedInput_unitWeightedPairEquiv,sourceUnitDomainEquiv_apply] using he.symm
  rw [ht,ht,sourceGreenPairing_unitInput,sourceGreenPairing_unitInput]
  exact weightedGreenPairing_correctedPotential_symm hp SpectralWeight.one (unitWeightedPairEquiv φ) n z hz h f g

end NLS.ZakharovShabat
