import NLS.ZakharovShabat.ResonantDiagonalSymmetry

/-!
# Constant complex potentials and the resonant diagonal

An explicit computation gives `a_n = ab * complementarySymbol n λ (-n)` for
constant components `a,b`. This also tests the hypotheses needed in the
conjugation assertion printed in Lemma 6.7(ii).
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Two amplitudes at the same physical Fourier frequency. -/
def weightedPairMode (w : Weight) (k : ℤ) (a b : ℂ) : WeightedCoeffPair w p :=
  (WeightedCoeffPair.toMax w p).symm (weightedMode w k a, weightedMode w k b)

@[simp] theorem weightedPairMode_fst (w : Weight) (k : ℤ) (a b : ℂ) (j : ℤ) :
    (weightedPairMode (p := p) w k a b).fst.val j = if j = k then a else 0 := weightedMode_apply _ _ _ _
@[simp] theorem weightedPairMode_snd (w : Weight) (k : ℤ) (a b : ℂ) (j : ℤ) :
    (weightedPairMode (p := p) w k a b).snd.val j = if j = k then b else 0 := weightedMode_apply _ _ _ _

/-- A spatially constant off-diagonal potential with arbitrary complex components. -/
def constantSpectralPotential (w : SpectralWeight) (a b : ℂ) : WeightedCoeffPair w.toWeight p :=
  weightedPairMode w.toWeight 0 a b

@[simp] theorem constantSpectralPotential_domain_fst (hp : p ≠ ⊤) (w : SpectralWeight)
    (a b : ℂ) (f : WeightedDomain w.toWeight p) (k : ℤ) :
    (weightedDomainPotential hp w (constantSpectralPotential w a b) f).fst.val k = a * f.snd.val k := by
  rw [weightedDomainPotential_fst]
  simp [constantSpectralPotential, ite_mul, sub_eq_zero]

@[simp] theorem constantSpectralPotential_domain_snd (hp : p ≠ ⊤) (w : SpectralWeight)
    (a b : ℂ) (f : WeightedDomain w.toWeight p) (k : ℤ) :
    (weightedDomainPotential hp w (constantSpectralPotential w a b) f).snd.val k = b * f.fst.val k := by
  rw [weightedDomainPotential_snd]
  simp [constantSpectralPotential, ite_mul, sub_eq_zero]

@[simp] theorem constantSpectralPotential_inverse_fst (hp : p ≠ ⊤) (w : SpectralWeight)
    (a b : ℂ) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) (f : WeightedCoeffPair w.toWeight p) (k : ℤ) :
    (weightedPotentialInverse hp w (constantSpectralPotential w a b) n z hz f).fst.val k =
      a * (complementarySymbol n z k * f.snd.val k) := by
  have he := congrArg (fun v => v.fst.val k)
    (weightedDomainPotential_complementaryInverse hp w (constantSpectralPotential w a b) f n z hz)
  simpa only [constantSpectralPotential_domain_fst, complementaryFreeDomainInverse_snd] using he.symm

@[simp] theorem constantSpectralPotential_inverse_snd (hp : p ≠ ⊤) (w : SpectralWeight)
    (a b : ℂ) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) (f : WeightedCoeffPair w.toWeight p) (k : ℤ) :
    (weightedPotentialInverse hp w (constantSpectralPotential w a b) n z hz f).snd.val k =
      b * (complementarySymbol n z (-k) * f.fst.val k) := by
  have he := congrArg (fun v => v.snd.val k)
    (weightedDomainPotential_complementaryInverse hp w (constantSpectralPotential w a b) f n z hz)
  simpa only [constantSpectralPotential_domain_snd, complementaryFreeDomainInverse_fst] using he.symm

/-- The exact diagonal correction for arbitrary constant complex potentials. -/
theorem weightedResonantA_constant (hp : p ≠ ⊤) (w : SpectralWeight) (a b : ℂ)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w (constantSpectralPotential w a b) n z hz‖ < 1) :
    weightedResonantA hp w (constantSpectralPotential w a b) n z hz h = a * b * complementarySymbol n z (-n) := by
  let φ := constantSpectralPotential (p := p) w a b
  let u := resonantSynthesis (p := p) w.toWeight.oneDerivative n (Pi.single 0 1)
  let x := weightedPairMode (p := p) w.toWeight (-n) (a*b*complementarySymbol n z (-n)) b
  have hx : x - weightedPotentialInverse hp w φ n z hz x = weightedDomainPotential hp w φ u := by
    apply weightedPair_ext <;> intro k
    · change x.fst.val k - (weightedPotentialInverse hp w (constantSpectralPotential w a b) n z hz x).fst.val k =
        (weightedDomainPotential hp w (constantSpectralPotential w a b) u).fst.val k
      rw [constantSpectralPotential_inverse_fst, constantSpectralPotential_domain_fst]
      by_cases hk : k = -n <;> simp [x, u, hk]
      ring
    · change x.snd.val k - (weightedPotentialInverse hp w (constantSpectralPotential w a b) n z hz x).snd.val k =
        (weightedDomainPotential hp w (constantSpectralPotential w a b) u).snd.val k
      rw [constantSpectralPotential_inverse_snd, constantSpectralPotential_domain_snd]
      by_cases hk : k = -n <;> simp [x, u, hk]
  have he := weightedCorrection_unique hp w φ n z hz h x (weightedDomainPotential hp w φ u) hx
  unfold weightedResonantA weightedCorrectionMatrix
  rw [resonantCoordinates_zero]
  have heval := congrArg (fun v => v.fst.val (-n)) he
  simpa only [x, weightedPairMode_fst, ite_true] using! heval.symm

end NLS.ZakharovShabat
