import NLS.ZakharovShabat.WeightedCorrection
import NLS.ZakharovShabat.WeightedDomainPotential

/-!
# Solving the Section 6 complementary Q-equation

The solution is `v=A_λ⁻¹ Q_n T̂_n Φu`. It belongs to the weighted derivative
domain and to the complementary subspace. The source identity
`Φv=T̂_n T_n Φu` and uniqueness are proved for the actual potential operator.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The domain-valued complementary solution, linear in the prescribed input `u`. -/
def weightedQSolution (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) :
    WeightedDomain w.toWeight p →L[ℂ] WeightedDomain w.toWeight p :=
  (complementaryFreeDomainInverse w.toWeight n z hz).comp
    ((weightedCorrection hp w φ n z hz h).comp (weightedDomainPotential hp w φ))

/-- The solution has zero resonant coordinates in the derivative domain. -/
theorem weightedQSolution_nonresonant (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) (u : WeightedDomain w.toWeight p) :
    complementaryProjection w.toWeight.oneDerivative n (weightedQSolution hp w φ n z hz h u) =
      weightedQSolution hp w φ n z hz h u := complementaryFreeDomainInverse_nonresonant _ _ _ _ _

/-- Multiplying the reconstructed complementary vector gives `T_n T̂_n Φu`. -/
theorem weightedQSolution_potential (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) (u : WeightedDomain w.toWeight p) :
    weightedDomainPotential hp w φ (weightedQSolution hp w φ n z hz h u) =
      weightedPotentialInverse hp w φ n z hz (weightedCorrection hp w φ n z hz h (weightedDomainPotential hp w φ u)) :=
  weightedDomainPotential_complementaryInverse _ _ _ _ _ _ _

/-- The source's displayed equation `Φv=T̂_n T_n Φu`. -/
theorem weightedQSolution_potential_source (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) (u : WeightedDomain w.toWeight p) :
    weightedDomainPotential hp w φ (weightedQSolution hp w φ n z hz h u) =
      weightedCorrection hp w φ n z hz h (weightedPotentialInverse hp w φ n z hz (weightedDomainPotential hp w φ u)) := by
  rw [weightedQSolution_potential, weightedCorrection_commute]

/-- The total potential is the corrected potential of the prescribed component. -/
theorem weightedQSolution_total_potential (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) (u : WeightedDomain w.toWeight p) :
    weightedDomainPotential hp w φ (u + weightedQSolution hp w φ n z hz h u) =
      weightedCorrection hp w φ n z hz h (weightedDomainPotential hp w φ u) := by
  rw [map_add, weightedQSolution_potential, weightedCorrection_expand]

/-- The reconstructed vector solves the original projected differential equation. -/
theorem weightedQSolution_equation (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) (u : WeightedDomain w.toWeight p) :
    weightedFreePencil w.toWeight z (weightedQSolution hp w φ n z hz h u) =
      complementaryProjection w.toWeight n (weightedDomainPotential hp w φ (u + weightedQSolution hp w φ n z hz h u)) := by
  rw [weightedQSolution_total_potential]
  exact pencil_complementaryFreeDomainInverse _ _ _ _ _

/-- Uniqueness holds in the actual complementary weighted derivative domain. -/
theorem weightedQSolution_unique (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w φ n z hz‖ < 1) (u v : WeightedDomain w.toWeight p)
    (hv : complementaryProjection w.toWeight.oneDerivative n v = v)
    (he : weightedFreePencil w.toWeight z v = complementaryProjection w.toWeight n (weightedDomainPotential hp w φ (u+v))) :
    v = weightedQSolution hp w φ n z hz h u := by
  have hvR := complementaryFreeDomainInverse_unique w.toWeight n z hz (weightedDomainPotential hp w φ (u+v)) v hv he
  have hPhi : weightedDomainPotential hp w φ v = weightedPotentialInverse hp w φ n z hz (weightedDomainPotential hp w φ (u+v)) := by
    calc
      _ = weightedDomainPotential hp w φ (complementaryFreeDomainInverse w.toWeight n z hz
          (weightedDomainPotential hp w φ (u+v))) := congrArg (weightedDomainPotential hp w φ) hvR
      _ = _ := weightedDomainPotential_complementaryInverse _ _ _ _ _ _ _
  have ha : weightedDomainPotential hp w φ (u+v) -
      weightedPotentialInverse hp w φ n z hz (weightedDomainPotential hp w φ (u+v)) = weightedDomainPotential hp w φ u := by
    rw [← hPhi, map_add, add_sub_cancel_right]
  have haC := weightedCorrection_unique hp w φ n z hz h _ _ ha
  calc
    v = complementaryFreeDomainInverse w.toWeight n z hz (weightedDomainPotential hp w φ (u+v)) := hvR
    _ = weightedQSolution hp w φ n z hz h u := by rw [haC]; rfl

/-- Existence and uniqueness of the Q-equation solution at every sufficiently large frequency,
uniformly for potentials in one neighborhood. -/
theorem exists_uniform_unique_weightedQSolution (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ n : ℤ, N ≤ n.natAbs → ∀ z : ℂ, z ∈ resonantStrip n →
        ∀ u : WeightedDomain w.toWeight p, ∃! v : WeightedDomain w.toWeight p,
          complementaryProjection w.toWeight.oneDerivative n v = v ∧
          weightedFreePencil w.toWeight z v = complementaryProjection w.toWeight n (weightedDomainPotential hp w ψ (u+v)) := by
  obtain ⟨N, hN, U, ho, hc, hφ, h0, _, hsmall⟩ := exists_uniform_complementarySquare_half hp w φ
  refine ⟨N, hN, U, ho, hc, hφ, h0, ?_⟩
  intro ψ hψ n hn z hz u
  have h : ‖weightedPotentialSquareInShift hp w ψ n z hz‖ < 1 :=
    ((hsmall ψ hψ n hn z hz).1).trans_lt (by norm_num)
  refine ⟨weightedQSolution hp w ψ n z hz h u,
    ⟨weightedQSolution_nonresonant hp w ψ n z hz h u, weightedQSolution_equation hp w ψ n z hz h u⟩, ?_⟩
  intro v hv
  exact weightedQSolution_unique hp w ψ n z hz h u v hv.1 hv.2

end NLS.ZakharovShabat
