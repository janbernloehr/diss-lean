import NLS.SequenceSpaces.FunctionOrZero
import NLS.ZakharovShabat.WeightedResonantDiagonalCenter
import NLS.ZakharovShabat.OffDiagonalSummability

/-!
# The actual spectral-center remainder as an `ℓᵖ` pair

At every distant diagonal center, subtract the signed leading Fourier
mode from the actual off-diagonal coefficient. Multiplication by
`w(2n)` expresses its weighted size in an ordinary `ℓᵖ` sequence. The
two components carry the original component-sum norm. The actual
full-strip estimates prove membership and the joint norm budget on
one open convex source neighborhood, for every larger cutoff.
-/

noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A weighted tail coordinate evaluated at the actual diagonal
center. `false` selects the negative coefficient and `true` the positive. -/
def weightedResonantCenterRemainderCoordinate (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) (positive : Bool) (n : ℤ) : ℂ :=
  if N ≤ n.natAbs then
    (w (2*n) : ℂ) *
      ((if positive then weightedResonantBPlusExtension hp w φ n
          (weightedResonantDiagonalCenter hp w φ n)
        else weightedResonantBMinusExtension hp w φ n
          (weightedResonantDiagonalCenter hp w φ n)) -
        if positive then φ.snd.val (2*n) else φ.fst.val (-(2*n)))
  else 0

/-- The pair of weighted actual center remainders, with zero fallback
outside sequence membership. The uniform theorem below rules that out. -/
def weightedResonantCenterRemainder (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) : CoeffPair p :=
  WithLp.toLp p
    (Coeff.ofFunctionOrZero p (weightedResonantCenterRemainderCoordinate hp w φ N false),
      Coeff.ofFunctionOrZero p (weightedResonantCenterRemainderCoordinate hp w φ N true))

/-- Membership identifies both components with their actual spectral
coordinates, including the identically zero block below the cutoff. -/
theorem weightedResonantCenterRemainder_apply_of_mem
    (hp : p ≠ ⊤) (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p) (N : ℕ)
    (hmem : ∀ positive : Bool,
      Memℓp (weightedResonantCenterRemainderCoordinate hp w φ N positive) p) (n : ℤ) :
    (weightedResonantCenterRemainder hp w φ N).fst n =
      weightedResonantCenterRemainderCoordinate hp w φ N false n ∧
    (weightedResonantCenterRemainder hp w φ N).snd n =
      weightedResonantCenterRemainderCoordinate hp w φ N true n :=
  ⟨Coeff.ofFunctionOrZero_apply_of_mem p _ (hmem false) n,
    Coeff.ofFunctionOrZero_apply_of_mem p _ (hmem true) n⟩

/-- Actual strip control and summability construct the full sequence
pair and retain the sum of the two actual remainder power tails. -/
theorem weightedResonantCenterRemainder_mem_and_norm_rpow_le
    (hp : p ≠ ⊤) (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p) (N : ℕ)
    (hcenter : ∀ n : ℤ, N ≤ n.natAbs → weightedResonantDiagonalCenter hp w φ n ∈ resonantStrip n)
    (hbound : ∀ n : ℤ, N ≤ n.natAbs → ∀ z ∈ resonantStrip n,
      w (2*n)*‖weightedResonantBMinusExtension hp w φ n z-φ.fst.val (-(2*n))‖ ≤
        resonantBMinusRemainderSup hp w φ n ∧
      w (2*n)*‖weightedResonantBPlusExtension hp w φ n z-φ.snd.val (2*n)‖ ≤
        resonantBPlusRemainderSup hp w φ n)
    (hsminus : Summable (fun n : ℤ => if N ≤ n.natAbs then
      (resonantBMinusRemainderSup hp w φ n)^p.toReal else 0))
    (hsplus : Summable (fun n : ℤ => if N ≤ n.natAbs then
      (resonantBPlusRemainderSup hp w φ n)^p.toReal else 0)) :
    (∀ positive : Bool, Memℓp (weightedResonantCenterRemainderCoordinate hp w φ N positive) p) ∧
    ‖weightedResonantCenterRemainder hp w φ N‖^p.toReal ≤
      (∑' n : ℤ, if N ≤ n.natAbs then (resonantBMinusRemainderSup hp w φ n)^p.toReal else 0) +
      (∑' n : ℤ, if N ≤ n.natAbs then (resonantBPlusRemainderSup hp w φ n)^p.toReal else 0) := by
  let M := fun (positive : Bool) (n : ℤ) => if N ≤ n.natAbs then
    ((if positive then resonantBPlusRemainderSup hp w φ n
      else resonantBMinusRemainderSup hp w φ n)^p.toReal) else 0
  have hs (positive : Bool) : Summable (M positive) := by
    cases positive
    · exact hsminus
    · exact hsplus
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos
    (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p))) hp
  have hdom (positive : Bool) (n : ℤ) :
      ‖weightedResonantCenterRemainderCoordinate hp w φ N positive n‖^p.toReal ≤ M positive n := by
    by_cases hn : N ≤ n.natAbs
    · have hpoint := hbound n hn _ (hcenter n hn)
      cases positive
      · simpa only [weightedResonantCenterRemainderCoordinate,M,if_pos hn,Bool.false_eq_true,if_false,
          norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (w.positive _)] using
          Real.rpow_le_rpow (mul_nonneg (w.positive _).le (norm_nonneg _)) hpoint.1 ENNReal.toReal_nonneg
      · simpa only [weightedResonantCenterRemainderCoordinate,M,if_pos hn,if_true,
          norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (w.positive _)] using
          Real.rpow_le_rpow (mul_nonneg (w.positive _).le (norm_nonneg _)) hpoint.2 ENNReal.toReal_nonneg
    · simp only [weightedResonantCenterRemainderCoordinate,M,if_neg hn,norm_zero,
        Real.zero_rpow hp0.ne',le_refl]
  refine ⟨fun positive => Coeff.memℓp_of_power_dominated _ (M positive) (hs positive) (hdom positive),?_⟩
  rw [norm_withLp_prod_rpow hp]
  exact add_le_add
    (Coeff.norm_ofFunctionOrZero_rpow_le hp _ (M false) (hs false) (hdom false))
    (Coeff.norm_ofFunctionOrZero_rpow_le hp _ (M true) (hs true) (hdom true))

/-- One neighborhood constructs the actual sequence map for every
larger cutoff and supplies its joint source-pair norm budget. -/
theorem exists_uniform_weightedResonantCenterRemainder_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ N : ℕ, N₀ ≤ N →
        (∀ positive : Bool, Memℓp (weightedResonantCenterRemainderCoordinate hp w ψ N positive) p) ∧
        ‖weightedResonantCenterRemainder hp w ψ N‖^p.toReal ≤
          offDiagonalSummationConstant p * ‖ψ‖^p.toReal *
            (‖ψ‖^(2*p.toReal)/(N : ℝ)^(min 1 (p.toReal-1)) +
              ‖weightedPairFourierTail w.toWeight (N/2) ψ‖^(2*p.toReal)) := by
  obtain ⟨N₁,hN₁,U₁,ho₁,hc₁,hφ₁,h0₁,h₁⟩ := exists_uniform_offDiagonalSup hp hp1 w φ
  obtain ⟨N₂,_,U₂,ho₂,hc₂,hφ₂,h0₂,h₂⟩ := exists_uniform_offDiagonalSummability hp hp1 w φ
  obtain ⟨N₃,_,U₃,ho₃,hc₃,hφ₃,h0₃,h₃⟩ := exists_uniform_weightedResonantDiagonalCenters hp hp1 w φ
  refine ⟨max N₁ (max N₂ N₃),hN₁.trans (le_max_left _ _),U₁ ∩ (U₂ ∩ U₃),
    ho₁.inter (ho₂.inter ho₃),hc₁.inter (hc₂.inter hc₃),⟨hφ₁,hφ₂,hφ₃⟩,⟨h0₁,h0₂,h0₃⟩,?_⟩
  intro ψ hψ N hN
  have hsup (n : ℤ) (hn : N ≤ n.natAbs) := h₁ ψ hψ.1 N (by omega) n hn
  have hsum := h₂ ψ hψ.2.1 N (by omega)
  obtain ⟨hmem,hbound⟩ := weightedResonantCenterRemainder_mem_and_norm_rpow_le hp w ψ N
    (fun n hn => refinedResonantDisk_subset_strip n (h₃ ψ hψ.2.2 n (by omega)).1.1)
    (fun n hn => (hsup n hn).2.2) hsum.1.1 hsum.2.1
  refine ⟨hmem,hbound.trans ?_⟩
  apply (add_le_add hsum.1.2 hsum.2.2).trans_eq
  rw [norm_withLp_prod_rpow hp ψ]
  ring

end NLS.ZakharovShabat
