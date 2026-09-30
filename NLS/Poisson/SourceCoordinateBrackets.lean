import NLS.Poisson.SourceBracket

/-! # Fourier coordinate brackets and the physical sign convention

Opposite component Fourier coefficients pair at opposite frequencies.
Their bracket is `-i`; same-component brackets vanish. These identities
check the sign and frequency reversal against the dissertation's physical
bilinear L² bracket, at every source exponent at least two.
-/

noncomputable section
open Complex
open scoped ENNReal
namespace NLS.Poisson
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceCoordinateLeft (n : ℤ) : CoeffPair p →L[ℂ] ℂ :=
  (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).comp
    ((ContinuousLinearMap.fst ℂ _ _).comp (CoeffPair.toMax p).toContinuousLinearMap)

def sourceCoordinateRight (n : ℤ) : CoeffPair p →L[ℂ] ℂ :=
  (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).comp
    ((ContinuousLinearMap.snd ℂ _ _).comp (CoeffPair.toMax p).toContinuousLinearMap)

@[simp] theorem sourceCoordinateLeft_apply (n : ℤ) (ψ : CoeffPair p) :
    sourceCoordinateLeft n ψ = ψ.fst n := rfl

@[simp] theorem sourceCoordinateRight_apply (n : ℤ) (ψ : CoeffPair p) :
    sourceCoordinateRight n ψ = ψ.snd n := rfl

theorem cotangentCoefficients_coordinateLeft (h2p : (2:ℝ≥0∞) ≤ p) (n : ℤ) :
    CoeffPair.cotangentCoefficients h2p (sourceCoordinateLeft n) = (lp.single 2 n 1,0) := by
  apply Prod.ext <;> ext k <;>
    simp [CoeffPair.cotangentCoefficients_fst,CoeffPair.cotangentCoefficients_snd,
      lp.single_apply,Pi.single_apply,eq_comm]

theorem cotangentCoefficients_coordinateRight (h2p : (2:ℝ≥0∞) ≤ p) (n : ℤ) :
    CoeffPair.cotangentCoefficients h2p (sourceCoordinateRight n) = (0,lp.single 2 n 1) := by
  apply Prod.ext <;> ext k <;>
    simp [CoeffPair.cotangentCoefficients_fst,CoeffPair.cotangentCoefficients_snd,
      lp.single_apply,Pi.single_apply,eq_comm]

theorem reflectedHilbertPairing_single_left (n : ℤ) (z : ℂ) (b : Coeff 2) :
    reflectedHilbertPairing (lp.single 2 n z) b = z*b (-n) := by
  classical
  rw [reflectedHilbertPairing_apply,tsum_eq_single n]
  · simp
  · intro k hk
    simp [lp.single_apply,hk]

theorem sourceBivector_coordinateLeft_coordinateRight (h2p : (2:ℝ≥0∞) ≤ p) (n m : ℤ) :
    sourceBivector h2p (sourceCoordinateLeft n) (sourceCoordinateRight m) =
      if n = -m then -I else 0 := by
  classical
  have he := congrArg₂ (fun a b : Coeff 2 × Coeff 2 => hilbertPairBivector a b)
    (cotangentCoefficients_coordinateLeft h2p n) (cotangentCoefficients_coordinateRight h2p m)
  change sourceBivector h2p (sourceCoordinateLeft n) (sourceCoordinateRight m) =
    hilbertPairBivector (lp.single 2 n 1,0) (0,lp.single 2 m 1) at he
  rw [he,hilbertPairBivector_apply]
  simp only [reflectedHilbertPairing_single_left,map_zero,
    sub_zero,one_mul]
  by_cases hnm : n = -m
  · simp [hnm]
  · have hne : -n ≠ m := by omega
    simp [lp.single_apply,hne,hnm]

@[simp] theorem sourceBivector_coordinateLeft_coordinateLeft (h2p : (2:ℝ≥0∞) ≤ p) (n m : ℤ) :
    sourceBivector h2p (sourceCoordinateLeft n) (sourceCoordinateLeft m) = 0 := by
  have he := congrArg₂ (fun a b : Coeff 2 × Coeff 2 => hilbertPairBivector a b)
    (cotangentCoefficients_coordinateLeft h2p n) (cotangentCoefficients_coordinateLeft h2p m)
  exact he.trans (by simp)

@[simp] theorem sourceBivector_coordinateRight_coordinateRight (h2p : (2:ℝ≥0∞) ≤ p) (n m : ℤ) :
    sourceBivector h2p (sourceCoordinateRight n) (sourceCoordinateRight m) = 0 := by
  have he := congrArg₂ (fun a b : Coeff 2 × Coeff 2 => hilbertPairBivector a b)
    (cotangentCoefficients_coordinateRight h2p n) (cotangentCoefficients_coordinateRight h2p m)
  exact he.trans (by simp)

/-- The bracket of coordinate functionals has the same physical sign and
opposite-frequency convention as the cotangent bivector. -/
theorem sourceBracket_coordinateLeft_coordinateRight (h2p : (2:ℝ≥0∞) ≤ p)
    (n m : ℤ) (ψ : CoeffPair p) :
    sourceBracket h2p (sourceCoordinateLeft n) (sourceCoordinateRight m) ψ =
      if n = -m then -I else 0 := by
  simp only [sourceBracket,ContinuousLinearMap.fderiv]
  exact sourceBivector_coordinateLeft_coordinateRight h2p n m

@[simp] theorem sourceBracket_coordinateLeft_coordinateLeft (h2p : (2:ℝ≥0∞) ≤ p)
    (n m : ℤ) (ψ : CoeffPair p) :
    sourceBracket h2p (sourceCoordinateLeft n) (sourceCoordinateLeft m) ψ = 0 := by
  simp [sourceBracket]

@[simp] theorem sourceBracket_coordinateRight_coordinateRight (h2p : (2:ℝ≥0∞) ≤ p)
    (n m : ℤ) (ψ : CoeffPair p) :
    sourceBracket h2p (sourceCoordinateRight n) (sourceCoordinateRight m) ψ = 0 := by
  simp [sourceBracket]

end NLS.Poisson
