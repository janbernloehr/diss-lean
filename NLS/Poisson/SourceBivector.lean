import NLS.SequenceSpaces.SourceCotangent
import NLS.SequenceSpaces.Reflection

/-! # The dissertation's source Poisson bivector

The Fourier form of the bilinear physical L² pairing reverses the
frequency in its second factor. Restricting source cotangents to Hilbert
directions gives absolutely convergent cross-component pairings for
every exponent at least two. Their difference, multiplied by `-i`, is
the dissertation's canonical Poisson bivector, continuously bilinear
in the two cotangents.
-/

noncomputable section
open Complex
open scoped ENNReal
namespace NLS.Poisson

def reflectedHilbertPairing : Coeff 2 →L[ℂ] Coeff 2 →L[ℂ] ℂ :=
  (Coeff.dualPairing (p := 2) (q := 2)).bilinearComp
    (ContinuousLinearMap.id ℂ (Coeff 2)) Coeff.reflection.toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem reflectedHilbertPairing_apply (a b : Coeff 2) :
    reflectedHilbertPairing a b = ∑' n : ℤ, a n*b (-n) := rfl

theorem summable_norm_reflectedHilbertPairing (a b : Coeff 2) :
    Summable (fun n : ℤ => ‖a n*b (-n)‖) :=
  Coeff.summable_norm_dualPairing a (Coeff.reflection b)

theorem reflectedHilbertPairing_comm (a b : Coeff 2) :
    reflectedHilbertPairing a b = reflectedHilbertPairing b a := by
  rw [reflectedHilbertPairing_apply,reflectedHilbertPairing_apply,
    ← (Equiv.neg ℤ).tsum_eq (fun n : ℤ => b n*a (-n))]
  apply tsum_congr
  intro n
  simp only [Equiv.neg_apply,neg_neg]
  exact mul_comm _ _

theorem norm_reflectedHilbertPairing_le (a b : Coeff 2) :
    ‖reflectedHilbertPairing a b‖ ≤ ‖a‖*‖b‖ := by
  rw [reflectedHilbertPairing_apply]
  have h := Coeff.norm_dualPairing_le a (Coeff.reflection b)
  rw [Coeff.dualPairing_apply] at h
  simpa only [Coeff.reflection_apply,Coeff.reflection.norm_map] using h

def hilbertPairBivector : (Coeff 2 × Coeff 2) →L[ℂ] (Coeff 2 × Coeff 2) →L[ℂ] ℂ :=
  (-I) • (reflectedHilbertPairing.bilinearComp
    (ContinuousLinearMap.fst ℂ _ _) (ContinuousLinearMap.snd ℂ _ _)-
    reflectedHilbertPairing.bilinearComp
      (ContinuousLinearMap.snd ℂ _ _) (ContinuousLinearMap.fst ℂ _ _))

@[simp] theorem hilbertPairBivector_apply (a b : Coeff 2 × Coeff 2) :
    hilbertPairBivector a b = -I*(reflectedHilbertPairing a.1 b.2-reflectedHilbertPairing a.2 b.1) := rfl

theorem hilbertPairBivector_antisymm (a b : Coeff 2 × Coeff 2) :
    hilbertPairBivector a b = -hilbertPairBivector b a := by
  simp only [hilbertPairBivector_apply]
  rw [reflectedHilbertPairing_comm b.1 a.2,reflectedHilbertPairing_comm b.2 a.1]
  ring

@[simp] theorem hilbertPairBivector_self (a : Coeff 2 × Coeff 2) : hilbertPairBivector a a = 0 := by
  simp [reflectedHilbertPairing_comm a.1 a.2]

theorem norm_hilbertPairBivector_le (a b : Coeff 2 × Coeff 2) :
    ‖hilbertPairBivector a b‖ ≤ 2*‖a‖*‖b‖ := by
  rw [hilbertPairBivector_apply,norm_mul]
  simp only [norm_neg,norm_I,one_mul]
  calc
    _ ≤ ‖reflectedHilbertPairing a.1 b.2‖+‖reflectedHilbertPairing a.2 b.1‖ := norm_sub_le _ _
    _ ≤ ‖a.1‖*‖b.2‖+‖a.2‖*‖b.1‖ := add_le_add (norm_reflectedHilbertPairing_le _ _) (norm_reflectedHilbertPairing_le _ _)
    _ ≤ ‖a‖*‖b‖+‖a‖*‖b‖ := by
      gcongr
      · exact norm_fst_le a
      · exact norm_snd_le b
      · exact norm_snd_le a
      · exact norm_fst_le b
    _ = _ := by ring

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceBivector (h2p : (2:ℝ≥0∞) ≤ p) :
    (CoeffPair p →L[ℂ] ℂ) →L[ℂ] (CoeffPair p →L[ℂ] ℂ) →L[ℂ] ℂ :=
  hilbertPairBivector.bilinearComp (CoeffPair.cotangentCoefficients h2p) (CoeffPair.cotangentCoefficients h2p)

theorem sourceBivector_antisymm (h2p : (2:ℝ≥0∞) ≤ p) (L M : CoeffPair p →L[ℂ] ℂ) :
    sourceBivector h2p L M = -sourceBivector h2p M L :=
  hilbertPairBivector_antisymm _ _

@[simp] theorem sourceBivector_self (h2p : (2:ℝ≥0∞) ≤ p) (L : CoeffPair p →L[ℂ] ℂ) :
    sourceBivector h2p L L = 0 := hilbertPairBivector_self _

theorem norm_sourceBivector_le (h2p : (2:ℝ≥0∞) ≤ p) (L M : CoeffPair p →L[ℂ] ℂ) :
    ‖sourceBivector h2p L M‖ ≤ 2*‖L‖*‖M‖ :=
  (norm_hilbertPairBivector_le _ _).trans (by
    gcongr <;> apply CoeffPair.norm_cotangentCoefficients_le)

/-- The literal Fourier formula has an absolutely convergent sum. -/
theorem sourceBivector_eq_tsum (h2p : (2:ℝ≥0∞) ≤ p) (L M : CoeffPair p →L[ℂ] ℂ) :
    sourceBivector h2p L M = -I*∑' n : ℤ,
      (L (CoeffPair.inlCLM (lp.single p n 1))*M (CoeffPair.inrCLM (lp.single p (-n) 1))-
        L (CoeffPair.inrCLM (lp.single p n 1))*M (CoeffPair.inlCLM (lp.single p (-n) 1))) := by
  let a := CoeffPair.cotangentCoefficients h2p L
  let b := CoeffPair.cotangentCoefficients h2p M
  change -I*(reflectedHilbertPairing a.1 b.2-reflectedHilbertPairing a.2 b.1) = _
  rw [reflectedHilbertPairing_apply,reflectedHilbertPairing_apply,
    ← (summable_norm_reflectedHilbertPairing a.1 b.2).of_norm.tsum_sub
      (summable_norm_reflectedHilbertPairing a.2 b.1).of_norm]
  simp only [a,b,CoeffPair.cotangentCoefficients_fst,CoeffPair.cotangentCoefficients_snd]

theorem sourceBivector_summable_norm (h2p : (2:ℝ≥0∞) ≤ p) (L M : CoeffPair p →L[ℂ] ℂ) :
    Summable (fun n : ℤ => ‖L (CoeffPair.inlCLM (lp.single p n 1))*
        M (CoeffPair.inrCLM (lp.single p (-n) 1))-
      L (CoeffPair.inrCLM (lp.single p n 1))*M (CoeffPair.inlCLM (lp.single p (-n) 1))‖) := by
  have h := ((summable_norm_reflectedHilbertPairing (CoeffPair.cotangentCoefficients h2p L).1
    (CoeffPair.cotangentCoefficients h2p M).2).of_norm.sub
      (summable_norm_reflectedHilbertPairing (CoeffPair.cotangentCoefficients h2p L).2
        (CoeffPair.cotangentCoefficients h2p M).1).of_norm).norm
  simpa only [CoeffPair.cotangentCoefficients_fst,CoeffPair.cotangentCoefficients_snd] using h

variable {q : ℝ≥0∞} [Fact (1 ≤ q)]

theorem cotangentCoefficients_restrict_exponent
    (h2p : (2:ℝ≥0∞) ≤ p) (hpq : p ≤ q) (L : CoeffPair q →L[ℂ] ℂ) :
    CoeffPair.cotangentCoefficients h2p (L.comp (CoeffPair.exponentInclusion hpq)) =
      CoeffPair.cotangentCoefficients (h2p.trans hpq) L := by
  apply Prod.ext <;> ext n <;>
    simp only [CoeffPair.cotangentCoefficients_fst,CoeffPair.cotangentCoefficients_snd,
      ContinuousLinearMap.comp_apply] <;> rfl

/-- Restriction to a smaller exponent preserves the physical Poisson
pairing. In particular this compares every `p ≥ 2` with `p = 2`. -/
theorem sourceBivector_restrict_exponent
    (h2p : (2:ℝ≥0∞) ≤ p) (hpq : p ≤ q) (L M : CoeffPair q →L[ℂ] ℂ) :
    sourceBivector h2p (L.comp (CoeffPair.exponentInclusion hpq))
      (M.comp (CoeffPair.exponentInclusion hpq)) = sourceBivector (h2p.trans hpq) L M := by
  change hilbertPairBivector _ _ = hilbertPairBivector _ _
  exact congrArg₂ (fun a b : Coeff 2 × Coeff 2 => hilbertPairBivector a b)
    (cotangentCoefficients_restrict_exponent h2p hpq L)
    (cotangentCoefficients_restrict_exponent h2p hpq M)

end NLS.Poisson
