import NLS.SequenceSpaces.SobolevPairCotangent

/-! # The physical Poisson bivector in signed Sobolev coordinates

The first signed component has reversed scalar Fourier frequency. Therefore
the printed physical -iJ pairing becomes a same-index cross-component sum
in signed coordinates. Reciprocal weights cancel and Hölder gives absolute
convergence for all conjugate Banach exponents, including either endpoint.
-/
noncomputable section
open scoped ENNReal
namespace NLS.Poisson
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

def sameIndexPairing (s : ℝ) : WeightedCoeff (Weight.sobolev s) p →L[ℂ]
    WeightedCoeff (Weight.sobolev (-s)) q →L[ℂ] ℂ :=
  (WeightedCoeff.sobolevBilinearPairing s).bilinearComp (ContinuousLinearMap.id ℂ _)
    (WeightedCoeff.reflection (-s)).toContinuousLinearEquiv.toContinuousLinearMap

theorem sameIndexPairing_apply (s : ℝ) (a : WeightedCoeff (Weight.sobolev s) p)
    (b : WeightedCoeff (Weight.sobolev (-s)) q) :
    sameIndexPairing s a b = ∑' n : ℤ, a.val n*b.val n := by
  change WeightedCoeff.sobolevBilinearPairing s a (WeightedCoeff.reflection (-s) b) = _
  simp only [WeightedCoeff.sobolevBilinearPairing_apply,WeightedCoeff.reflection_apply,neg_neg]

theorem norm_sameIndexPairing_le (s : ℝ) (a : WeightedCoeff (Weight.sobolev s) p)
    (b : WeightedCoeff (Weight.sobolev (-s)) q) :
    ‖sameIndexPairing s a b‖ ≤ ‖a‖*‖b‖ := by
  change ‖WeightedCoeff.sobolevBilinearPairing s a (WeightedCoeff.reflection (-s) b)‖ ≤ ‖a‖*‖b‖
  simpa only [LinearIsometryEquiv.norm_map] using
    WeightedCoeff.norm_sobolevBilinearPairing_le s a (WeightedCoeff.reflection (-s) b)

def signedBivector (s : ℝ) :
    (WeightedCoeff (Weight.sobolev s) p × WeightedCoeff (Weight.sobolev s) p) →L[ℂ]
      (WeightedCoeff (Weight.sobolev (-s)) q × WeightedCoeff (Weight.sobolev (-s)) q) →L[ℂ] ℂ :=
  (-Complex.I) • ((sameIndexPairing s).bilinearComp (ContinuousLinearMap.fst ℂ _ _) (ContinuousLinearMap.snd ℂ _ _) -
    (sameIndexPairing s).bilinearComp (ContinuousLinearMap.snd ℂ _ _) (ContinuousLinearMap.fst ℂ _ _))

theorem signedBivector_apply (s : ℝ)
    (a : WeightedCoeff (Weight.sobolev s) p × WeightedCoeff (Weight.sobolev s) p)
    (b : WeightedCoeff (Weight.sobolev (-s)) q × WeightedCoeff (Weight.sobolev (-s)) q) :
    signedBivector s a b = -Complex.I*(sameIndexPairing s a.1 b.2 - sameIndexPairing s a.2 b.1) := rfl

theorem signedBivector_physical (s : ℝ)
    (a : WeightedCoeff (Weight.sobolev s) p × WeightedCoeff (Weight.sobolev s) p)
    (b : WeightedCoeff (Weight.sobolev (-s)) q × WeightedCoeff (Weight.sobolev (-s)) q) :
    signedBivector s a b = -Complex.I*(
      WeightedCoeff.sobolevBilinearPairing s (WeightedCoeff.reflection s a.1) b.2 -
      WeightedCoeff.sobolevBilinearPairing s a.2 (WeightedCoeff.reflection (-s) b.1)) := by
  rw [signedBivector_apply]
  have he : WeightedCoeff.sobolevBilinearPairing s (WeightedCoeff.reflection s a.1) b.2 =
      sameIndexPairing s a.1 b.2 := by
    have h := WeightedCoeff.sobolevBilinearPairing_reflection s a.1 (WeightedCoeff.reflection (-s) b.2)
    change WeightedCoeff.sobolevBilinearPairing s (WeightedCoeff.reflection s a.1) b.2 =
      WeightedCoeff.sobolevBilinearPairing s a.1 (WeightedCoeff.reflection (-s) b.2)
    simpa only [WeightedCoeff.reflection_reflection] using h
  rw [he]
  rfl

def negNegIsometry (s : ℝ) :
    WeightedCoeff (Weight.sobolev (-(-s))) p ≃ₗᵢ[ℂ] WeightedCoeff (Weight.sobolev s) p :=
  (WeightedCoeff.weightIsometry (Weight.sobolev (-(-s))) p).trans
    (WeightedCoeff.weightIsometry (Weight.sobolev s) p).symm

theorem negNegIsometry_val (s : ℝ) (a : WeightedCoeff (Weight.sobolev (-(-s))) p) (n : ℤ) :
    (negNegIsometry s a).val n = a.val n := by
  change ((Weight.sobolev (-(-s)) n : ℂ)*a.val n)/(Weight.sobolev s n : ℂ) = a.val n
  simp only [neg_neg]
  exact mul_div_cancel_left₀ _ (Weight.complex_ne_zero _ _)

theorem norm_signedBivector_le (s : ℝ)
    (a : WeightedCoeff (Weight.sobolev s) p × WeightedCoeff (Weight.sobolev s) p)
    (b : WeightedCoeff (Weight.sobolev (-s)) q × WeightedCoeff (Weight.sobolev (-s)) q) :
    ‖signedBivector s a b‖ ≤ 2*‖a‖*‖b‖ := by
  rw [signedBivector_apply,norm_mul]
  simp only [norm_neg,Complex.norm_I,one_mul]
  calc
    _ ≤ ‖sameIndexPairing s a.1 b.2‖ + ‖sameIndexPairing s a.2 b.1‖ := norm_sub_le _ _
    _ ≤ ‖a.1‖*‖b.2‖+‖a.2‖*‖b.1‖ := add_le_add (norm_sameIndexPairing_le s _ _) (norm_sameIndexPairing_le s _ _)
    _ ≤ ‖a‖*‖b‖+‖a‖*‖b‖ := by
      gcongr
      · exact norm_fst_le a
      · exact norm_snd_le b
      · exact norm_snd_le a
      · exact norm_fst_le b
    _ = _ := by ring

def negNegComponents (s : ℝ) :
    (WeightedCoeff (Weight.sobolev (-(-s))) p × WeightedCoeff (Weight.sobolev (-(-s))) p) →L[ℂ]
      (WeightedCoeff (Weight.sobolev s) p × WeightedCoeff (Weight.sobolev s) p) :=
  (negNegIsometry s).toContinuousLinearEquiv.toContinuousLinearMap.prodMap
    (negNegIsometry s).toContinuousLinearEquiv.toContinuousLinearMap

theorem norm_negNegComponents (s : ℝ)
    (a : WeightedCoeff (Weight.sobolev (-(-s))) p × WeightedCoeff (Weight.sobolev (-(-s))) p) :
    ‖negNegComponents s a‖ = ‖a‖ := by
  change max ‖negNegIsometry s a.1‖ ‖negNegIsometry s a.2‖ = max ‖a.1‖ ‖a.2‖
  simp only [LinearIsometryEquiv.norm_map]

theorem summable_sameIndex (s : ℝ) (a : WeightedCoeff (Weight.sobolev s) p)
    (b : WeightedCoeff (Weight.sobolev (-s)) q) :
    Summable (fun n : ℤ => ‖a.val n*b.val n‖) := by
  simpa only [WeightedCoeff.reflection_apply,neg_neg] using
    WeightedCoeff.summable_norm_sobolevBilinearPairing s a (WeightedCoeff.reflection (-s) b)

theorem signedBivector_eq_tsum (s : ℝ)
    (a : WeightedCoeff (Weight.sobolev s) p × WeightedCoeff (Weight.sobolev s) p)
    (b : WeightedCoeff (Weight.sobolev (-s)) q × WeightedCoeff (Weight.sobolev (-s)) q) :
    signedBivector s a b = -Complex.I * ∑' n : ℤ,
      (a.1.val n*b.2.val n-a.2.val n*b.1.val n) := by
  rw [signedBivector_apply,sameIndexPairing_apply,sameIndexPairing_apply,
    ← (summable_sameIndex s a.1 b.2).of_norm.tsum_sub (summable_sameIndex s a.2 b.1).of_norm]

theorem summable_signed_cross (s : ℝ)
    (a : WeightedCoeff (Weight.sobolev s) p × WeightedCoeff (Weight.sobolev s) p)
    (b : WeightedCoeff (Weight.sobolev (-s)) q × WeightedCoeff (Weight.sobolev (-s)) q) :
    Summable (fun n : ℤ => ‖a.1.val n*b.2.val n-a.2.val n*b.1.val n‖) :=
  ((summable_sameIndex s a.1 b.2).of_norm.sub (summable_sameIndex s a.2 b.1).of_norm).norm


/-- The printed physical matrix J in the signed coefficient basis. -/
def signedJ (s : ℝ) :
    (WeightedCoeff (Weight.sobolev s) p × WeightedCoeff (Weight.sobolev s) p) →L[ℂ]
      (WeightedCoeff (Weight.sobolev s) p × WeightedCoeff (Weight.sobolev s) p) :=
  (((WeightedCoeff.reflection (p := p) s).toContinuousLinearEquiv.toContinuousLinearMap).comp
    (ContinuousLinearMap.snd ℂ (WeightedCoeff (Weight.sobolev s) p) (WeightedCoeff (Weight.sobolev s) p))).prod
  (-((WeightedCoeff.reflection (p := p) s).toContinuousLinearEquiv.toContinuousLinearMap).comp
    (ContinuousLinearMap.fst ℂ (WeightedCoeff (Weight.sobolev s) p) (WeightedCoeff (Weight.sobolev s) p)))

@[simp] theorem signedJ_apply (s : ℝ)
    (b : WeightedCoeff (Weight.sobolev s) p × WeightedCoeff (Weight.sobolev s) p) :
    signedJ s b = (WeightedCoeff.reflection s b.2,-WeightedCoeff.reflection s b.1) := rfl

/-- In scalar Fourier coordinates J sends (u-,u+) to (u+,-u-), with no extra sign. -/
theorem signedJ_physical (s : ℝ)
    (b : WeightedCoeff (Weight.sobolev s) p × WeightedCoeff (Weight.sobolev s) p) :
    (WeightedCoeff.reflection s (signedJ s b).1,(signedJ s b).2) =
      (b.2,-WeightedCoeff.reflection s b.1) := by
  simp only [signedJ_apply,WeightedCoeff.reflection_reflection]

/-- The stated bivector is exactly -i times the corrected physical pairing with J. -/
theorem signedBivector_eq_pairing_J (s : ℝ)
    (a : WeightedCoeff (Weight.sobolev s) p × WeightedCoeff (Weight.sobolev s) p)
    (b : WeightedCoeff (Weight.sobolev (-s)) q × WeightedCoeff (Weight.sobolev (-s)) q) :
    signedBivector s a b = -Complex.I *
      (WeightedCoeff.sobolevBilinearPairing s a.1 (signedJ (-s) b).1 +
        WeightedCoeff.sobolevBilinearPairing s a.2 (signedJ (-s) b).2) := by
  rw [signedBivector_apply]
  change -Complex.I*(WeightedCoeff.sobolevBilinearPairing s a.1 (WeightedCoeff.reflection (-s) b.2) -
    WeightedCoeff.sobolevBilinearPairing s a.2 (WeightedCoeff.reflection (-s) b.1)) = _
  simp only [signedJ_apply,map_neg,sub_eq_add_neg]

@[simp] theorem negNegIsometry_symm_val (s : ℝ)
    (a : WeightedCoeff (Weight.sobolev s) p) (n : ℤ) :
    ((negNegIsometry s).symm a).val n = a.val n := by
  have h := negNegIsometry_val s ((negNegIsometry s).symm a) n
  simpa only [LinearIsometryEquiv.apply_symm_apply] using h.symm

/-- Symmetry of scalar coefficient duality after its required order transport. -/
theorem sameIndexPairing_comm (s : ℝ) (a : WeightedCoeff (Weight.sobolev s) p)
    (b : WeightedCoeff (Weight.sobolev (-s)) q) :
    sameIndexPairing (-s) b ((negNegIsometry s).symm a) = sameIndexPairing s a b := by
  simp only [sameIndexPairing_apply,negNegIsometry_symm_val]
  exact tsum_congr (fun n => mul_comm _ _)

/-- Antisymmetry retains every raw coefficient while exchanging opposite Sobolev orders. -/
theorem signedBivector_antisymm (s : ℝ)
    (a : WeightedCoeff (Weight.sobolev s) p × WeightedCoeff (Weight.sobolev s) p)
    (b : WeightedCoeff (Weight.sobolev (-s)) q × WeightedCoeff (Weight.sobolev (-s)) q) :
    signedBivector s a b = -signedBivector (-s) b
      ((negNegIsometry s).symm a.1,(negNegIsometry s).symm a.2) := by
  simp only [signedBivector_apply,sameIndexPairing_comm]
  ring

@[simp] theorem negNegComponents_fst_val (s : ℝ)
    (a : WeightedCoeff (Weight.sobolev (-(-s))) p × WeightedCoeff (Weight.sobolev (-(-s))) p) (n : ℤ) :
    (negNegComponents s a).1.val n = a.1.val n := negNegIsometry_val s a.1 n

@[simp] theorem negNegComponents_snd_val (s : ℝ)
    (a : WeightedCoeff (Weight.sobolev (-(-s))) p × WeightedCoeff (Weight.sobolev (-(-s))) p) (n : ℤ) :
    (negNegComponents s a).2.val n = a.2.val n := negNegIsometry_val s a.2 n

end NLS.Poisson
