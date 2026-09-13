import NLS.ZakharovShabat.ResonantDeterminantAnalytic

/-!
# A potential supported at the two resonant frequencies

The negative component at `-2n` and positive component at `2n` preserve the
resonant two-dimensional space. Their complementary corrections vanish.
Consequently the actual determinant is the exact centered quadratic with
these amplitudes as off-diagonal entries.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A single signed resonant mode in each physical potential component. -/
def singleResonantPotential (w : SpectralWeight) (n : ℤ) (a b : ℂ) : WeightedCoeffPair w.toWeight p :=
  (WeightedCoeffPair.toMax w.toWeight p).symm
    (weightedMode w.toWeight (-(2*n)) a, weightedMode w.toWeight (2*n) b)

@[simp] theorem singleResonantPotential_fst (w : SpectralWeight) (n : ℤ) (a b : ℂ) (k : ℤ) :
    (singleResonantPotential (p := p) w n a b).fst.val k = if k = -(2*n) then a else 0 :=
  weightedMode_apply _ _ _ _

@[simp] theorem singleResonantPotential_snd (w : SpectralWeight) (n : ℤ) (a b : ℂ) (k : ℤ) :
    (singleResonantPotential (p := p) w n a b).snd.val k = if k = 2*n then b else 0 :=
  weightedMode_apply _ _ _ _

/-- The complementary free inverse annihilates both actual resonant potential sources. -/
theorem complementaryInverse_singleResonantSource (hp : p ≠ ⊤) (w : SpectralWeight)
    (n : ℤ) (a b z : ℂ) (hz : z ∈ resonantStrip n) (j : Fin 2) :
    complementaryFreeDomainInverse w.toWeight n z hz
      (weightedResonantSource hp w (singleResonantPotential w n a b) n j) = 0 := by
  fin_cases j
  · apply weightedPair_ext <;> intro k
    · simp
    · by_cases hk : k = n
      · simp [hk]
      · simp [show k+n ≠ 2*n by omega]
  · apply weightedPair_ext <;> intro k
    · by_cases hk : k = -n
      · simp [hk]
      · simp [show k-n ≠ -(2*n) by omega]
    · simp

/-- For a resonant potential, the full correction fixes each resonant potential source. -/
theorem correction_singleResonantSource (hp : p ≠ ⊤) (w : SpectralWeight)
    (n : ℤ) (a b z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w (singleResonantPotential w n a b) n z hz‖ < 1) (j : Fin 2) :
    weightedCorrectionExtension hp w (singleResonantPotential w n a b) n z
      (weightedResonantSource hp w (singleResonantPotential w n a b) n j) =
        weightedResonantSource hp w (singleResonantPotential w n a b) n j := by
  rw [weightedCorrectionExtension_eq hp w _ n z hz h]
  symm
  apply weightedCorrection_unique
  rw [← weightedDomainPotential_complementaryInverse,
    complementaryInverse_singleResonantSource, map_zero, sub_zero]

/-- The actual scalar determinant is the centered quadratic for this resonant mode family. -/
theorem resonantDeterminant_singleResonantPotential (hp : p ≠ ⊤) (w : SpectralWeight)
    (n : ℤ) (a b z : ℂ) (hz : z ∈ resonantStrip n)
    (h : ‖weightedPotentialSquareInShift hp w (singleResonantPotential w n a b) n z hz‖ < 1) :
    resonantDeterminantExtension hp w (singleResonantPotential w n a b) n z =
      (z-(Real.pi : ℂ)*n)^2-b*a := by
  simp [resonantDeterminantExtension, weightedResonantAExtension, weightedResonantBPlusExtension,
    weightedResonantBMinusExtension, weightedCorrectionEntryExtension,
    correction_singleResonantSource hp w n a b z hz h, show -n-n = -(2*n) by omega,
    show n+n = 2*n by omega]

/-- A unit-weight Fourier mode has exactly the modulus of its amplitude as norm. -/
theorem norm_weightedMode_one (k : ℤ) (a : ℂ) :
    ‖weightedMode (p := p) SpectralWeight.one.toWeight k a‖ = ‖a‖ := by
  simp [weightedMode, norm_smul, lp.norm_single (zero_lt_one.trans_le (show 1 ≤ p from Fact.out))]

/-- The Hilbert pair norm retains the energies of both resonant amplitudes. -/
theorem norm_singleResonantPotential_sq (n : ℤ) (a b : ℂ) :
    ‖singleResonantPotential (p := 2) SpectralWeight.one n a b‖^2 = ‖a‖^2+‖b‖^2 := by
  have h := norm_withLp_prod_rpow (p := 2) (by norm_num)
    (singleResonantPotential (p := 2) SpectralWeight.one n a b)
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  change ‖singleResonantPotential (p := 2) SpectralWeight.one n a b‖^2 =
    ‖weightedMode (p := 2) SpectralWeight.one.toWeight (-(2*n)) a‖^2 +
    ‖weightedMode (p := 2) SpectralWeight.one.toWeight (2*n) b‖^2 at h
  simpa only [norm_weightedMode_one] using h

end NLS.ZakharovShabat
