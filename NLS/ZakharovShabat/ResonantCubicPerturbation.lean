import NLS.ZakharovShabat.ResonantCubicTail

/-! # Exact mixed cubic expansion and full-strip perturbation bounds

These estimates support the unresolved final weighted gap sum on dissertation
p.44. They do not prove the actual counted-root gap asymptotics.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The total complementary potential extension is additive in its potential. -/
theorem weightedPotentialExtension_add (hp : p ≠ ⊤) (w : SpectralWeight)
    (A B : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) :
    weightedPotentialExtension hp w (A+B) n z =
      weightedPotentialExtension hp w A n z + weightedPotentialExtension hp w B n z := by
  change (weightedDomainPotentialCLM hp w (A+B)).comp _ =
    (weightedDomainPotentialCLM hp w A).comp _ + (weightedDomainPotentialCLM hp w B).comp _
  rw [map_add,ContinuousLinearMap.add_comp]

/-- The total extension is complex homogeneous in its potential. -/
theorem weightedPotentialExtension_smul (hp : p ≠ ⊤) (w : SpectralWeight)
    (A : WeightedCoeffPair w.toWeight p) (c : ℂ) (n : ℤ) (z : ℂ) :
    weightedPotentialExtension hp w (c • A) n z = c • weightedPotentialExtension hp w A n z := by
  change (weightedDomainPotentialCLM hp w (c • A)).comp _ =
    c • (weightedDomainPotentialCLM hp w A).comp _
  rw [map_smul,ContinuousLinearMap.smul_comp]

/-- The actual resonant source is additive in its potential. -/
theorem weightedResonantSource_add (hp : p ≠ ⊤) (w : SpectralWeight)
    (A B : WeightedCoeffPair w.toWeight p) (n : ℤ) (j : Fin 2) :
    weightedResonantSource hp w (A+B) n j =
      weightedResonantSource hp w A n j + weightedResonantSource hp w B n j := by
  change (weightedDomainPotentialCLM hp w (A+B)) _ =
    (weightedDomainPotentialCLM hp w A) _ + (weightedDomainPotentialCLM hp w B) _
  rw [map_add,add_apply]

/-- The actual resonant source is complex homogeneous. -/
theorem weightedResonantSource_smul (hp : p ≠ ⊤) (w : SpectralWeight)
    (A : WeightedCoeffPair w.toWeight p) (c : ℂ) (n : ℤ) (j : Fin 2) :
    weightedResonantSource hp w (c • A) n j = c • weightedResonantSource hp w A n j := by
  change (weightedDomainPotentialCLM hp w (c • A)) _ = c • (weightedDomainPotentialCLM hp w A) _
  rw [map_smul,smul_apply]

/-- An ordered mixed cubic term of the actual operator series. -/
def resonantMixedCubic (hp : p ≠ ⊤) (w : SpectralWeight)
    (A B C : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (i j : Fin 2) : ℂ :=
  resonantCoordinates w.toWeight n (weightedPotentialExtension hp w A n z
    (weightedPotentialExtension hp w B n z (weightedResonantSource hp w C n j))) i

/-- The first cubic parity term is the corresponding repeated mixed term. -/
theorem resonantCubic_eq_mixed (hp : p ≠ ⊤) (w : SpectralWeight)
    (A : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (i j : Fin 2) :
    weightedResonantParityTermFunction hp w A n 2 0 i j z = resonantMixedCubic hp w A A A n z i j := by
  simp only [weightedResonantParityTermFunction,resonantMixedCubic,pow_zero,pow_two,
    one_apply_eq_self,mul_apply_eq_comp]

/-- The exact cubic expansion of s*A+s^3*B has degrees 3, 5, 7 and 9. -/
theorem resonantCubic_polynomial (hp : p ≠ ⊤) (w : SpectralWeight)
    (A B : WeightedCoeffPair w.toWeight p) (n : ℤ) (z s : ℂ) (i j : Fin 2) :
    weightedResonantParityTermFunction hp w (s • A + s^3 • B) n 2 0 i j z =
      s^3 * resonantMixedCubic hp w A A A n z i j +
      s^5 * (resonantMixedCubic hp w B A A n z i j + resonantMixedCubic hp w A B A n z i j +
        resonantMixedCubic hp w A A B n z i j) +
      s^7 * (resonantMixedCubic hp w B B A n z i j + resonantMixedCubic hp w B A B n z i j +
        resonantMixedCubic hp w A B B n z i j) +
      s^9 * resonantMixedCubic hp w B B B n z i j := by
  rw [resonantCubic_eq_mixed]
  simp only [resonantMixedCubic,weightedPotentialExtension_add,weightedPotentialExtension_smul,weightedResonantSource_add,weightedResonantSource_smul,
    add_apply,smul_apply,map_add,map_smul,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  ring

/-- A bound for a mixed cubic term, independent of the point in the strip. -/
def resonantMixedCubicBound (hp : p ≠ ⊤) (w : SpectralWeight)
    (A B C : WeightedCoeffPair w.toWeight p) (n : ℤ) (j : Fin 2) : ℝ :=
  (Coeff.complementaryConstant p hp * ‖A‖) *
    ((Coeff.complementaryConstant p hp * ‖B‖) * ‖weightedResonantSource hp w C n j‖)

/-- The mixed-term majorant is nonnegative. -/
theorem resonantMixedCubicBound_nonneg (hp : p ≠ ⊤) (w : SpectralWeight)
    (A B C : WeightedCoeffPair w.toWeight p) (n : ℤ) (j : Fin 2) :
    0 ≤ resonantMixedCubicBound hp w A B C n j := by
  have h := Coeff.complementaryConstant_nonneg p hp
  unfold resonantMixedCubicBound
  positivity

/-- The same mixed-term bound holds on the whole closed strip. -/
theorem resonantMixedCubic_norm_le (hp : p ≠ ⊤) (w : SpectralWeight)
    (A B C : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ)
    (hz : z ∈ resonantStrip n) (i j : Fin 2) :
    ‖resonantMixedCubic hp w A B C n z i j‖ ≤ resonantMixedCubicBound hp w A B C n j := by
  unfold resonantMixedCubic
  rw [weightedPotentialExtension_eq hp w A n z hz,weightedPotentialExtension_eq hp w B n z hz]
  have hc := weighted_resonantCoordinate_le_shifted w n 0
    (weightedPotentialInverse hp w A n z hz
      (weightedPotentialInverse hp w B n z hz (weightedResonantSource hp w C n j))) i
  simp only [add_zero,SpectralWeight.shiftedPairNorm_zero] at hc
  apply (le_mul_of_one_le_left (norm_nonneg _) (w.one_le n)).trans hc |>.trans
  apply (norm_weightedPotentialInverse_apply_le hp w A n z hz _).trans
  exact mul_le_mul_of_nonneg_left (norm_weightedPotentialInverse_apply_le hp w B n z hz _)
    (mul_nonneg (Coeff.complementaryConstant_nonneg p hp) (norm_nonneg _))

/-- The seven higher mixed-term bounds in the cubic perturbation. -/
def resonantCubicPerturbationBound (hp : p ≠ ⊤) (w : SpectralWeight)
    (A B : WeightedCoeffPair w.toWeight p) (n : ℤ) (j : Fin 2) : ℝ :=
  (resonantMixedCubicBound hp w B A A n j + resonantMixedCubicBound hp w A B A n j + resonantMixedCubicBound hp w A A B n j) +
  (resonantMixedCubicBound hp w B B A n j + resonantMixedCubicBound hp w B A B n j + resonantMixedCubicBound hp w A B B n j) +
  resonantMixedCubicBound hp w B B B n j

private theorem cubicPerturbation_norm_three_add (x y z : ℂ) : ‖x+y+z‖ ≤ ‖x‖+‖y‖+‖z‖ :=
  (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)

/-- The cubic change is bounded by norm(s)^5 on every full strip for norm(s)<=1. -/
theorem resonantCubicPerturbation_norm_le (hp : p ≠ ⊤) (w : SpectralWeight)
    (A B : WeightedCoeffPair w.toWeight p) (n : ℤ) (z s : ℂ)
    (hz : z ∈ resonantStrip n) (hs : ‖s‖ ≤ 1) (i j : Fin 2) :
    ‖weightedResonantParityTermFunction hp w (s • A + s^3 • B) n 2 0 i j z -
      s^3 * resonantMixedCubic hp w A A A n z i j‖ ≤
        ‖s‖^5 * resonantCubicPerturbationBound hp w A B n j := by
  let U := resonantMixedCubic hp w B A A n z i j + resonantMixedCubic hp w A B A n z i j + resonantMixedCubic hp w A A B n z i j
  let V := resonantMixedCubic hp w B B A n z i j + resonantMixedCubic hp w B A B n z i j + resonantMixedCubic hp w A B B n z i j
  let W := resonantMixedCubic hp w B B B n z i j
  let u := resonantMixedCubicBound hp w B A A n j + resonantMixedCubicBound hp w A B A n j + resonantMixedCubicBound hp w A A B n j
  let v := resonantMixedCubicBound hp w B B A n j + resonantMixedCubicBound hp w B A B n j + resonantMixedCubicBound hp w A B B n j
  let b := resonantMixedCubicBound hp w B B B n j
  have hU : ‖U‖ ≤ u := (cubicPerturbation_norm_three_add _ _ _).trans
    (add_le_add (add_le_add (resonantMixedCubic_norm_le hp w B A A n z hz i j)
      (resonantMixedCubic_norm_le hp w A B A n z hz i j)) (resonantMixedCubic_norm_le hp w A A B n z hz i j))
  have hV : ‖V‖ ≤ v := (cubicPerturbation_norm_three_add _ _ _).trans
    (add_le_add (add_le_add (resonantMixedCubic_norm_le hp w B B A n z hz i j)
      (resonantMixedCubic_norm_le hp w B A B n z hz i j)) (resonantMixedCubic_norm_le hp w A B B n z hz i j))
  have hW : ‖W‖ ≤ b := resonantMixedCubic_norm_le hp w B B B n z hz i j
  have hv : 0 ≤ v := (norm_nonneg _).trans hV
  have hb : 0 ≤ b := (norm_nonneg _).trans hW
  have h7 : ‖s‖^7 ≤ ‖s‖^5 := pow_le_pow_of_le_one (norm_nonneg _) hs (by norm_num)
  have h9 : ‖s‖^9 ≤ ‖s‖^5 := pow_le_pow_of_le_one (norm_nonneg _) hs (by norm_num)
  rw [resonantCubic_polynomial]
  change ‖(s^3 * resonantMixedCubic hp w A A A n z i j + s^5*U + s^7*V + s^9*W) -
    s^3 * resonantMixedCubic hp w A A A n z i j‖ ≤ _
  rw [show (s^3 * resonantMixedCubic hp w A A A n z i j + s^5*U + s^7*V + s^9*W) -
    s^3 * resonantMixedCubic hp w A A A n z i j = s^5*U+s^7*V+s^9*W by ring]
  apply (cubicPerturbation_norm_three_add _ _ _).trans
  simp only [norm_mul,norm_pow]
  calc
    _ ≤ ‖s‖^5*u+‖s‖^7*v+‖s‖^9*b := by gcongr
    _ ≤ ‖s‖^5*u+‖s‖^5*v+‖s‖^5*b :=
      add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_right h7 hv))
        (mul_le_mul_of_nonneg_right h9 hb)
    _ = _ := by change _ = ‖s‖^5*(u+v+b); ring

/-- Scaling a potential scales its cubic term by the third power. -/
theorem resonantCubic_homogeneous (hp : p ≠ ⊤) (w : SpectralWeight)
    (A : WeightedCoeffPair w.toWeight p) (n : ℤ) (z s : ℂ) (i j : Fin 2) :
    weightedResonantParityTermFunction hp w (s • A) n 2 0 i j z =
      s^3 * resonantMixedCubic hp w A A A n z i j := by
  rw [resonantCubic_eq_mixed]
  simp only [resonantMixedCubic,weightedPotentialExtension_smul,weightedResonantSource_smul,smul_apply,map_smul,
    Pi.smul_apply,smul_eq_mul]
  ring

/-- The actual weighted full-strip supremum of the cubic perturbation. -/
def resonantCubicPerturbationSup (hp : p ≠ ⊤) (w : SpectralWeight)
    (A B : WeightedCoeffPair w.toWeight p) (n : ℤ) (s : ℂ) (i j : Fin 2) : ℝ :=
  weightedStripSup w n (fun z =>
    weightedResonantParityTermFunction hp w (s • A+s^3 • B) n 2 0 i j z -
      weightedResonantParityTermFunction hp w (s • A) n 2 0 i j z)

/-- The cubic perturbation supremum is nonnegative and has a fifth-order bound. -/
theorem resonantCubicPerturbationSup_bounds (hp : p ≠ ⊤) (w : SpectralWeight)
    (A B : WeightedCoeffPair w.toWeight p) (n : ℤ) (s : ℂ) (hs : ‖s‖ ≤ 1) (i j : Fin 2) :
    0 ≤ resonantCubicPerturbationSup hp w A B n s i j ∧
    resonantCubicPerturbationSup hp w A B n s i j ≤ w (2*n)*‖s‖^5*resonantCubicPerturbationBound hp w A B n j := by
  have h := weightedStripSup_bounds w n
    (fun z => weightedResonantParityTermFunction hp w (s • A+s^3 • B) n 2 0 i j z -
      weightedResonantParityTermFunction hp w (s • A) n 2 0 i j z)
    (w (2*n)*‖s‖^5*resonantCubicPerturbationBound hp w A B n j) (by
      intro z hz
      rw [resonantCubic_homogeneous]
      exact (mul_le_mul_of_nonneg_left (resonantCubicPerturbation_norm_le hp w A B n z s hz hs i j)
        (w.positive _).le).trans_eq (by ring))
  exact ⟨h.1,h.2.1⟩

/-- Cubic normalization gives an eighth-power upper bound for the fourth-power error. -/
theorem resonantCubicPerturbationSup_fourth_normalized (hp : p ≠ ⊤) (w : SpectralWeight)
    (A B : WeightedCoeffPair w.toWeight p) (n : ℤ) (s : ℝ)
    (hs : 0 < s) (hs1 : s ≤ 1) (i j : Fin 2) :
    (resonantCubicPerturbationSup hp w A B n (s : ℂ) i j)^4/s^12 ≤
      (w (2*n)*resonantCubicPerturbationBound hp w A B n j)^4*s^8 := by
  have h := resonantCubicPerturbationSup_bounds hp w A B n (s : ℂ)
    (by simpa only [Complex.norm_real,Real.norm_of_nonneg hs.le] using hs1) i j
  simp only [Complex.norm_real,Real.norm_of_nonneg hs.le] at h
  apply (div_le_iff₀ (pow_pos hs 12)).mpr
  exact (pow_le_pow_left₀ h.1 h.2 4).trans_eq (by ring)

end NLS.ZakharovShabat
