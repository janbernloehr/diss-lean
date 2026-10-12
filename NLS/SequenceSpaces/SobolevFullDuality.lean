import NLS.SequenceSpaces.FullDuality
import NLS.SequenceSpaces.SobolevBilinearPairing
import NLS.SequenceSpaces.WeightedFiniteCoefficients

/-! # Full physical scalar duality on every real Sobolev scale

Every bounded functional at finite p has a unique opposite-order coefficient
representative under the corrected physical pairing. The representative
has exactly the operator norm; the endpoint p=1 is included.
-/
noncomputable section
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [q.HolderConjugate p]

/-- Recover the physical scalar gradient, including frequency reversal. -/
def sobolevCotangent (s : ℝ) (hp : p ≠ ⊤)
    (L : WeightedCoeff (Weight.sobolev s) p →L[ℂ] ℂ) :
    WeightedCoeff (Weight.sobolev (-s)) q :=
  (weightIsometry (Weight.sobolev (-s)) q).symm
    (Coeff.reflection (Coeff.fullCotangent hp
      (L.comp (weightIsometry (Weight.sobolev s) p).symm.toContinuousLinearEquiv.toContinuousLinearMap)))

/-- The recovered gradient represents the entire functional, not only its modes. -/
theorem sobolevBilinearPairing_sobolevCotangent (s : ℝ) (hp : p ≠ ⊤)
    (L : WeightedCoeff (Weight.sobolev s) p →L[ℂ] ℂ) (h : WeightedCoeff (Weight.sobolev s) p) :
    sobolevBilinearPairing s h (sobolevCotangent (q := q) s hp L) = L h := by
  let e := weightIsometry (Weight.sobolev s) p
  let K := L.comp e.symm.toContinuousLinearEquiv.toContinuousLinearMap
  change Coeff.dualPairing (e h)
    (Coeff.reflection ((weightIsometry (Weight.sobolev (-s)) q)
      ((weightIsometry (Weight.sobolev (-s)) q).symm (Coeff.reflection (Coeff.fullCotangent hp K))))) = _
  rw [LinearIsometryEquiv.apply_symm_apply,Coeff.reflection_reflection]
  have hc : Coeff.dualPairing (e h) (Coeff.fullCotangent (q := q) hp K) =
      Coeff.dualPairing (Coeff.fullCotangent (q := q) hp K) (e h) := by
    exact tsum_congr (fun n => mul_comm _ _)
  rw [hc,Coeff.dualPairing_fullCotangent]
  change L (e.symm (e h)) = L h
  rw [LinearIsometryEquiv.symm_apply_apply]

/-- The exact original norm, with no constant lost to weight transport or reflection. -/
theorem norm_sobolevCotangent (s : ℝ) (hp : p ≠ ⊤)
    (L : WeightedCoeff (Weight.sobolev s) p →L[ℂ] ℂ) :
    ‖sobolevCotangent (q := q) s hp L‖ = ‖L‖ := by
  apply le_antisymm
  · simp only [sobolevCotangent,LinearIsometryEquiv.norm_map,Coeff.norm_fullCotangent]
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro a
    simpa only [ContinuousLinearMap.comp_apply,LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      ContinuousLinearEquiv.coe_coe,LinearIsometryEquiv.norm_map] using
      L.le_opNorm ((weightIsometry (Weight.sobolev s) p).symm a)
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro h
    rw [← sobolevBilinearPairing_sobolevCotangent (q := q) s hp L h,mul_comm]
    exact norm_sobolevBilinearPairing_le s h _

/-- A physical gradient is uniquely determined by its action on the original source space. -/
theorem sobolevBilinearPairing_flip_injective (s : ℝ) :
    Function.Injective (sobolevBilinearPairing (p := p) (q := q) s).flip := by
  intro a b hab
  apply (weightIsometry (Weight.sobolev (-s)) q).injective
  apply Coeff.reflection.injective
  apply Coeff.dualPairing_injective (p := p)
  ext x
  have h := congrArg (fun L : WeightedCoeff (Weight.sobolev s) p →L[ℂ] ℂ =>
    L ((weightIsometry (Weight.sobolev s) p).symm x)) hab
  change Coeff.dualPairing ((weightIsometry (Weight.sobolev s) p)
      ((weightIsometry (Weight.sobolev s) p).symm x))
      (Coeff.reflection ((weightIsometry (Weight.sobolev (-s)) q) a)) =
    Coeff.dualPairing ((weightIsometry (Weight.sobolev s) p)
      ((weightIsometry (Weight.sobolev s) p).symm x))
      (Coeff.reflection ((weightIsometry (Weight.sobolev (-s)) q) b)) at h
  simp only [LinearIsometryEquiv.apply_symm_apply] at h
  simpa only [Coeff.dualPairing_apply,mul_comm] using h

/-- Unique representation under the physical pairing for all finite source exponents. -/
theorem existsUnique_sobolevCotangent (s : ℝ) (hp : p ≠ ⊤)
    (L : WeightedCoeff (Weight.sobolev s) p →L[ℂ] ℂ) :
    ∃! a : WeightedCoeff (Weight.sobolev (-s)) q, ∀ h : WeightedCoeff (Weight.sobolev s) p, sobolevBilinearPairing s h a = L h := by
  refine ⟨sobolevCotangent (q := q) s hp L,sobolevBilinearPairing_sobolevCotangent (q := q) s hp L,?_⟩
  intro a ha
  apply sobolevBilinearPairing_flip_injective (p := p) s
  ext h
  exact (ha h).trans (sobolevBilinearPairing_sobolevCotangent (q := q) s hp L h).symm


@[simp] theorem sobolevCotangent_pairing (s : ℝ) (hp : p ≠ ⊤)
    (a : WeightedCoeff (Weight.sobolev (-s)) q) :
    sobolevCotangent (q := q) s hp ((sobolevBilinearPairing (p := p) s).flip a) = a := by
  apply sobolevBilinearPairing_flip_injective (p := p) s
  ext h
  exact sobolevBilinearPairing_sobolevCotangent (q := q) s hp _ h

/-- Physical duality is a complex linear isometry onto the entire continuous dual. -/
def sobolevDualityIsometry (s : ℝ) (hp : p ≠ ⊤) :
    WeightedCoeff (Weight.sobolev (-s)) q ≃ₗᵢ[ℂ]
      (WeightedCoeff (Weight.sobolev s) p →L[ℂ] ℂ) where
  toLinearEquiv := LinearEquiv.ofBijective (sobolevBilinearPairing (p := p) (q := q) s).flip.toLinearMap
    ⟨sobolevBilinearPairing_flip_injective (p := p) (q := q) s,fun L =>
      ⟨sobolevCotangent (q := q) s hp L,ContinuousLinearMap.ext (sobolevBilinearPairing_sobolevCotangent (q := q) s hp L)⟩⟩
  norm_map' a := by
    change ‖(sobolevBilinearPairing (p := p) s).flip a‖ = ‖a‖
    simpa only [sobolevCotangent_pairing] using
      (norm_sobolevCotangent (q := q) s hp ((sobolevBilinearPairing s).flip a)).symm

@[simp] theorem sobolevDualityIsometry_apply (s : ℝ) (hp : p ≠ ⊤)
    (a : WeightedCoeff (Weight.sobolev (-s)) q) (h : WeightedCoeff (Weight.sobolev s) p) :
    sobolevDualityIsometry s hp a h = sobolevBilinearPairing s h a := rfl

@[simp] theorem sobolevDualityIsometry_symm_apply (s : ℝ) (hp : p ≠ ⊤)
    (L : WeightedCoeff (Weight.sobolev s) p →L[ℂ] ℂ) :
    (sobolevDualityIsometry (q := q) s hp).symm L = sobolevCotangent (q := q) s hp L := by
  apply (sobolevDualityIsometry s hp).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  ext h
  exact (sobolevBilinearPairing_sobolevCotangent (q := q) s hp L h).symm


/-- The physical coefficient at n is the original functional evaluated on the raw mode -n. -/
@[simp] theorem sobolevCotangent_val (s : ℝ) (hp : p ≠ ⊤)
    (L : WeightedCoeff (Weight.sobolev s) p →L[ℂ] ℂ) (n : ℤ) :
    (sobolevCotangent (q := q) s hp L).val n =
      L (ofFinsupp (Weight.sobolev s) p (Finsupp.single (-n) 1)) := by
  have h := sobolevBilinearPairing_sobolevCotangent (q := q) s hp L
    (ofFinsupp (Weight.sobolev s) p (Finsupp.single (-n) 1))
  simpa [sobolevBilinearPairing_apply,ofFinsupp_apply,Finsupp.single_apply] using h

end NLS.WeightedCoeff
