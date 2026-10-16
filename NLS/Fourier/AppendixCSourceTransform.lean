import NLS.Fourier.ModifiedHilbert
import NLS.Fourier.HilbertNotIsomorphismLp

/-!
# Appendix C: original convergent series and exact operator scope

C.1 defines a unique bounded operator for every finite exponent above one,
but its printed isomorphism assertion fails throughout that range. Even an
algebraic linear equivalence cannot satisfy the source series on all inputs.

C.2 retains arbitrary bounded complex lattice displacements, the exact pi
factor, and the omitted diagonal. A single bound is chosen before both
lattices, depending only on their norm bounds, the separation constant, and p.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Fourier
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The ordinary transform has the actual convergent source series on every input. -/
theorem sourceHilbert_hasSum (hp1 : 1 < p) (hp : p ≠ ⊤) (a : Coeff p) (n : ℤ) :
    HasSum (fun k : ℤ => if k = n then 0 else a k / ((k : ℂ) - n))
      (hilbertTransform hp1 hp a n) := by
  let : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩
  have he : (fun k : ℤ => if k = n then 0 else a k / ((k : ℂ) - n)) =
      (fun k : ℤ => a k / ((k : ℂ) - n)) := by
    funext k
    split_ifs with h
    · simp [h]
    · rfl
  rw [he, hilbertTransform_apply hp1 hp
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top)
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p.conjExponent p).mpr hp1).ne]
  exact (summable_norm_hilbertSeries_of_finite hp1 hp a n).of_norm.hasSum

/-- The valid part of C.1: a unique bounded complex linear realization, with its norm bound. -/
theorem sourceLemmaC1_bounded (hp1 : 1 < p) (hp : p ≠ ⊤) :
    ∃! H : Coeff p →L[ℂ] Coeff p,
      (∀ (a : Coeff p) (n : ℤ),
        HasSum (fun k : ℤ => if k = n then 0 else a k / ((k : ℂ) - n)) (H a n)) ∧
      ‖H‖ ≤ hilbertTransformBound hp1 hp := by
  refine ⟨hilbertTransform hp1 hp, ⟨sourceHilbert_hasSum hp1 hp, ?_⟩, ?_⟩
  · exact ContinuousLinearMap.opNorm_le_bound _ (hilbertTransformBound_nonneg hp1 hp)
      (norm_hilbertTransform_apply_le hp1 hp)
  · intro H hH
    ext a n
    exact (hH.1 a n).unique (sourceHilbert_hasSum hp1 hp a n)

/-- C.1's isomorphism assertion fails at every finite exponent strictly above one. -/
theorem sourceLemmaC1_not_bijective (hp1 : 1 < p) (hp : p ≠ ⊤) :
    ¬ Function.Bijective (hilbertTransform hp1 hp) :=
  HilbertLpObstruction.transform_not_bijective hp1 hp

/-- No continuous linear equivalence can realize the printed ordinary series. -/
theorem sourceLemmaC1_no_isomorphism (hp1 : 1 < p) (hp : p ≠ ⊤) :
    ¬ ∃ H : Coeff p ≃L[ℂ] Coeff p,
      ∀ (a : Coeff p) (n : ℤ),
        HasSum (fun k : ℤ => if k = n then 0 else a k / ((k : ℂ) - n)) (H a n) := by
  rintro ⟨H, hH⟩
  apply sourceLemmaC1_not_bijective hp1 hp
  have he : hilbertTransform hp1 hp = H.toContinuousLinearMap := by
    ext a n
    exact (sourceHilbert_hasSum hp1 hp a n).unique (hH a n)
  rw [he]
  exact H.bijective

/-- No algebraic linear equivalence can realize it either: its series already forces continuity. -/
theorem sourceLemmaC1_no_linearEquiv (hp1 : 1 < p) (hp : p ≠ ⊤) :
    ¬ ∃ H : Coeff p ≃ₗ[ℂ] Coeff p,
      ∀ (a : Coeff p) (n : ℤ),
        HasSum (fun k : ℤ => if k = n then 0 else a k / ((k : ℂ) - n)) (H a n) := by
  rintro ⟨H, hH⟩
  apply sourceLemmaC1_not_bijective hp1 hp
  have he : (hilbertTransform hp1 hp : Coeff p → Coeff p) = H := by
    funext a
    apply lp.ext
    funext n
    exact (sourceHilbert_hasSum hp1 hp a n).unique (hH a n)
  rw [he]
  exact H.bijective

/-- The exact C.2 series converges, with the factor pi and the diagonal explicitly omitted. -/
theorem sourceModifiedHilbert_hasSum (hp1 : 1 < p) (hp : p ≠ ⊤)
    (s r : Coeff ⊤) {c : ℝ} (hc : 0 < c) (hsep : HilbertLatticeSeparated s r c)
    (a : Coeff p) (n : ℤ) :
    HasSum (fun k : ℤ => if k = n then 0 else
      (Real.pi : ℂ) * (a k / (hilbertLattice r k - hilbertLattice s n)))
      (modifiedHilbert s r hc hsep hp1 hp a n) := by
  rw [modifiedHilbert_source_apply]
  simpa only [mul_ite, mul_zero] using
    ((summable_norm_modifiedHilbert_source_series s r hc hsep hp1 hp a n).of_norm.hasSum).mul_left
      (Real.pi : ℂ)

/-- C.2 with a uniform constant fixed before both lattices and their unique operator.
Only the printed separation and bounded complex displacement assumptions are used. -/
theorem sourceLemmaC2 (hp1 : 1 < p) (hp : p ≠ ⊤)
    {c S R : ℝ} (hc : 0 < c) (hS : 0 ≤ S) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s r : Coeff ⊤, ‖s‖ ≤ S → ‖r‖ ≤ R →
      HilbertLatticeSeparated s r c →
        ∃! A : Coeff p →L[ℂ] Coeff p,
          (∀ (a : Coeff p) (n : ℤ), HasSum (fun k : ℤ => if k = n then 0 else
            (Real.pi : ℂ) * (a k / (hilbertLattice r k - hilbertLattice s n))) (A a n)) ∧
          ‖A‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_modifiedHilbert_uniform_bound hc hp1 hp hS hR
  refine ⟨C, hC, ?_⟩
  intro s r hs hr hsep
  refine ⟨modifiedHilbert s r hc hsep hp1 hp,
    ⟨sourceModifiedHilbert_hasSum hp1 hp s r hc hsep, hbound s r hs hr hsep⟩, ?_⟩
  intro A hA
  ext a n
  exact (hA.1 a n).unique (sourceModifiedHilbert_hasSum hp1 hp s r hc hsep a n)

end NLS.Fourier
