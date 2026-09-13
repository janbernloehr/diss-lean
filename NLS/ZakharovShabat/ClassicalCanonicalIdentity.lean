import NLS.ZakharovShabat.ClassicalExteriorRatioBounds
import NLS.ZakharovShabat.CanonicalExteriorLowerBounds
import NLS.ZakharovShabat.ClassicalExteriorNormalization

/-!
# Exact classical normalization of the canonical products

For an even Hilbert potential with a compatible continuous representative,
the intrinsic parity products are exactly the shifted classical trace and
the full product is its squared discriminant. The exterior quotient bound
is proved here, rather than assumed.
-/

noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra NLS.Fourier
namespace NLS.ZakharovShabat

/-- Each filled parity quotient is bounded at exterior infinity. The bound itself
does not require compatibility of the two potentials. -/
theorem exists_bound_classicalParityProductQuotient_exterior
    (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0) (Φ : Curve (ℂ × ℂ))
    (k : ℤ) (hk : k = 0 ∨ k = 1) {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4) :
    ∃ R B : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → (∀ n : ℤ, r ≤ ‖z-(Real.pi : ℂ)*n‖) →
      ‖classicalParityProductQuotient φ Φ k z‖ ≤ B := by
  have hb : (2*wave k 1)^2 = (4 : ℂ) := by
    rcases hk with rfl | rfl
    · norm_num [wave_zero]
    · have hw : wave 1 1 = -1 := by simpa using wave_odd_at_one 0
      rw [hw]; norm_num
  obtain ⟨B, hB, hbound⟩ := exists_bound_classicalDiscriminant_sub_div_free Φ (2*wave k 1) hb hr
  obtain ⟨R, hR⟩ := exists_threshold_canonicalParity_div_free_lower
    (by simp : (2 : ENNReal) ≠ ⊤) (by norm_num) φ hφ k hk hr hrπ
  refine ⟨R, 2*B, ?_⟩
  intro z hz hsep
  have hl := hR z hz hsep
  have hg : canonicalParityProduct (by simp) φ k z ≠ 0 := by
    intro hg
    simp only [hg, zero_div, norm_zero] at hl
    norm_num at hl
  have hd : freeDiscriminant z-2*wave k 1 ≠ 0 :=
    freeDiscriminant_sub_ne_zero_of_sq_eq_four _ hb z (notMem_freeLattice_of_separated hr hsep)
  rw [classicalParityProductQuotient_eq_div φ hφ Φ k hk z hg,
    ← div_div_div_cancel_right₀ hd, norm_div]
  have hpos := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/2) hl
  apply (div_le_iff₀ hpos).mpr
  calc
    ‖(classicalDiscriminant Φ z-2*wave k 1)/(freeDiscriminant z-2*wave k 1)‖ ≤ B := hbound z hsep
    _ ≤ 2*B*‖canonicalParityProduct (by simp) φ k z/(freeDiscriminant z-2*wave k 1)‖ := by
      nlinarith

/-- The canonical parity product has the exact classical normalization. -/
theorem canonicalParity_eq_classical
    (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0)
    (Φ : Curve (ℂ × ℂ)) (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (k : ℤ) (hk : k = 0 ∨ k = 1) (z : ℂ) :
    canonicalParityProduct (by simp) φ k z = classicalDiscriminant Φ z-2*wave k 1 := by
  have hr : 0 < Real.pi/4 := by positivity
  obtain ⟨R, B, hb⟩ := exists_bound_classicalParityProductQuotient_exterior φ hφ Φ k hk hr le_rfl
  exact canonicalParity_eq_classical_of_exterior_quotient_bound φ hφ Φ hΦ k hk hr le_rfl R B hb z

/-- The even intrinsic product is the classical trace minus two. -/
theorem canonicalEven_eq_classical
    (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0)
    (Φ : Curve (ℂ × ℂ)) (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ) (z : ℂ) :
    canonicalParityProduct (by simp) φ 0 z = classicalDiscriminant Φ z-2 := by
  simpa only [wave_zero, mul_one] using canonicalParity_eq_classical φ hφ Φ hΦ 0 (Or.inl rfl) z

/-- The odd intrinsic product is the classical trace plus two. -/
theorem canonicalOdd_eq_classical
    (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0)
    (Φ : Curve (ℂ × ℂ)) (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ) (z : ℂ) :
    canonicalParityProduct (by simp) φ 1 z = classicalDiscriminant Φ z+2 := by
  have hw : wave 1 1 = -1 := by simpa using wave_odd_at_one 0
  simpa only [hw, mul_neg_one, sub_neg_eq_add] using
    canonicalParity_eq_classical φ hφ Φ hΦ 1 (Or.inr rfl) z

/-- The full intrinsic product is exactly the classical characteristic function. -/
theorem canonicalPeriodic_eq_classical
    (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0)
    (Φ : Curve (ℂ × ℂ)) (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ) (z : ℂ) :
    canonicalPeriodicProduct (by simp) φ z = (classicalDiscriminant Φ z)^2-4 := by
  rw [← canonicalParityProducts_mul (by simp) (by norm_num) φ hφ z,
    canonicalEven_eq_classical φ hφ Φ hΦ, canonicalOdd_eq_classical φ hφ Φ hΦ]
  ring

/-- Lemma 8.1's two shifted products recover the same classical trace. -/
theorem canonicalParity_shifted_eq_classical
    (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0)
    (Φ : Curve (ℂ × ℂ)) (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ) (z : ℂ) :
    canonicalParityProduct (by simp) φ 0 z+2 = classicalDiscriminant Φ z ∧
    canonicalParityProduct (by simp) φ 1 z-2 = classicalDiscriminant Φ z := by
  rw [canonicalEven_eq_classical φ hφ Φ hΦ, canonicalOdd_eq_classical φ hφ Φ hΦ]
  constructor <;> ring

end NLS.ZakharovShabat
