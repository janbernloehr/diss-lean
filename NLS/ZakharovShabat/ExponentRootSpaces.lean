import NLS.ZakharovShabat.ExponentDomainRegularity
import NLS.ZakharovShabat.RootSpaces

/-!
# Exact root-space comparison across finite sequence exponents

Every root chain at the larger exponent recovers smaller-exponent domain
regularity one step at a time. Thus the actual coefficient inclusion maps
both finite and full original root spaces onto their counterparts.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- The original root spaces at every finite chain length are exactly transported by exponent inclusion. -/
theorem periodicRootSpace_map_exponent (hp : p ≠ ⊤) (hq : q ≠ ⊤) (h : p ≤ q)
    (φ : PairSpace p) (z : ℂ) (n : ℕ) :
    (periodicRootSpace hp φ z n).map (pairExponentInclusion h).toLinearMap =
      periodicRootSpace hq (pairExponentInclusion h φ) z n := by
  induction n with
  | zero => simp only [periodicRootSpace_zero, Submodule.map_bot]
  | succ n ih =>
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨a, ha, hPa⟩ := (mem_periodicRootSpace_succ hp φ z n y).mp hy
      apply (mem_periodicRootSpace_succ hq (pairExponentInclusion h φ) z n _).mpr
      refine ⟨domainExponentInclusion h a, ?_, ?_⟩
      · rw [domainInclusion_domainExponentInclusion, ha]
        rfl
      · rw [spectralPencil_domainExponentInclusion hp hq, ← ih]
        exact ⟨spectralPencil hp φ z a, hPa, rfl⟩
    · intro hx
      obtain ⟨a, ha, hPa⟩ := (mem_periodicRootSpace_succ hq (pairExponentInclusion h φ) z n x).mp hx
      rw [← ih] at hPa
      obtain ⟨b, hb, hbe⟩ := hPa
      obtain ⟨c, hc⟩ := exists_domain_of_spectralPencil_exponent hq h φ b z a hbe.symm
      have hPc : spectralPencil hp φ z c = b := by
        apply pairExponentInclusion_injective h
        rw [← spectralPencil_domainExponentInclusion hp hq, hc]
        exact hbe.symm
      refine ⟨domainInclusion c, ?_, ?_⟩
      · exact (mem_periodicRootSpace_succ hp φ z n _).mpr ⟨c, rfl, hPc ▸ hb⟩
      · change pairExponentInclusion h (domainInclusion c) = x
        rw [← domainInclusion_domainExponentInclusion, hc, ha]

/-- Exponent inclusion maps onto the full original root space, including all generalized vectors. -/
theorem periodicRootSpaceTop_map_exponent (hp : p ≠ ⊤) (hq : q ≠ ⊤) (h : p ≤ q)
    (φ : PairSpace p) (z : ℂ) :
    (periodicRootSpaceTop hp φ z).map (pairExponentInclusion h).toLinearMap =
      periodicRootSpaceTop hq (pairExponentInclusion h φ) z := by
  simp only [periodicRootSpaceTop, Submodule.map_iSup, periodicRootSpace_map_exponent hp hq h]

/-- Every finite root-space dimension is independent of increasing the ambient exponent. -/
theorem finrank_periodicRootSpace_exponent (hp : p ≠ ⊤) (hq : q ≠ ⊤) (h : p ≤ q)
    (φ : PairSpace p) (z : ℂ) (n : ℕ) :
    Module.finrank ℂ (periodicRootSpace hp φ z n) =
      Module.finrank ℂ (periodicRootSpace hq (pairExponentInclusion h φ) z n) := by
  rw [← periodicRootSpace_map_exponent hp hq h]
  exact (Submodule.equivMapOfInjective (pairExponentInclusion h).toLinearMap
    (pairExponentInclusion_injective h) _).finrank_eq

/-- The full original algebraic multiplicity is unchanged by exponent inclusion. -/
theorem periodicAlgebraicMultiplicity_exponent (hp : p ≠ ⊤) (hq : q ≠ ⊤) (h : p ≤ q)
    (φ : PairSpace p) (z : ℂ) :
    periodicAlgebraicMultiplicity hp φ z =
      periodicAlgebraicMultiplicity hq (pairExponentInclusion h φ) z := by
  simp only [periodicAlgebraicMultiplicity]
  rw [← periodicRootSpaceTop_map_exponent hp hq h]
  exact (Submodule.equivMapOfInjective (pairExponentInclusion h).toLinearMap
    (pairExponentInclusion_injective h) _).finrank_eq

end NLS.ZakharovShabat
