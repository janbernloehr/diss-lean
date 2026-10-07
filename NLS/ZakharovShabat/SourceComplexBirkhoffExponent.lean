import NLS.ZakharovShabat.SourceBirkhoffImageInverse
import NLS.ZakharovShabat.SourceBirkhoffMapExponent
import NLS.ZakharovShabat.SourceFiniteGapMassDivergence

/-! # Complex Birkhoff coordinates and the Hilbert locus

The actual complex coordinate map commutes with exponent inclusion.
Consequently a Hilbert source has square-summable complex Birkhoff
coordinates even when it is viewed in a larger source space.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.Birkhoff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- The real-to-complex coordinate change preserves coefficientwise exponent inclusions. -/
theorem encodeReal_exponent (hpq : p ≤ q) (z : RealCoeff p × RealCoeff p) :
    encodeReal (((RealCoeff.exponentInclusion hpq).prodMap (RealCoeff.exponentInclusion hpq)) z) =
      ((Coeff.exponentInclusion hpq).prodMap (Coeff.exponentInclusion hpq)) (encodeReal z) := by
  apply Prod.ext <;> ext n <;> simp [encodeReal]

end NLS.Birkhoff
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B X : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
variable {hq : q ≠ ⊤} {hq1 : 1 < q} {V₀ C Y : Set (CoeffPair q)}
  {t : (n : ℤ) → CoeffPair q → DeletedCoeff q n}

/-- The actual complex Birkhoff map commutes with increasing the source exponent. -/
theorem complex_map_exponent (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X s)
    (E : SourceBirkhoffMapComplexData hq hq1 V₀ C Y t) (hpq : p ≤ q)
    (φ : realTypeSourceSubmodule p) :
    ((Coeff.exponentInclusion hpq).prodMap (Coeff.exponentInclusion hpq))
      (sourceComplexBirkhoffMap hp hp1 s φ.val) =
    sourceComplexBirkhoffMap hq hq1 t (realTypeSourceExponentInclusion hpq φ).val := by
  let ψ : realTypeSourceSubmodule q := realTypeSourceExponentInclusion hpq φ
  change _ = sourceComplexBirkhoffMap hq hq1 t ψ.val
  rw [← D.encode_real_map,← E.encode_real_map ψ,← Birkhoff.encodeReal_exponent]
  exact congrArg (Birkhoff.encodeReal (p := q)) (D.real_map_exponent E hpq φ)

/-- Hilbert sources have square-summable first complex coordinates in every larger exponent. -/
theorem summable_complex_map_fst_of_mem_hilbert
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X s) (h2p : 2 ≤ p)
    (φ : realTypeSourceSubmodule p) (hφ : φ ∈ sourceHilbertLocus h2p) :
    Summable (fun n : ℤ => ‖(sourceComplexBirkhoffMap hp hp1 s φ.val).1 n‖^2) := by
  obtain ⟨ψ,rfl⟩ := hφ
  obtain ⟨V₀,C,Y,t,E⟩ := exists_sourceBirkhoffMap_complex_analytic (p := 2) (by simp) (by norm_num)
  have he := E.complex_map_exponent D h2p ψ
  rw [← he]
  simpa only [Coeff.exponentInclusion_apply,
    ENNReal.toReal_ofNat,Real.rpow_two] using!
    (sourceComplexBirkhoffMap (by simp) (by norm_num) t ψ.val).1.property.summable
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal)

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
