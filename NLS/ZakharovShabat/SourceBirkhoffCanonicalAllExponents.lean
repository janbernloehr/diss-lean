import NLS.ZakharovShabat.SourceBirkhoffCoordinateExponent
import NLS.ZakharovShabat.SourceBirkhoffClosedGapPoisson

/-! # Canonical rectangular cotangents at every finite exponent

Restriction from an exponent at least two supplies actual square-summable
Fourier witnesses even below two and at closed gaps. Equality of the full
rectangular derivatives makes the physical pairing independent of the
chosen comparison family. All three canonical identities follow.
-/

noncomputable section
open Set Complex NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
namespace SourceAngularEtaLocalCommonDomainData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- Restriction from any larger exponent at least two gives regular
cotangents for the original family's full rectangular derivatives. -/
theorem exists_birkhoff_regular_canonical_of_le
    (D : SourceAngularEtaLocalCommonDomainData hp hp1 W₀ B s)
    (W : Set (CoeffPair p)) (hW : IsOpen W) (hWB : W ⊆ B)
    (hrW : realTypeSourceLocus p ⊆ W)
    {hq : q ≠ ⊤} {hq1 : 1 < q} {V₀ C V : Set (CoeffPair q)}
    {t : (k : ℤ) → CoeffPair q → DeletedCoeff q k}
    (E : SourceAngularThetaCommonDomainData hq hq1 V₀ C V t)
    (hpq : p ≤ q) (h2q : (2 : ℝ≥0∞) ≤ q) (φ : realTypeSourceSubmodule p) :
    ∃ X Y : ℤ → RegularSourceCotangent p,
      (∀ n, (X n).toCotangent = fderiv ℂ (sourceBirkhoffX hp hp1 n s) φ.val ∧
        (Y n).toCotangent = fderiv ℂ (sourceBirkhoffY hp hp1 n s) φ.val) ∧
      ∀ n m, (X n).bivector (X m) = 0 ∧
        (X n).bivector (Y m) = -(if n = m then 1 else 0) ∧ (Y n).bivector (Y m) = 0 := by
  let χ := CoeffPair.exponentInclusion hpq φ.val
  let X (n : ℤ) := (RegularSourceCotangent.ofCotangent h2q (fderiv ℂ (sourceBirkhoffX hq hq1 n t) χ)).restrict hpq
  let Y (n : ℤ) := (RegularSourceCotangent.ofCotangent h2q (fderiv ℂ (sourceBirkhoffY hq hq1 n t) χ)).restrict hpq
  refine ⟨X,Y,?_,?_⟩
  · intro n
    have h := D.fderiv_birkhoffXY_exponent E.toSourceAngularEtaLocalCommonDomainData
      W V hW E.source_open hWB E.source_subset hrW E.real_subset hpq n φ
    exact ⟨h.1.symm,h.2.symm⟩
  · intro n m
    exact E.birkhoff_sourceBracket_canonical h2q n m
      ⟨χ,(realTypeSourceExponentInclusion hpq φ).property⟩

/-- Lemma 15.3 for the actual scalar coordinates of any constructed
angular family, at every real source and every finite exponent above one. -/
theorem exists_birkhoff_regular_canonical
    (D : SourceAngularEtaLocalCommonDomainData hp hp1 W₀ B s)
    (W : Set (CoeffPair p)) (hW : IsOpen W) (hWB : W ⊆ B)
    (hrW : realTypeSourceLocus p ⊆ W) (φ : realTypeSourceSubmodule p) :
    ∃ X Y : ℤ → RegularSourceCotangent p,
      (∀ n, (X n).toCotangent = fderiv ℂ (sourceBirkhoffX hp hp1 n s) φ.val ∧
        (Y n).toCotangent = fderiv ℂ (sourceBirkhoffY hp hp1 n s) φ.val) ∧
      ∀ n m, (X n).bivector (X m) = 0 ∧
        (X n).bivector (Y m) = -(if n = m then 1 else 0) ∧ (Y n).bivector (Y m) = 0 := by
  by_cases h2p : (2 : ℝ≥0∞) ≤ p
  · obtain ⟨V₀,C,V,_,_,_,_,_,_,t,E⟩ := exists_sourceAngularTheta_theorem13_1_iv hp hp1
    exact D.exists_birkhoff_regular_canonical_of_le W hW hWB hrW E (le_refl _) h2p φ
  · obtain ⟨V₀,C,V,_,_,_,_,_,_,t,E⟩ := exists_sourceAngularTheta_theorem13_1_iv (p := 2) (by simp) (by norm_num)
    exact D.exists_birkhoff_regular_canonical_of_le W hW hWB hrW E (le_of_not_ge h2p) (le_refl _) φ

end SourceAngularEtaLocalCommonDomainData
end NLS.ZakharovShabat
