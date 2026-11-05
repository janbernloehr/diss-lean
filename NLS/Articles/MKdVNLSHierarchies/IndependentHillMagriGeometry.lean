import NLS.KdV.HillMagriLogEnergyCoordinates

/-! # Independent Hill separated-coordinate geometry needed by Theorem 4(iii)

Every coordinate here is constructed from the original Hill Dirichlet
IVP and its logarithmic slope. The weak Magri pairing uses their actual
second derivatives and periodic traces. These results identify the
spectral bracket normalization needed to construct the independent
mKdV angle; they do not assert that the final Abelian angle is complete.
-/
noncomputable section
open Set Complex NLS.KdV NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.Articles.MKdVNLSHierarchies

/-- The complete raw independent separated-coordinate Magri matrix,
for every original real period-one L² Hill potential and all indices.
No simplicity of a periodic gap or finite spectral support is required. -/
theorem independent_Hill_weak_Magri_spectral_brackets (q : RealPeriodOneHillPotential)
    (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    hillDirichletMagriBracket q n m hn hm = 0 ∧
      hillDirichletLogMagriBracket q n m hn hm =
        (if n = m then -2*(hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ) else 0) ∧
      hillLogDirichletMagriBracket q n m hn hm =
        (if n = m then 2*(hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ) else 0) ∧
      hillLogNormingMagriBracket q n m hn hm = 0 :=
  ⟨hillDirichletMagriBracket_eq_zero q n m hn hm,hillDirichletLogMagriBracket_eq q n m hn hm,
    hillLogDirichletMagriBracket_eq q n m hn hm,hillLogNormingMagriBracket_eq_zero q n m hn hm⟩

/-- Logarithmic energy has the exact negative unit Magri normalization
against the independent log-norming coordinate whenever that energy is
nonzero. Its actual logarithmic derivative is proved separately. -/
theorem independent_Hill_logEnergy_unit_Magri_bracket (q : RealPeriodOneHillPotential)
    (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hmu : hillDirichletEnergy q.val q.property.1 q.property.2 n hn ≠ 0) :
    hillWeakGradientMagri (SpectralWeight.one.toCoeff q.val) (hillLogEnergyGradientCurve q n hn)
      (hillLogEnergyGradientSpatialCurve q n hn) (hillLogEnergyGradientSecond q n hn)
      (hillLogNormingGradientCurve q m hm) (hillLogNormingGradientSpatialCurve q m hm) =
        if n = m then -1 else 0 :=
  hillLogEnergyLogNormingMagriBracket_eq q n m hn hm hmu

end NLS.Articles.MKdVNLSHierarchies
