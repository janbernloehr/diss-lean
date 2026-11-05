import NLS.MKdV.MiuraLogEnergyGardnerCoordinates
import NLS.MKdV.MiuraDirichletBranchCompatibility

/-! # Independent spectral Gardner geometry on every original real H¹ profile

The branches exist unconditionally and agree with the original Hill
Dirichlet data on nearby real profiles. Their actual H¹ gradients give
the full raw and half-logarithmic Gardner matrices, including closed gaps.
The independent Abelian mKdV phase is still required for Theorem 4(iii).
-/
noncomputable section
open Set Complex NLS.Poisson NLS.ZakharovShabat NLS.KdV NLS.MKdV
open scoped ComplexConjugate
namespace NLS.Articles.MKdVNLSHierarchies

theorem independent_mKdV_Dirichlet_energy_positive (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n) :
    0 < hillDirichletEnergy (realSobolevMiuraHillPotential a ha).val
      (realSobolevMiuraHillPotential a ha).property.1 (realSobolevMiuraHillPotential a ha).property.2 n hn :=
  hillDirichletEnergy_Miura_pos a ha n hn

/-- Every real H¹ profile admits actual original spectral branches whose
Gardner brackets have the independently derived normalization. The
existence statement has no regular-gap or finite-support hypotheses. -/
theorem independent_mKdV_spectral_Gardner_geometry (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    ∃ (B : MiuraDirichletBranch a ha n hn) (C : MiuraDirichletBranch a ha m hm),
      B.energyGradient.bracket C.energyGradient = 0 ∧
      B.energyGradient.bracket C.logNormingGradient =
        (if n = m then -2*(hillDirichletEnergy (realSobolevMiuraHillPotential a ha).val
          (realSobolevMiuraHillPotential a ha).property.1 (realSobolevMiuraHillPotential a ha).property.2 n hn : ℂ) else 0) ∧
      B.logNormingGradient.bracket C.energyGradient =
        (if n = m then 2*(hillDirichletEnergy (realSobolevMiuraHillPotential a ha).val
          (realSobolevMiuraHillPotential a ha).property.1 (realSobolevMiuraHillPotential a ha).property.2 n hn : ℂ) else 0) ∧
      B.logNormingGradient.bracket C.logNormingGradient = 0 ∧
      B.logEnergyGradient.bracket C.logNormingGradient = (if n = m then -1 else 0) ∧
      B.logNormingGradient.bracket C.logEnergyGradient = (if n = m then 1 else 0) ∧
      B.logEnergyGradient.bracket C.logEnergyGradient = 0 := by
  obtain ⟨B⟩ := nonempty_miuraDirichletBranch a ha n hn
  obtain ⟨C⟩ := nonempty_miuraDirichletBranch a ha m hm
  exact ⟨B,C,B.energyGradient_bracket C,B.energyGradient_logNormingGradient_bracket C,
    B.logNormingGradient_energyGradient_bracket C,B.logNormingGradient_bracket C,
    B.logEnergyGradient_logNormingGradient_bracket C,B.logNormingGradient_logEnergyGradient_bracket C,
    B.logEnergyGradient_bracket C⟩

end NLS.Articles.MKdVNLSHierarchies
