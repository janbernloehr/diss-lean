import NLS.MKdV.MiuraDirichletBranchGradients
import NLS.Poisson.SobolevGardnerGradientCalculus
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-! # The independent logarithmic-energy Gardner normalization on real H¹

Strict positivity of the original Dirichlet energies makes every local
half-logarithm legitimate. Its actual H¹ gradient has bracket -delta
with the independent logarithmic Dirichlet multiplier. This is separated
spectral geometry, not the final Abelian angle construction.
-/
noncomputable section
open Set Complex NLS.Poisson NLS.ZakharovShabat NLS.KdV
open scoped ComplexConjugate
namespace NLS.MKdV.MiuraDirichletBranch
variable {a : ScalarDomain 2} {ha : ∀ n, a.val n = conj (a.val (-n))} {n : ℕ} {hn : 1 ≤ n}

theorem energyBranch_mem_slitPlane (B : MiuraDirichletBranch a ha n hn) :
    B.energyBranch (sobolevMiuraHillPotential a) ∈ slitPlane := by
  rw [B.value]
  exact Complex.ofReal_mem_slitPlane.mpr (hillDirichletEnergy_Miura_pos a ha n hn)

def logEnergyGradient (B : MiuraDirichletBranch a ha n hn) :
    SobolevGardnerGradientAt (fun b => (1/2 : ℂ)*log (B.energyBranch (sobolevMiuraHillPotential b))) a :=
  B.energyGradient.comp (fun z => (1/2 : ℂ)*log z)
    ((1/2 : ℂ)*(B.energyBranch (sobolevMiuraHillPotential a))⁻¹)
    ((Complex.hasDerivAt_log B.energyBranch_mem_slitPlane).const_mul (1/2 : ℂ))

theorem logEnergyGradient_logNormingGradient_bracket (B : MiuraDirichletBranch a ha n hn)
    {m : ℕ} {hm : 1 ≤ m} (C : MiuraDirichletBranch a ha m hm) :
    B.logEnergyGradient.bracket C.logNormingGradient = if n = m then -1 else 0 := by
  rw [logEnergyGradient,SobolevGardnerGradientAt.comp_bracket,
    B.energyGradient_logNormingGradient_bracket C,B.value]
  by_cases h : n = m
  · rw [if_pos h,if_pos h]
    have hmu := Complex.ofReal_ne_zero.mpr (hillDirichletEnergy_Miura_pos a ha n hn).ne'
    field_simp [hmu]
  · rw [if_neg h,if_neg h,mul_zero]

theorem logEnergyGradient_bracket (B : MiuraDirichletBranch a ha n hn)
    {m : ℕ} {hm : 1 ≤ m} (C : MiuraDirichletBranch a ha m hm) :
    B.logEnergyGradient.bracket C.logEnergyGradient = 0 := by
  rw [logEnergyGradient,logEnergyGradient,SobolevGardnerGradientAt.comp_bracket,
    SobolevGardnerGradientAt.bracket_comp,B.energyGradient_bracket C,mul_zero,mul_zero]

theorem logNormingGradient_logEnergyGradient_bracket (B : MiuraDirichletBranch a ha n hn)
    {m : ℕ} {hm : 1 ≤ m} (C : MiuraDirichletBranch a ha m hm) :
    B.logNormingGradient.bracket C.logEnergyGradient = if n = m then 1 else 0 := by
  rw [SobolevGardnerGradientAt.bracket_antisymm,C.logEnergyGradient_logNormingGradient_bracket B]
  by_cases h : n = m
  · simp only [h,ite_true,neg_neg]
  · simp only [h,Ne.symm h,ite_false,neg_zero]

end NLS.MKdV.MiuraDirichletBranch
