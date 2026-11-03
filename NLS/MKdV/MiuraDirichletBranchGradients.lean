import NLS.MKdV.HillNativeSpectralBrackets
import NLS.MKdV.MiuraHillDirichletPositivity
import NLS.KdV.HillNativeBranchGradients

/-! # Actual independent Dirichlet spectral gradients on the original mKdV domain

Every real H¹ profile admits local complex analytic branches of the
original Hill Dirichlet energy. Their energy and logarithmic multiplier
pullbacks have the explicitly constructed H¹ Gardner gradients below.
The branches agree locally with the original independent spectral data.
-/
noncomputable section
open Set Complex Filter Topology MeasureTheory
open NLS.Fourier NLS.Poisson NLS.ZakharovShabat NLS.KdV
open scoped ComplexConjugate ENNReal
namespace NLS.MKdV

structure MiuraDirichletBranch (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (n : ℕ) (hn : 1 ≤ n) where
  energyBranch : Coeff 2 → ℂ
  analytic : AnalyticAt ℂ energyBranch (sobolevMiuraHillPotential a)
  value : energyBranch (sobolevMiuraHillPotential a) =
    (hillDirichletEnergy (realSobolevMiuraHillPotential a ha).val
      (realSobolevMiuraHillPotential a ha).property.1 (realSobolevMiuraHillPotential a ha).property.2 n hn : ℂ)
  root : ∀ᶠ p in 𝓝 (sobolevMiuraHillPotential a), hillL2DirichletCharacteristic p (energyBranch p) = 0
  real_match : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (realSobolevMiuraHillPotential a ha),
    energyBranch (SpectralWeight.one.toCoeff p.val) =
      (hillDirichletEnergy p.val p.property.1 p.property.2 n hn : ℂ)

theorem nonempty_miuraDirichletBranch (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (n : ℕ) (hn : 1 ≤ n) :
    Nonempty (MiuraDirichletBranch a ha n hn) := by
  obtain ⟨F,hF,hF0,hroot,hmatch⟩ := exists_hillDirichletEnergy_analytic_extension
    (realSobolevMiuraHillPotential a ha) n hn
  rw [realSobolevMiuraHillPotential_toCoeff] at hF hroot
  conv_lhs at hF0 => rw [realSobolevMiuraHillPotential_toCoeff]
  exact ⟨⟨F,hF,hF0,hroot,hmatch⟩⟩

namespace MiuraDirichletBranch
variable {a : ScalarDomain 2} {ha : ∀ n, a.val n = conj (a.val (-n))} {n : ℕ} {hn : 1 ≤ n}

def logNormingBranch (B : MiuraDirichletBranch a ha n hn) (p : Coeff 2) : ℂ :=
  log ((-1 : ℂ)^n*hillL2DirichletSlope p (B.energyBranch p))

theorem unit_energy_derivative (B : MiuraDirichletBranch a ha n hn) :
    HasFDerivAt (fun b => B.energyBranch (Coeff.periodDouble b))
      (reflectedHilbertPairing (scalarInclusion
        (sobolevHillTestInclusion (hillDirichletNativeGradient (realSobolevMiuraHillPotential a ha) n hn))))
      (sobolevMiuraUnitPotential a) := by
  have h := hasFDerivAt_hillDirichlet_unit_branch (realSobolevMiuraHillPotential a ha) n hn B.energyBranch
    (by rw [realSobolevMiuraHillPotential_toCoeff];exact B.analytic)
    (by conv_lhs => rw [realSobolevMiuraHillPotential_toCoeff]
        exact B.value)
    (by rw [realSobolevMiuraHillPotential_toCoeff];exact B.root)
  rw [realSobolevMiuraHillPotential_periodHalve] at h
  exact h

theorem unit_logNorming_derivative (B : MiuraDirichletBranch a ha n hn) :
    HasFDerivAt (fun b => B.logNormingBranch (Coeff.periodDouble b))
      (reflectedHilbertPairing (scalarInclusion
        (sobolevHillTestInclusion (hillLogNormingNativeGradient (realSobolevMiuraHillPotential a ha) n hn))))
      (sobolevMiuraUnitPotential a) := by
  have h := hasFDerivAt_hillLogNorming_unit_branch (realSobolevMiuraHillPotential a ha) n hn B.energyBranch
    (by rw [realSobolevMiuraHillPotential_toCoeff];exact B.analytic)
    (by conv_lhs => rw [realSobolevMiuraHillPotential_toCoeff]
        exact B.value)
    (by rw [realSobolevMiuraHillPotential_toCoeff];exact B.root)
  rw [realSobolevMiuraHillPotential_periodHalve] at h
  exact h

def energyGradient (B : MiuraDirichletBranch a ha n hn) :
    SobolevGardnerGradientAt (fun b => B.energyBranch (sobolevMiuraHillPotential b)) a :=
  miuraSobolevPullbackGradient (fun p => B.energyBranch (Coeff.periodDouble p)) a
    (hillDirichletNativeGradient (realSobolevMiuraHillPotential a ha) n hn) B.unit_energy_derivative

def logNormingGradient (B : MiuraDirichletBranch a ha n hn) :
    SobolevGardnerGradientAt (fun b => B.logNormingBranch (sobolevMiuraHillPotential b)) a :=
  miuraSobolevPullbackGradient (fun p => B.logNormingBranch (Coeff.periodDouble p)) a
    (hillLogNormingNativeGradient (realSobolevMiuraHillPotential a ha) n hn) B.unit_logNorming_derivative

theorem energyGradient_bracket (B : MiuraDirichletBranch a ha n hn) {m : ℕ} {hm : 1 ≤ m}
    (C : MiuraDirichletBranch a ha m hm) : B.energyGradient.bracket C.energyGradient = 0 := by
  have h := sobolevMiuraPullbackGradient_bracket_eq_Magri _ _ a _ _
    B.unit_energy_derivative C.unit_energy_derivative
  rw [← realSobolevMiuraHillPotential_periodHalve a ha,hillNativeDirichlet_Magri_bracket] at h
  exact h

theorem energyGradient_logNormingGradient_bracket (B : MiuraDirichletBranch a ha n hn)
    {m : ℕ} {hm : 1 ≤ m} (C : MiuraDirichletBranch a ha m hm) :
    B.energyGradient.bracket C.logNormingGradient =
      if n = m then -2*(hillDirichletEnergy (realSobolevMiuraHillPotential a ha).val
        (realSobolevMiuraHillPotential a ha).property.1 (realSobolevMiuraHillPotential a ha).property.2 n hn : ℂ) else 0 := by
  have h := sobolevMiuraPullbackGradient_bracket_eq_Magri _ _ a _ _
    B.unit_energy_derivative C.unit_logNorming_derivative
  rw [← realSobolevMiuraHillPotential_periodHalve a ha,hillNativeDirichlet_logNorming_Magri_bracket] at h
  exact h

theorem logNormingGradient_energyGradient_bracket (B : MiuraDirichletBranch a ha n hn)
    {m : ℕ} {hm : 1 ≤ m} (C : MiuraDirichletBranch a ha m hm) :
    B.logNormingGradient.bracket C.energyGradient =
      if n = m then 2*(hillDirichletEnergy (realSobolevMiuraHillPotential a ha).val
        (realSobolevMiuraHillPotential a ha).property.1 (realSobolevMiuraHillPotential a ha).property.2 n hn : ℂ) else 0 := by
  have h := sobolevMiuraPullbackGradient_bracket_eq_Magri _ _ a _ _
    B.unit_logNorming_derivative C.unit_energy_derivative
  rw [← realSobolevMiuraHillPotential_periodHalve a ha,hillNativeLogNorming_dirichlet_Magri_bracket] at h
  exact h

theorem logNormingGradient_bracket (B : MiuraDirichletBranch a ha n hn) {m : ℕ} {hm : 1 ≤ m}
    (C : MiuraDirichletBranch a ha m hm) : B.logNormingGradient.bracket C.logNormingGradient = 0 := by
  have h := sobolevMiuraPullbackGradient_bracket_eq_Magri _ _ a _ _
    B.unit_logNorming_derivative C.unit_logNorming_derivative
  rw [← realSobolevMiuraHillPotential_periodHalve a ha,hillNativeLogNorming_Magri_bracket] at h
  exact h

end MiuraDirichletBranch
end NLS.MKdV
