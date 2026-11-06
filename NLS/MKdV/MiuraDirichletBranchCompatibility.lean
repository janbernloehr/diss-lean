import NLS.MKdV.MiuraDirichletBranchGradients

/-! # Local branches agree with the original spectral data along real H¹ families -/
noncomputable section
open Set Complex Filter Topology
open NLS.ZakharovShabat NLS.KdV
open scoped ComplexConjugate
namespace NLS.MKdV

theorem continuous_realSobolevMiuraHillPotential_family {T : Type*} [TopologicalSpace T]
    (A : T → ScalarDomain 2) (hA : Continuous A)
    (hreal : ∀ t n, (A t).val n = conj ((A t).val (-n))) :
    Continuous (fun t => realSobolevMiuraHillPotential (A t) (hreal t)) := by
  have hc : Continuous sobolevMiuraHillPotential :=
    continuous_iff_continuousAt.mpr (fun a => (analyticAt_sobolevMiuraHillPotential a).continuousAt)
  have hw := (WeightedCoeff.weightIsometry SpectralWeight.one.toWeight 2).symm.continuous.comp (hc.comp hA)
  exact hw.subtype_mk _

namespace MiuraDirichletBranch
variable {a : ScalarDomain 2} {ha : ∀ n, a.val n = conj (a.val (-n))} {n : ℕ} {hn : 1 ≤ n}

theorem eventually_real_family_match (B : MiuraDirichletBranch a ha n hn)
    {T : Type*} [TopologicalSpace T] (A : T → ScalarDomain 2) (hA : Continuous A)
    (hreal : ∀ t j, (A t).val j = conj ((A t).val (-j))) (t0 : T) (h0 : A t0 = a) :
    ∀ᶠ t in 𝓝 t0,
      B.energyBranch (sobolevMiuraHillPotential (A t)) =
        (hillDirichletEnergy (realSobolevMiuraHillPotential (A t) (hreal t)).val
          (realSobolevMiuraHillPotential (A t) (hreal t)).property.1
          (realSobolevMiuraHillPotential (A t) (hreal t)).property.2 n hn : ℂ) ∧
      B.logNormingBranch (sobolevMiuraHillPotential (A t)) =
        (hillDirichletLogMultiplier (realSobolevMiuraHillPotential (A t) (hreal t)).val
          (realSobolevMiuraHillPotential (A t) (hreal t)).property.1
          (realSobolevMiuraHillPotential (A t) (hreal t)).property.2 n hn : ℂ) := by
  have hc := continuous_realSobolevMiuraHillPotential_family A hA hreal
  have he : realSobolevMiuraHillPotential (A t0) (hreal t0) = realSobolevMiuraHillPotential a ha := by
    apply Subtype.ext
    exact congrArg sobolevMiuraWeightedPotential h0
  have ht : Tendsto (fun t => realSobolevMiuraHillPotential (A t) (hreal t))
      (𝓝 t0) (𝓝 (realSobolevMiuraHillPotential (A t0) (hreal t0))) := hc.tendsto t0
  rw [he] at ht
  filter_upwards [ht.eventually B.real_match] with t hp
  let q := realSobolevMiuraHillPotential (A t) (hreal t)
  have henergy : B.energyBranch (sobolevMiuraHillPotential (A t)) =
      (hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ) :=
    (congrArg B.energyBranch (realSobolevMiuraHillPotential_toCoeff (A t) (hreal t)).symm).trans hp
  refine ⟨henergy,?_⟩
  change log ((-1 : ℂ)^n*hillL2DirichletSlope (sobolevMiuraHillPotential (A t))
    (B.energyBranch (sobolevMiuraHillPotential (A t)))) = _
  rw [henergy,← realSobolevMiuraHillPotential_toCoeff (A t) (hreal t),← hillDirichletMultiplier_ofReal,
    ← Complex.ofReal_log (hillDirichletMultiplier_pos q.val q.property.1 q.property.2 n hn).le]
  rfl

end MiuraDirichletBranch
end NLS.MKdV
