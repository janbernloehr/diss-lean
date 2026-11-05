import NLS.MKdV.MiuraHillRealLabels
import NLS.KdV.HillDirichletLabels

/-! # Strict positivity of every original Dirichlet energy on the real Miura image

The bottom periodic energy may vanish. The first strict band inequality
places every Dirichlet energy strictly above that bottom, also when its
own periodic gap is closed. All original real H¹ profiles are included.
-/
noncomputable section
open Set Complex NLS.Fourier NLS.ZakharovShabat NLS.KdV
open scoped ComplexConjugate ENNReal
namespace NLS.MKdV

def realSobolevMiuraHillPotential (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) : RealPeriodOneHillPotential :=
  ⟨sobolevMiuraWeightedPotential a,by
    rw [toCoeff_sobolevMiuraWeightedPotential]
    exact ⟨sobolevMiuraHillPotential_even a,sobolevMiuraHillPotential_real a ha⟩⟩

theorem realSobolevMiuraHillPotential_toCoeff (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) :
    SpectralWeight.one.toCoeff (realSobolevMiuraHillPotential a ha).val = sobolevMiuraHillPotential a :=
  toCoeff_sobolevMiuraWeightedPotential a

theorem realSobolevMiuraHillPotential_periodHalve (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) :
    Coeff.periodHalve (SpectralWeight.one.toCoeff (realSobolevMiuraHillPotential a ha).val) =
      sobolevMiuraUnitPotential a := by
  rw [realSobolevMiuraHillPotential_toCoeff,sobolevMiuraHillPotential,Coeff.periodHalve_periodDouble]

theorem hillDirichletEnergy_Miura_pos (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (n : ℕ) (hn : 1 ≤ n) :
    0 < hillDirichletEnergy (realSobolevMiuraHillPotential a ha).val
      (realSobolevMiuraHillPotential a ha).property.1 (realSobolevMiuraHillPotential a ha).property.2 n hn := by
  let q := realSobolevMiuraHillPotential a ha
  have h0 : 0 ≤ hillRealLabels q.val q.property.1 q.property.2 0 := miuraHillLabels_nonnegative a ha 0
  have h01 := hillRealLabels_band_strict q.val q.property.1 q.property.2 0
  have h1n := monotone_hillRealLabels q.val q.property.1 q.property.2 (show 1 ≤ 2*n-1 by omega)
  have hmu := (hillDirichletEnergy_mem_gap q.val q.property.1 q.property.2 n hn).1
  exact lt_of_lt_of_le (lt_of_le_of_lt h0 (by simpa only [Nat.mul_zero,zero_add] using h01))
    (h1n.trans hmu)

end NLS.MKdV
