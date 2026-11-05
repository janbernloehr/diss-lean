import NLS.Poisson.GardnerHamiltonianHilbert
import NLS.KdV.HillHminusOriginalSource
import NLS.KdV.HillUnitWeightLift
import NLS.Poisson.GardnerHamiltonianZeroMode

noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.KdV

/-- The actual Gardner Hamiltonian direction, realized in the ORIGINAL
complex even weighted L2 source space without any change of coefficients. -/
def hillGardnerOriginalHilbertDirection (L : PeriodOneHminusOne →L[ℂ] ℂ) :
    WeightedCoeff SpectralWeight.one.toWeight 2 :=
  hillUnitWeightLift 2 (hillNativeHilbertDirection (NLS.Poisson.gardnerHamiltonianHilbertDirection L))

theorem hillGardnerOriginalHilbertDirection_even (L : PeriodOneHminusOne →L[ℂ] ℂ) :
    SpectralWeight.one.toCoeff (hillGardnerOriginalHilbertDirection L) ∈ Coeff.paritySubspace 0 := by
  rw [hillGardnerOriginalHilbertDirection,toCoeff_hillUnitWeightLift,hillNativeHilbertDirection_eq_periodDouble]
  exact Coeff.periodDouble_mem _

theorem hillGardnerOriginalHilbertDirection_source (L : PeriodOneHminusOne →L[ℂ] ℂ) :
    hillOriginalHminusSource (hillGardnerOriginalHilbertDirection L) =
      NLS.Poisson.gardnerHamiltonianDirection L := by
  calc
    _ = NLS.Poisson.hilbertToHminus (NLS.Poisson.gardnerHamiltonianHilbertDirection L) := by
      apply Subtype.ext
      funext k
      simp only [hillOriginalHminusSource_apply,hillGardnerOriginalHilbertDirection,
        hillUnitWeightLift_apply,hillNativeHilbertDirection_eq_periodDouble,
        NLS.Poisson.hilbertToHminus_apply]
      exact Coeff.periodDouble_even _ k
    _ = _ := NLS.Poisson.gardnerHamiltonianHilbertDirection_inclusion L

theorem hillGardnerOriginalHilbertDirection_mean_zero (L : PeriodOneHminusOne →L[ℂ] ℂ) :
    (hillGardnerOriginalHilbertDirection L).val 0 = 0 := by
  have he := congrArg (fun a : PeriodOneHminusOne => a.val 0)
    (hillGardnerOriginalHilbertDirection_source L)
  simpa only [hillOriginalHminusSource_apply,mul_zero,
    NLS.Poisson.gardnerHamiltonianDirection_zero_mode] using he

end NLS.KdV
