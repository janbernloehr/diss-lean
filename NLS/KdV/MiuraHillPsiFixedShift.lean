import NLS.KdV.MiuraHillPsiEnergyRoot
import NLS.KdV.HminusOneMiuraIsospectral
import NLS.ZakharovShabat.SourcePsiEnergyIsospectral

/-! Numerator independence for arbitrary real L2 Miura lifts with the
SAME physical energy shift. Different verified simultaneous families
also agree. No independence under a change of shift is asserted here. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV

theorem hillMiuraRealSource_isospectral_of_same_shift
    (q : PeriodOneHminusOne) (u v : PeriodOneRealL2) (c : ℂ)
    (hu : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 c))
    (hv : periodOneMiura v.val = q+periodOneL2Inclusion (lp.single 2 0 c)) :
    hillMiuraRealSource u ∈ sourceIsospectralSet (by norm_num) (hillMiuraRealSource v) := by
  apply (mem_sourceIsospectralSet_iff_discriminant_eq (by norm_num) (by norm_num) _ _).mpr
  funext z
  exact (hillHminusDiscriminant_shifted_miura_square q u.val c z hu).symm.trans
    (hillHminusDiscriminant_shifted_miura_square q v.val c z hv)

namespace MiuraHillPsiFamily

theorem numerator_eq_of_real_same_shift (A B : MiuraHillPsiFamily)
    (q : PeriodOneHminusOne) (u v : PeriodOneRealL2) (c : ℂ)
    (hu : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 c))
    (hv : periodOneMiura v.val = q+periodOneL2Inclusion (lp.single 2 0 c)) (n : ℕ+) (E : ℂ) :
    A.numerator n (E,u.val) = B.numerator n (E,v.val) :=
  A.verified.energyNumerator_eq_of_real_isospectral B.verified
    (hillMiuraRealSource v) (hillMiuraRealSource u)
    (hillMiuraRealSource_isospectral_of_same_shift q u v c hu hv) ((n:ℕ):ℤ) E

end MiuraHillPsiFamily
end NLS.KdV
