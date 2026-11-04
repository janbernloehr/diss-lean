import NLS.KdV.HillMiuraFreeIsospectral
import NLS.KdV.HillDiscriminantJointCotangent
import NLS.Poisson.GardnerRealForm
import NLS.ZakharovShabat.RealDiscriminantValues

/-! The actual Hill discriminant intertwines energy conjugation at
every physical real H-minus-one source. Its real-energy cotangents
and native Gardner vectors consequently preserve the real form. -/
noncomputable section
open Set Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.KdV

theorem hillHminusDiscriminant_conj_of_real (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (E : ℂ) :
    hillHminusDiscriminant q (conj E)=conj (hillHminusDiscriminant q E) := by
  obtain ⟨B,hq⟩ := exists_hillHminusMiuraActionBall q hr
  let c : ℂ := B.shift
  let z := Complex.sqrt (E+c)
  have hz : z^2-c=E := by dsimp only [z]; rw [complex_sqrt_sq]; ring
  have hzc : (conj z)^2-c=conj E := by
    rw [← map_pow]
    have hs : z^2=E+c := by linear_combination hz
    rw [hs,map_add]
    simp only [c,conj_ofReal,add_sub_cancel_right]
  have he := conj_canonicalDiscriminant_of_realType (by norm_num) (by norm_num)
    (periodOnePotential (B.diracSource q)) (periodOnePotential_mem _)
    (isRealType_periodOnePotential _ (B.diracSource_real q hq hr)) z
  rw [B.diracSource_discriminant_eq q hq z,B.diracSource_discriminant_eq q hq (conj z),hz,hzc] at he
  exact he.symm

theorem hillHminusDiscriminant_im_eq_zero_of_real (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (E : ℝ) : (hillHminusDiscriminant q (E:ℂ)).im=0 := by
  have he := hillHminusDiscriminant_conj_of_real q hr (E:ℂ)
  rw [conj_ofReal] at he
  exact conj_eq_iff_im.mp he.symm

theorem hillHminusDiscriminant_Hamiltonian_real (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (E : ℝ) :
    IsRealPeriodOneHminusOne (NLS.Poisson.gardnerHamiltonianVector
      (fun p => hillHminusDiscriminant p (E:ℂ)) q) :=
  NLS.Poisson.gardnerHamiltonianVector_real_of_eventually_real _ q hr
    (analyticOnNhd_hillHminusDiscriminant_source (E:ℂ) q (mem_univ _))
    (Eventually.of_forall (fun p hpr => hillHminusDiscriminant_im_eq_zero_of_real p hpr E))

end NLS.KdV
