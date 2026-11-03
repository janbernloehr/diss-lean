import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import NLS.KdV.HillHminusOneMiuraResidueHilbert
import NLS.ZakharovShabat.SourcePsiCriticalAbsoluteInterpolation

/-! # Actual absolutely convergent energy principal-part series

The two original critical interpolation sums combine under the exact
shifted-square pullback. Their actual absolute convergence proves the
energy resolvent representation, with no prescribed Mittag-Leffler sum.
-/
noncomputable section
open Set Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV

def hillHminusMiuraSignedEnergyPrincipalTerm (C : HillHminusMiuraChart)
    (s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n) (n : ℤ)
    (q : PeriodOneHminusOne) (m : ℤ) (energy : ℂ) : ℂ :=
  let β := canonicalCriticalPoints (by simp) (by norm_num)
    (periodOnePotential (C.criticalSource q)) (periodOnePotential_mem _) m
  (2*β)*hillHminusMiuraSignedCriticalResidue C s n q m / (energy+C.energyShift-β^2)

theorem hillHminusMiura_signed_energy_principal_series (C : HillHminusMiuraChart)
    (s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n) (n : ℤ)
    (q : PeriodOneHminusOne) (hq : q ∈ C.domain)
    (hr : IsRealType (CoeffPair.toMax 2 (C.criticalSource q))) (energy : ℂ)
    (hc : energy ≠ -C.energyShift) (hD : deriv (hillHminusDiscriminant q) energy ≠ 0) :
    Summable (fun m : ℤ => ‖hillHminusMiuraSignedEnergyPrincipalTerm C s n q m energy‖) ∧
      (∑' m : ℤ, hillHminusMiuraSignedEnergyPrincipalTerm C s n q m energy) =
        hillHminusMiuraEnergyPsi C s n (energy,q)/deriv (hillHminusDiscriminant q) energy := by
  let φ := C.criticalSource q
  let a : Coeff 2 := s n φ
  let z := sqrt (energy+C.energyShift)
  let β := canonicalCriticalPoints (by simp) (by norm_num) (periodOnePotential φ) (periodOnePotential_mem φ)
  have he : z^2-C.energyShift = energy := by dsimp only [z]; rw [sq_sqrt,add_sub_cancel_right]
  have hz : z ≠ 0 := by
    intro h
    apply hc
    simpa only [h,zero_pow (by norm_num : (2:ℕ) ≠ 0),zero_sub] using he.symm
  have hN : deriv (canonicalDiscriminant (by simp) (periodOnePotential φ)) z ≠ 0 := by
    rw [C.frequency_derivative_eq q hq,he]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hz) hD
  have hodd : deriv (canonicalDiscriminant (by simp) (periodOnePotential φ)) (-z) =
      -deriv (canonicalDiscriminant (by simp) (periodOnePotential φ)) z := by
    exact deriv_neg_argument_of_even _ (hillMiuraFrequencyTrace_even (C.lift q)) z
  have hNm : deriv (canonicalDiscriminant (by simp) (periodOnePotential φ)) (-z) ≠ 0 := by
    rw [hodd]
    exact neg_ne_zero.mpr hN
  have hpart (m : ℤ) : hillHminusMiuraSignedEnergyPrincipalTerm C s n q m energy =
      sourcePsiCriticalInterpolationTerm (by simp) (by norm_num) n a φ m z+
        sourcePsiCriticalInterpolationTerm (by simp) (by norm_num) n a φ m (-z) := by
    have hb := canonicalCriticalPoints_is_critical (by simp) (by norm_num)
      (periodOnePotential φ) (periodOnePotential_mem φ) m
    have hzb : z-β m ≠ 0 := sub_ne_zero.mpr (by intro h; exact hN (h ▸ hb))
    have hmzb : -z-β m ≠ 0 := sub_ne_zero.mpr (by intro h; exact hNm (h ▸ hb))
    have hzplus : z+β m ≠ 0 := by
      intro h
      apply hmzb
      linear_combination -h
    have hsq : z^2-β m^2 ≠ 0 := by
      rw [show z^2-β m^2 = (z-β m)*(z+β m) by ring]
      exact mul_ne_zero hzb hzplus
    have hzsq : z^2 = energy+C.energyShift := sq_sqrt _
    change (2*β m)*sourcePsiCriticalResidue (by simp) (by norm_num) n a φ m /
      (energy+C.energyShift-β m^2) =
      sourcePsiCriticalResidue (by simp) (by norm_num) n a φ m/(z-β m)+
        sourcePsiCriticalResidue (by simp) (by norm_num) n a φ m/(-z-β m)
    rw [← hzsq]
    field_simp [hzb,hmzb,hsq]
    ring
  have hs := summable_norm_sourcePsiCriticalInterpolation (by simp) (by norm_num) n a φ hr z
  have hm := summable_norm_sourcePsiCriticalInterpolation (by simp) (by norm_num) n a φ hr (-z)
  refine ⟨(hs.add hm).of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_),?_⟩
  · rw [hpart]
    exact norm_add_le _ _
  · calc
      (∑' m : ℤ, hillHminusMiuraSignedEnergyPrincipalTerm C s n q m energy) =
          ∑' m : ℤ, (sourcePsiCriticalInterpolationTerm (by simp) (by norm_num) n a φ m z+
            sourcePsiCriticalInterpolationTerm (by simp) (by norm_num) n a φ m (-z)) := tsum_congr hpart
      _ = (∑' m : ℤ, sourcePsiCriticalInterpolationTerm (by simp) (by norm_num) n a φ m z)+
          ∑' m : ℤ, sourcePsiCriticalInterpolationTerm (by simp) (by norm_num) n a φ m (-z) :=
        hs.of_norm.tsum_add hm.of_norm
      _ = sourcePsiCandidate n (z,a)/deriv (canonicalDiscriminant (by simp) (periodOnePotential φ)) z+
          sourcePsiCandidate n (-z,a)/deriv (canonicalDiscriminant (by simp) (periodOnePotential φ)) (-z) := by
        rw [sourcePsiCriticalInterpolation_tsum_eq_quotient (by simp) (by norm_num) n a φ hr z hN,
          sourcePsiCriticalInterpolation_tsum_eq_quotient (by simp) (by norm_num) n a φ hr (-z) hNm]
      _ = (sourcePsiCandidate n (z,a)-sourcePsiCandidate n (-z,a))/
          deriv (canonicalDiscriminant (by simp) (periodOnePotential φ)) z := by rw [hodd,div_neg]; ring
      _ = hillHminusMiuraEnergyPsi C s n (energy,q)/deriv (hillHminusDiscriminant q) energy := by
        have h := hillHminusMiuraEnergyPsi_derivative_ratio_pullback C s n q hq z hz
        rw [he] at h
        exact h.symm

theorem hillHminusMiuraSignedEnergyPrincipalTerm_pair (C : HillHminusMiuraChart)
    (s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n) (n : ℤ)
    (q : PeriodOneHminusOne) (hq : q ∈ C.domain)
    (hr : IsRealType (CoeffPair.toMax 2 (C.criticalSource q))) (j : ℕ+) (energy : ℂ) :
    hillHminusMiuraSignedEnergyPrincipalTerm C s n q (j:ℤ) energy+
      hillHminusMiuraSignedEnergyPrincipalTerm C s n q (-(j:ℤ)) energy =
        hillHminusMiuraEnergyCriticalResidue C s n q j/(energy-C.energyCritical q j) := by
  have href := canonicalCriticalPoints_neg_of_discriminant_even_of_realType
    (by simp) (by norm_num) _ (periodOnePotential_mem _) (isRealType_periodOnePotential _ hr)
    (hillMiuraFrequencyTrace_even (C.lift q)) (j:ℤ)
  unfold hillHminusMiuraSignedEnergyPrincipalTerm
  dsimp only
  rw [href,neg_sq,hillHminusMiuraEnergyCriticalResidue_eq_signed C s n q hq hr j]
  change (2*C.frequencyCritical q j)*hillHminusMiuraSignedCriticalResidue C s n q (j:ℤ)/
      (energy+C.energyShift-C.frequencyCritical q j^2)+
    (2*(-C.frequencyCritical q j))*hillHminusMiuraSignedCriticalResidue C s n q (-(j:ℤ))/
      (energy+C.energyShift-C.frequencyCritical q j^2) = _
  rw [← add_div]
  change _ = _/(energy-(C.frequencyCritical q j^2-C.energyShift))
  rw [show energy-(C.frequencyCritical q j^2-C.energyShift) =
    energy+C.energyShift-C.frequencyCritical q j^2 by ring]
  congr 1
  ring

theorem hillHminusMiura_energy_principal_series (C : HillHminusMiuraChart)
    (s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n) (n : ℤ)
    (q : PeriodOneHminusOne) (hq : q ∈ C.domain)
    (hr : IsRealType (CoeffPair.toMax 2 (C.criticalSource q))) (energy : ℂ)
    (hc : energy ≠ -C.energyShift) (hD : deriv (hillHminusDiscriminant q) energy ≠ 0) :
    Summable (fun j : ℕ+ => ‖hillHminusMiuraEnergyCriticalResidue C s n q j /
      (energy-C.energyCritical q j)‖) ∧
      (∑' j : ℕ+, hillHminusMiuraEnergyCriticalResidue C s n q j /
        (energy-C.energyCritical q j)) =
        hillHminusMiuraEnergyPsi C s n (energy,q)/deriv (hillHminusDiscriminant q) energy := by
  let f : ℤ → ℂ := fun m => hillHminusMiuraSignedEnergyPrincipalTerm C s n q m energy
  obtain ⟨hs,he⟩ := hillHminusMiura_signed_energy_principal_series C s n q hq hr energy hc hD
  have hinj : Function.Injective (fun j : ℕ+ => (j:ℤ)) := by
    intro i j h
    dsimp only at h
    simp only [Int.natCast_inj] at h
    exact Subtype.ext h
  have hneg : Function.Injective (fun j : ℕ+ => -(j:ℤ)) := by intro i j h; exact hinj (neg_injective h)
  have hp : Summable (fun j : ℕ+ => ‖f (j:ℤ)‖) := hs.comp_injective hinj
  have hm : Summable (fun j : ℕ+ => ‖f (-(j:ℤ))‖) := hs.comp_injective hneg
  have hpair (j : ℕ+) : f (j:ℤ)+f (-(j:ℤ)) =
      hillHminusMiuraEnergyCriticalResidue C s n q j/(energy-C.energyCritical q j) :=
    hillHminusMiuraSignedEnergyPrincipalTerm_pair C s n q hq hr j energy
  have hz : f 0 = 0 := by
    unfold f hillHminusMiuraSignedEnergyPrincipalTerm
    rw [canonicalCriticalPoints_zero_of_discriminant_even_of_realType (by simp) (by norm_num)
      _ (periodOnePotential_mem _) (isRealType_periodOnePotential _ hr) (hillMiuraFrequencyTrace_even (C.lift q))]
    simp only [mul_zero,zero_mul,zero_div]
  refine ⟨(hp.add hm).of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => ?_),?_⟩
  · rw [← hpair]
    exact norm_add_le _ _
  · have hsplit := tsum_int_eq_zero_add_tsum_pnat (f := f) hs.of_norm
    rw [hz,zero_add,← hp.of_norm.tsum_add hm.of_norm] at hsplit
    rw [tsum_congr hpair] at hsplit
    exact hsplit.symm.trans he

end NLS.KdV
