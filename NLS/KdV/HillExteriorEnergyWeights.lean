import NLS.KdV.HillContourHilbertPsiBounds
import NLS.KdV.HillGapNumeratorDecay
import NLS.ZakharovShabat.FreeResolventExteriorLimit
import NLS.SequenceSpaces.PositiveDeletedProjection

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



def hillExteriorInverseFrequency (z : ℂ) (hz : z ∉ freeLattice) : Coeff 2 :=
  ⟨fun m => (z-(Real.pi : ℂ)*m)⁻¹,inverse_denominator_memlp (by norm_num : 1 < (2 : ℝ≥0∞)) z hz⟩

theorem norm_hillExteriorInverseFrequency_le
    (z : ℂ) (hz : z ∉ freeLattice)
    (hsep : ∀ m : ℤ, Real.pi/4 ≤ ‖z-(Real.pi : ℂ)*m‖) :
    ‖hillExteriorInverseFrequency z hz‖ ≤ WeightedCoeff.sobolevEmbeddingConstant 2 (by norm_num)/(Real.pi/4) := by
  obtain ⟨j,hj⟩ := exists_centered_real_part z
  have hb := scalarFreeL1Bound_le_verticalStrip (p := 2) (by norm_num) z hz
    (by positivity : 0 < Real.pi/4) le_rfl ⟨hj,hsep j⟩
  unfold scalarFreeL1Bound conjugateInverseSymbol at hb
  have he : ∀ (p : ℝ≥0∞) (hp : 1 < p), p = 2 →
      ‖(⟨fun m : ℤ => (z-(Real.pi : ℂ)*m)⁻¹,inverse_denominator_memlp hp z hz⟩ : Coeff p)‖ =
        ‖hillExteriorInverseFrequency z hz‖ := by
    rintro p hp rfl
    rfl
  have hq : (2 : ℝ≥0∞).conjExponent = 2 := ENNReal.HolderConjugate.unique 2 _ 2
  rw [he _ (by rw [hq]; norm_num) hq] at hb
  exact hb

def hillExteriorEnergyWeight (n : ℕ) (z : ℂ) (hz : z ∉ freeLattice) : Coeff 2 :=
  Coeff.positiveDeletedProjection 2 (n : ℤ)
    ((-1/(2*(Real.pi : ℂ))) • (hillExteriorInverseFrequency z hz+
      hillExteriorInverseFrequency (-z) (neg_notMem_freeLattice hz)))

theorem hillExteriorEnergyWeight_apply (n : ℕ) (z : ℂ) (hz : z ∉ freeLattice) (m : ℤ) :
    hillExteriorEnergyWeight n z hz m = hillFreeContourWeightSymbol n (z^2) m := by
  rw [hillExteriorEnergyWeight,Coeff.positiveDeletedProjection_apply]
  unfold hillFreeContourWeightSymbol
  split_ifs
  · change (-1/(2*(Real.pi : ℂ)))*((z-(Real.pi : ℂ)*m)⁻¹+(-z-(Real.pi : ℂ)*m)⁻¹) =
      (m : ℂ)/((freeHillValue m : ℂ)-z^2)
    have hp : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    have h1 : z-(Real.pi : ℂ)*m ≠ 0 := sub_ne_zero.mpr (fun he => hz ⟨m,he.symm⟩)
    have h2 : -z-(Real.pi : ℂ)*m ≠ 0 := sub_ne_zero.mpr (fun he => (neg_notMem_freeLattice hz) ⟨m,he.symm⟩)
    have hfree : (freeHillValue m : ℂ) = ((Real.pi : ℂ)*(m : ℂ))^2 := by
      simp only [freeHillValue,ofReal_mul,ofReal_pow,ofReal_intCast]
      ring
    rw [hfree]
    have hden : ((Real.pi : ℂ)*(m : ℂ))^2-z^2 ≠ 0 := by
      have he : ((Real.pi : ℂ)*(m : ℂ))^2-z^2 = (z-(Real.pi : ℂ)*m)*(-z-(Real.pi : ℂ)*m) := by ring
      rw [he]
      exact mul_ne_zero h1 h2
    apply (eq_div_iff hden).mpr
    field_simp [h1,h2]
    ring
  · rfl

theorem norm_hillExteriorEnergyWeight_le
    (n : ℕ) (z : ℂ) (hz : z ∉ freeLattice)
    (hsep : ∀ m : ℤ, Real.pi/4 ≤ ‖z-(Real.pi : ℂ)*m‖) :
    ‖hillExteriorEnergyWeight n z hz‖ ≤
      (1/Real.pi)*(WeightedCoeff.sobolevEmbeddingConstant 2 (by norm_num)/(Real.pi/4)) := by
  have hnegsep (m : ℤ) : Real.pi/4 ≤ ‖-z-(Real.pi : ℂ)*m‖ := by
    have ht := hsep (-m)
    simpa only [Int.cast_neg,mul_neg,sub_neg_eq_add,show -z-(Real.pi : ℂ)*m = -(z+(Real.pi : ℂ)*m) by ring,norm_neg] using ht
  have hproj : ‖hillExteriorEnergyWeight n z hz‖ ≤
      ‖(-1/(2*(Real.pi : ℂ))) • (hillExteriorInverseFrequency z hz+
        hillExteriorInverseFrequency (-z) (neg_notMem_freeLattice hz))‖ := by
    apply lp.norm_mono (x := hillExteriorEnergyWeight n z hz)
      (y := (-1/(2*(Real.pi : ℂ))) • (hillExteriorInverseFrequency z hz+
        hillExteriorInverseFrequency (-z) (neg_notMem_freeLattice hz))) (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro m
    rw [hillExteriorEnergyWeight,Coeff.positiveDeletedProjection_apply]
    split_ifs
    · exact le_rfl
    · rw [norm_zero]
      exact norm_nonneg _
  apply hproj.trans
  rw [norm_smul,norm_div,norm_neg,norm_one,norm_mul,norm_ofNat,norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  have hp := norm_hillExteriorInverseFrequency_le z hz hsep
  have hn := norm_hillExteriorInverseFrequency_le (-z) (neg_notMem_freeLattice hz) hnegsep
  have ht := norm_add_le (hillExteriorInverseFrequency z hz) (hillExteriorInverseFrequency (-z) (neg_notMem_freeLattice hz))
  calc
    _ ≤ (1/(2*Real.pi))*(2*(WeightedCoeff.sobolevEmbeddingConstant 2 (by norm_num)/(Real.pi/4))) := by
      gcongr
      linarith
    _ = _ := by ring

theorem hillExteriorEnergy_denominator_ne_zero (z : ℂ) (hz : z ∉ freeLattice) (m : ℤ) :
    (freeHillValue m : ℂ)-z^2 ≠ 0 := by
  have h1 : z-(Real.pi : ℂ)*m ≠ 0 := sub_ne_zero.mpr (fun he => hz ⟨m,he.symm⟩)
  have h2 : -z-(Real.pi : ℂ)*m ≠ 0 := sub_ne_zero.mpr (fun he => (neg_notMem_freeLattice hz) ⟨m,he.symm⟩)
  have he : (freeHillValue m : ℂ)-z^2 = (z-(Real.pi : ℂ)*m)*(-z-(Real.pi : ℂ)*m) := by
    simp only [freeHillValue,ofReal_mul,ofReal_pow,ofReal_intCast]
    ring
  rw [he]
  exact mul_ne_zero h1 h2

end NLS.KdV
