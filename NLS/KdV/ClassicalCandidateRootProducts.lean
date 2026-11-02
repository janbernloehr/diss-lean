import NLS.KdV.ClassicalNormalizedSimpleZeros
import NLS.SequenceSpaces.Reflection
import NLS.ZakharovShabat.SourceGapInterpolationProduct

/-! # Entire signed products for the selected candidate roots

The selected critical roots plus the antisymmetric Hilbert displacement
have actual l2 free-lattice displacement. Their complete signed product
converges locally uniformly and has precisely these simple roots.
The zero root and the omitted ±n placeholders are still included;
this is not yet the source's omitted normalized Psi_n product identity.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat
namespace NLS.KdV

def classicalHillSignedCandidate (N : ℕ)
    (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) (j : ℤ) : ℂ :=
  classicalHillSignedCritical N t.2 j+t.1 j-t.1 (-j)

theorem classicalHillSignedCandidate_zero (N : ℕ)
    (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) : classicalHillSignedCandidate N t 0 = 0 := by
  simp only [classicalHillSignedCandidate,classicalHillSignedCritical_zero,neg_zero,zero_add,sub_self]

theorem classicalHillSignedCandidate_positive (N : ℕ)
    (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) (haux : ∀ j ≤ (0 : ℤ), t.1 j = 0) (k : ℕ+) :
    classicalHillSignedCandidate N t (k : ℤ) = classicalHillCandidateFrequency N k t := by
  have hk : (0 : ℤ) < k := by exact_mod_cast k.pos
  rw [classicalHillSignedCandidate,classicalHillSignedCritical_positive,haux (-(k : ℤ)) (by omega),sub_zero]
  rfl

theorem classicalHillSignedCandidate_negative (N : ℕ)
    (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) (haux : ∀ j ≤ (0 : ℤ), t.1 j = 0) (k : ℕ+) :
    classicalHillSignedCandidate N t (-(k : ℤ)) = -classicalHillCandidateFrequency N k t := by
  have hk : (0 : ℤ) < k := by exact_mod_cast k.pos
  rw [classicalHillSignedCandidate,classicalHillSignedCritical_negative,haux (-(k : ℤ)) (by omega),neg_neg,add_zero]
  dsimp only [classicalHillCandidateFrequency,classicalHillCriticalFrequency]
  ring

namespace ClassicalAllContourPeriodData
variable {N : ℕ} {V : Set (NLS.LinearVolterra.Curve ℂ)} {A : ℝ}
variable (D : ClassicalAllContourPeriodData N V A)
include D

theorem signedCandidate_displacement_memlp
    (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) (hq : t.2 ∈ V) :
    Memℓp (fun j => classicalHillSignedCandidate N t j-(Real.pi : ℂ)*j) 2 := by
  have hc := (D.signedCritical_product t.2 hq).2.1
  have hr : Memℓp (fun j : ℤ => t.1 (-j)) 2 := lp.memℓp (NLS.Coeff.reflection t.1)
  have hs := hc.add ((lp.memℓp t.1).sub hr)
  convert hs using 1
  funext j
  dsimp only [classicalHillSignedCandidate]
  simp only [Pi.add_apply,Pi.sub_apply]
  ring

theorem signedCandidate_close
    (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) (ht : t ∈ classicalHillCandidateDomain V) (j : ℤ) :
    ‖classicalHillSignedCandidate N t j-(Real.pi : ℂ)*j‖ < Real.pi/4 := by
  have hc := D.signedCritical_close t.2 ht.2 j
  have hx : ‖t.1‖ < Real.pi/16 := by simpa only [mem_ball,dist_zero_right] using ht.1
  have hj := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) t.1 j
  have hneg := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) t.1 (-j)
  have he : classicalHillSignedCandidate N t j-(Real.pi : ℂ)*j =
      (classicalHillSignedCritical N t.2 j-(Real.pi : ℂ)*j)+(t.1 j-t.1 (-j)) := by
    dsimp only [classicalHillSignedCandidate]
    ring
  rw [he]
  exact (norm_add_le _ _).trans_lt (by
    have hb := norm_sub_le (t.1 j) (t.1 (-j))
    linarith [Real.pi_pos])

theorem signedCandidate_injective
    (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) (ht : t ∈ classicalHillCandidateDomain V) :
    Function.Injective (classicalHillSignedCandidate N t) := by
  intro j m he
  by_contra hjm
  have hgap : (1 : ℝ) ≤ |((j-m : ℤ) : ℝ)| := by exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hjm)
  have hj := D.signedCandidate_close t ht j
  have hm := D.signedCandidate_close t ht m
  have hrev : ‖(Real.pi : ℂ)*j-classicalHillSignedCandidate N t j‖ < Real.pi/4 := by rwa [norm_sub_rev]
  have hb := norm_sub_le_norm_sub_add_norm_sub ((Real.pi : ℂ)*j)
    (classicalHillSignedCandidate N t j) ((Real.pi : ℂ)*m)
  rw [norm_free_center_sub] at hb
  rw [he] at hb hrev
  nlinarith [Real.pi_pos,mul_le_mul_of_nonneg_left hgap Real.pi_pos.le]

/-- The whole signed candidate product is constructed, with locally
uniform literal cutoffs and its exact simple zero set. Deleting the zero
and omitted-mode factors and identifying Psi_n are separate obligations. -/
theorem signedCandidate_product
    (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) (ht : t ∈ classicalHillCandidateDomain V) :
    AnalyticOnNhd ℂ (entireSingleSpectralProduct (classicalHillSignedCandidate N t)) univ ∧
    TendstoLocallyUniformlyOn
      (fun M z => singleSpectralPartialProduct (classicalHillSignedCandidate N t) z M)
      (entireSingleSpectralProduct (classicalHillSignedCandidate N t)) atTop univ ∧
    (∀ z : ℂ, entireSingleSpectralProduct (classicalHillSignedCandidate N t) z = 0 ↔
      ∃ j : ℤ, classicalHillSignedCandidate N t j = z) ∧
    ∀ z : ℂ, entireSingleSpectralProduct (classicalHillSignedCandidate N t) z = 0 →
      deriv (entireSingleSpectralProduct (classicalHillSignedCandidate N t)) z ≠ 0 := by
  have hlp := D.signedCandidate_displacement_memlp t ht.2
  exact ⟨analyticOnNhd_entireSingleSpectralProduct (by norm_num : (2 : ENNReal) ≠ ⊤) _ hlp,
    tendstoLocallyUniformlyOn_entireSingleSpectralProduct (by norm_num : (2 : ENNReal) ≠ ⊤) _ hlp,
    entireSingleSpectralProduct_eq_zero_iff_of_lp (by norm_num : (2 : ENNReal) ≠ ⊤) _ hlp,
    entireSingleSpectralProduct_simple_zeros_of_injective (by norm_num : (2 : ENNReal) ≠ ⊤)
      (by norm_num : 1 < (2 : ENNReal)) _ hlp (D.signedCandidate_injective t ht)⟩

end ClassicalAllContourPeriodData
end NLS.KdV
