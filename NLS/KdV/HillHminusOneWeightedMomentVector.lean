import NLS.KdV.HillHminusOneWeightedPeriodInverse
import NLS.KdV.HillHminusOneUniformMomentBounds
import NLS.SequenceSpaces.HilbertMatrixTransposeAnalytic
import NLS.SequenceSpaces.PositiveDeletedProjectionBounds

/-! The actual second moments divided by their own index form ONE Hilbert
vector on every contour. It is the bounded bilinear transpose of the actual
one-weight normalization inverse, with the exact primitive factor 2*pi/3.
The whole-vector bounds retain the actual gap factor on the high tail. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
namespace NLS.KdV

def hillHminusWeightedSecondMomentVector (C : HillHminusMiuraChart) (N : ℕ)
    (Q : PeriodOneHminusOne → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2)) (k : ℕ+)
    (q : PeriodOneHminusOne) : NLS.Coeff 2 :=
  NLS.Coeff.positiveDeletedProjection 2 0
    (((2*(Real.pi : ℂ))/3) • NLS.Coeff.hilbertMatrixTranspose (Q q)
      (NLS.Coeff.multiplier NLS.Coeff.positiveIndexReciprocal (hillHminusMomentKernelVector C N k 2 q)))

@[simp] theorem hillHminusWeightedSecondMomentVector_nonpositive
    (C : HillHminusMiuraChart) (N : ℕ)
    (Q : PeriodOneHminusOne → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2)) (k : ℕ+)
    (q : PeriodOneHminusOne) (j : ℤ) (hj : j≤0) :
    hillHminusWeightedSecondMomentVector C N Q k q j=0 := by
  rw [hillHminusWeightedSecondMomentVector,NLS.Coeff.positiveDeletedProjection_apply,if_neg (by omega)]

namespace HillHminusUniformPeriodData
variable {C : HillHminusMiuraChart} {N M : ℕ} {V U : Set PeriodOneHminusOne} {A r B : ℝ}
variable (D : HillHminusUniformPeriodData C N V A)
include D

/-- Every positive coefficient is the SAME original normalized moment divided
by n, with no transpose conjugation, period rescaling or missing indices. -/
theorem weightedSecondMomentVector_positive
    (R Q : PeriodOneHminusOne → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (q : PeriodOneHminusOne) (hq : q∈V) (n k : ℕ+)
    (hcompat : ∀ j : ℤ, NLS.Coeff.positiveIndexWeight j*(R q (lp.single 2 (n : ℤ) 1)) j=
      (n : ℂ)*(Q q (lp.single 2 (n : ℤ) 1)) j) :
    hillHminusWeightedSecondMomentVector C N Q k q (n : ℤ)=
      hillHminusNormalizedMoment C N R n k 2 q/(n : ℂ) := by
  have hn : (0 : ℤ)<n := by exact_mod_cast n.pos
  have hn0 : (n : ℂ)≠0 := by exact_mod_cast n.pos.ne'
  have he : R q (lp.single 2 (n : ℤ) 1)=NLS.Coeff.multiplier NLS.Coeff.positiveIndexReciprocal
      ((n : ℂ) • Q q (lp.single 2 (n : ℤ) 1)) := by
    ext j
    rw [NLS.Coeff.multiplier_apply,NLS.Coeff.positiveIndexReciprocal_apply]
    change _=(NLS.Coeff.positiveIndexWeight j)⁻¹*((n : ℂ)*(Q q (lp.single 2 (n : ℤ) 1)) j)
    rw [←hcompat j]
    field_simp [NLS.Coeff.positiveIndexWeight_ne_zero]
  rw [hillHminusWeightedSecondMomentVector,NLS.Coeff.positiveDeletedProjection_apply,
    if_pos ⟨hn,ne_of_gt hn⟩]
  simp only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,NLS.Coeff.hilbertMatrixTranspose_apply]
  change ((2*(Real.pi : ℂ))/3)*NLS.Coeff.dualPairing
      (NLS.Coeff.multiplier NLS.Coeff.positiveIndexReciprocal (hillHminusMomentKernelVector C N k 2 q))
      (Q q (lp.single 2 (n : ℤ) 1))=_
  rw [NLS.Coeff.dualPairing_hilbert_comm]
  rw [D.normalizedMoment_eq_kernel_vector R n k 2 q hq,he,NLS.Coeff.dualPairing_multiplier_left]
  simp only [map_smul,smul_apply,smul_eq_mul,Nat.cast_ofNat]
  field_simp
  ring

/-- A full Hilbert vector, not merely each coordinate, obeys the same
one-weight high-gap bound on the actual common rough domain. -/
theorem norm_weightedSecondMomentVector_gap_bound
    (H : HillHminusCriticalPrimitiveCutData C N M U r B) (hUV : U⊆V)
    (Q : PeriodOneHminusOne → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (q : PeriodOneHminusOne) (hq : q∈U) (hQ : ‖Q q‖≤2) (k : ℕ+) (hk : M≤(k : ℕ))
    (l u : ℂ) (hp : HillHminusHighGapPair q k r l u) :
    ‖hillHminusWeightedSecondMomentVector C N Q k q‖≤
      (1376*Real.pi^2*B^3)*(‖l-u‖^2/(k : ℕ)^2)/(k : ℕ) := by
  have hB := H.bound_pos
  have hnorm : ‖(2*(Real.pi : ℂ))/3‖=2*Real.pi/3 := by
    rw [norm_div,norm_mul,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le]
    norm_num
  apply (NLS.Coeff.norm_positiveDeletedProjection_le 0 _).trans
  rw [norm_smul,hnorm]
  apply (mul_le_mul_of_nonneg_left (NLS.Coeff.norm_hilbertMatrixTranspose_apply_le _ _) (by positivity : 0≤2*Real.pi/3)).trans
  calc
    _≤(2*Real.pi/3)*(2*((1032*Real.pi*B^3)*(‖l-u‖^2/(k : ℕ)^2)/(k : ℕ))) := by
      gcongr
      exact D.momentKernel_onceWeighted_second_bound H hUV q hq k hk l u hp
    _=_ := by ring

/-- Uniform full-vector control handles every finite contour head on the
SAME complex domain, before all contours and every own frequency index. -/
theorem norm_weightedSecondMomentVector_uniform_bound
    (Q : PeriodOneHminusOne → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (q : PeriodOneHminusOne) (hq : q∈V) (hQ : ‖Q q‖≤2) (k : ℕ+) :
    ‖hillHminusWeightedSecondMomentVector C N Q k q‖≤320*A^3 := by
  have hA := D.amplitude_pos
  have hnorm : ‖(2*(Real.pi : ℂ))/3‖=2*Real.pi/3 := by
    rw [norm_div,norm_mul,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le]
    norm_num
  have hrec : ‖NLS.Coeff.multiplier NLS.Coeff.positiveIndexReciprocal
      (hillHminusMomentKernelVector C N k 2 q)‖≤‖hillHminusMomentKernelVector C N k 2 q‖ := by
    apply lp.norm_mono (by norm_num : (2 : ENNReal)≠0)
    intro j
    rw [NLS.Coeff.multiplier_apply,NLS.Coeff.positiveIndexReciprocal_apply,norm_mul,norm_inv]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (inv_le_one_of_one_le₀ (NLS.Coeff.one_le_norm_positiveIndexWeight j))
  apply (NLS.Coeff.norm_positiveDeletedProjection_le 0 _).trans
  rw [norm_smul,hnorm]
  apply (mul_le_mul_of_nonneg_left (NLS.Coeff.norm_hilbertMatrixTranspose_apply_le _ _) (by positivity : 0≤2*Real.pi/3)).trans
  calc
    _≤(2*Real.pi/3)*(2*((240/Real.pi)*A^3)) := by
      gcongr
      exact hrec.trans (D.momentKernel_second_uniform_bound k q hq)
    _=_ := by field_simp;ring

end HillHminusUniformPeriodData
end NLS.KdV
