import NLS.KdV.HillFreePeriodEvaluation

/-! The free positive Hill interaction kernel is the half-sum of two
translated punctured reciprocal lattices. One l2 bound works before
ALL row and omitted indices; absolute products need no root separation. -/
noncomputable section
open Set Complex
open scoped ENNReal Classical
namespace NLS.KdV

def hillFreeInteractionConstant : ℝ := 4*‖(2*(Real.pi:ℂ)^2)⁻¹‖

theorem hillFreeInteractionConstant_nonneg : 0 ≤ hillFreeInteractionConstant := by
  unfold hillFreeInteractionConstant
  positivity

def hillFreeInteractionKernel (m : ℕ+) : Coeff 2 :=
  (2*(Real.pi:ℂ)^2)⁻¹ •
    (Coeff.shift ((m:ℕ):ℤ) (Coeff.puncturedLattice 2 (by norm_num))+
      Coeff.shift (-((m:ℕ):ℤ)) (Coeff.puncturedLattice 2 (by norm_num)))

theorem norm_hillFreeInteractionKernel_le (m : ℕ+) :
    ‖hillFreeInteractionKernel m‖ ≤ hillFreeInteractionConstant := by
  rw [hillFreeInteractionKernel,norm_smul]
  have h := norm_add_le
    (Coeff.shift ((m:ℕ):ℤ) (Coeff.puncturedLattice 2 (by norm_num)))
    (Coeff.shift (-((m:ℕ):ℤ)) (Coeff.puncturedLattice 2 (by norm_num)))
  simp only [Coeff.norm_shift] at h
  have hp := Coeff.norm_puncturedLattice_two_le
  unfold hillFreeInteractionConstant
  nlinarith [norm_nonneg ((2*(Real.pi:ℂ)^2)⁻¹)]

theorem hillFreeInteractionKernel_positive (m k : ℕ+) (hkm : k ≠ m) :
    hillFreeInteractionKernel m ((k:ℕ):ℤ) =
      ((k:ℕ):ℂ)/((Real.pi:ℂ)^2*(((k:ℕ):ℂ)^2-((m:ℕ):ℂ)^2)) := by
  have hminus : ((k:ℕ):ℤ)-((m:ℕ):ℤ) ≠ 0 := by
    intro h
    exact hkm (Subtype.ext (Int.ofNat.inj (sub_eq_zero.mp h)))
  have hplus : ((k:ℕ):ℤ)-(-((m:ℕ):ℤ)) ≠ 0 := by
    have hk : 0 < ((k:ℕ):ℤ) := by exact_mod_cast k.pos
    have hm : 0 < ((m:ℕ):ℤ) := by exact_mod_cast m.pos
    omega
  simp only [hillFreeInteractionKernel,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,
    lp.coeFn_add,Pi.add_apply,Coeff.shift_apply,Coeff.puncturedLattice_apply,
    if_neg hminus,if_neg hplus,Int.cast_sub,Int.cast_natCast,Int.cast_neg]
  have hpi : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hsq := sub_ne_zero.mpr (pnat_complex_squares_ne hkm)
  have hdminus : ((k:ℕ):ℂ)-((m:ℕ):ℂ) ≠ 0 := by exact_mod_cast hminus
  have hdplus : ((k:ℕ):ℂ)-(-((m:ℕ):ℂ)) ≠ 0 := by exact_mod_cast hplus
  field_simp [hpi,hsq,hdminus,hdplus]
  ring

def hillFreeInteractionPerturbation (n m : ℕ+) (d : lp (fun _ : ℕ+ => ℂ) 2) (j : ℕ) : ℂ :=
  if j = (n:ℕ)-1 ∨ j = (m:ℕ)-1 then 0 else
    d ⟨j+1,by omega⟩*hillFreeInteractionKernel m ((j:ℤ)+1)

theorem sum_norm_hillFreeInteractionPerturbation_le (n m : ℕ+)
    (d : lp (fun _ : ℕ+ => ℂ) 2) (S : Finset ℕ) :
    (∑ j ∈ S, ‖hillFreeInteractionPerturbation n m d j‖) ≤ hillFreeInteractionConstant*‖d‖ := by
  let K := LpSequence.positiveRestriction (hillFreeInteractionKernel m)
  have hholder := lp.tsum_mul_le_mul_norm (show (2:ℝ≥0∞).toReal.HolderConjugate (2:ℝ≥0∞).toReal from Real.HolderConjugate.two_two) d K
  let e : ℕ ↪ ℕ+ := ⟨fun j => ⟨j+1,by omega⟩,fun i j h => by
    have he := congrArg (fun k : ℕ+ => (k:ℕ)) h
    change i+1 = j+1 at he
    omega⟩
  have hsum : (∑ j ∈ S, ‖hillFreeInteractionPerturbation n m d j‖) ≤
      ∑ k ∈ S.map e, ‖d k‖*‖K k‖ := by
    rw [Finset.sum_map]
    apply Finset.sum_le_sum
    intro j _
    unfold hillFreeInteractionPerturbation
    split_ifs
    · simpa only [norm_zero] using mul_nonneg (norm_nonneg (d (e j))) (norm_nonneg (K (e j)))
    · rw [norm_mul]
      rfl
  have hK : ‖K‖ ≤ hillFreeInteractionConstant :=
    (LpSequence.norm_positiveRestriction_le _).trans (norm_hillFreeInteractionKernel_le m)
  calc
    _ ≤ ∑ k ∈ S.map e, ‖d k‖*‖K k‖ := hsum
    _ ≤ ∑' k, ‖d k‖*‖K k‖ := hholder.1.sum_le_tsum _ (fun _ _ => by positivity)
    _ ≤ ‖d‖*‖K‖ := hholder.2
    _ ≤ ‖d‖*hillFreeInteractionConstant := mul_le_mul_of_nonneg_left hK (norm_nonneg _)
    _ = _ := mul_comm _ _

end NLS.KdV
