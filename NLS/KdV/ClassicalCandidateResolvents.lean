import NLS.KdV.ClassicalCandidateZeros
import NLS.SequenceSpaces.TwoSequenceBound
import NLS.SequenceSpaces.CompactPuncturedKernel

/-! # Actual analytic Hilbert resolvent rows for simultaneous zero equations

The rows omit their own moving critical factor and the selected numerator
index. A uniform reciprocal/translated-reciprocal majorant gives genuine
l2 membership and Banach analyticity on the full candidate domain.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

def classicalHillCandidateRowCoordinates (N : ℕ) (n k : ℕ+)
    (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) (m : ℤ) : ℂ :=
  if hm : 0 < m then
    let j := positiveIntegerIndex m hm
    if j = k ∨ j = n then 0 else
      (classicalHillCandidateEnergy N k t-classicalHillUniformCriticalPoint N n t.2)/
        ((m : ℂ)*(classicalHillCandidateEnergy N k t-classicalHillUniformCriticalPoint N j t.2))
  else 0

def classicalHillCandidateRow (N : ℕ) (n k : ℕ+)
    (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) : NLS.Coeff 2 :=
  NLS.Coeff.ofFunctionOrZero 2 (classicalHillCandidateRowCoordinates N n k t)

namespace ClassicalAllContourPeriodData
variable {N : ℕ} {V : Set (NLS.LinearVolterra.Curve ℂ)} {A : ℝ}
variable (D : ClassicalAllContourPeriodData N V A)
include D

theorem norm_candidate_resolvent_le (n k m : ℕ+) (hkm : k ≠ m)
    (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) (ht : t ∈ classicalHillCandidateDomain V) :
    ‖(classicalHillCandidateEnergy N k t-classicalHillUniformCriticalPoint N n t.2)/
      ((m : ℂ)*(classicalHillCandidateEnergy N k t-classicalHillUniformCriticalPoint N m t.2))‖ ≤
        (16*(1+(n : ℝ)^2))*(1/(m : ℝ)+1/|(k : ℝ)-(m : ℝ)|) := by
  have hm : (0 : ℝ) < m := by exact_mod_cast m.pos
  have hd := positiveIndex_squared_sub_ne_zero k m hkm
  have hden : 0 < (m : ℝ)*(Real.pi^2/4*|(k : ℝ)^2-(m : ℝ)^2|) :=
    mul_pos hm (mul_pos (by positivity) (abs_pos.mpr hd))
  rw [norm_div,norm_mul,Complex.norm_natCast]
  calc
    _ ≤ (4*Real.pi^2*((k : ℝ)^2+(n : ℝ)^2))/
        ((m : ℝ)*(Real.pi^2/4*|(k : ℝ)^2-(m : ℝ)^2|)) := by
      gcongr
      · exact D.norm_candidate_energy_sub_critical_le k n t ht
      · exact D.candidate_energy_separation k m hkm t ht
    _ = 16*(((k : ℝ)^2+(n : ℝ)^2)/((m : ℝ)*|(k : ℝ)^2-(m : ℝ)^2|)) := by field_simp; ring
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (positiveIndex_resolvent_kernel_le k m n hkm) (by norm_num : (0 : ℝ) ≤ 16)

theorem candidateRow_bound (n k : ℕ+)
    (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) (ht : t ∈ classicalHillCandidateDomain V) (m : ℤ) :
    ‖classicalHillCandidateRowCoordinates N n k t m‖ ≤ (16*(1+(n : ℝ)^2))*
      (‖NLS.Coeff.positiveReciprocalHilbert m‖+
        ‖NLS.Coeff.shift (k : ℤ) (NLS.Coeff.puncturedLattice 2 (by norm_num)) m‖) := by
  unfold classicalHillCandidateRowCoordinates
  by_cases hm : 0 < m
  · rw [dif_pos hm]
    let j := positiveIntegerIndex m hm
    by_cases hj : j = k ∨ j = n
    · rw [if_pos hj,norm_zero]
      positivity
    · rw [if_neg hj]
      have hkm : k ≠ j := Ne.symm (not_or.mp hj).1
      have hb := D.norm_candidate_resolvent_le n k j hkm t ht
      have hmk : m ≠ (k : ℤ) := by
        intro he
        apply (not_or.mp hj).1
        apply Subtype.ext
        change m.toNat = (k : ℕ)
        rw [he,Int.toNat_natCast]
      have hjC : (j : ℂ) = (m : ℂ) := by exact_mod_cast positiveIntegerIndex_int m hm
      rw [NLS.Coeff.positiveReciprocalHilbert_apply,if_pos hm,norm_inv,Complex.norm_intCast,
        abs_of_pos (by exact_mod_cast hm : (0 : ℝ) < m),
        NLS.Coeff.norm_shift_puncturedLattice_apply,if_neg hmk,Int.cast_sub,Int.cast_natCast]
      have hrev : |(m : ℝ)-(k : ℝ)| = |(k : ℝ)-(m : ℝ)| := abs_sub_comm _ _
      rw [hrev]
      simpa only [j,positiveIntegerIndex_real,hjC,one_div] using! hb
  · rw [dif_neg hm,norm_zero]
    positivity

theorem candidateRow_spec (n k : ℕ+) :
    (∀ t ∈ classicalHillCandidateDomain V, ∀ m : ℤ,
      classicalHillCandidateRow N n k t m = classicalHillCandidateRowCoordinates N n k t m) ∧
      (∀ t ∈ classicalHillCandidateDomain V, ‖classicalHillCandidateRow N n k t‖ ≤ 64*(1+(n : ℝ)^2)) ∧
      AnalyticOnNhd ℂ (classicalHillCandidateRow N n k) (classicalHillCandidateDomain V) := by
  have hmem (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) (ht : t ∈ classicalHillCandidateDomain V) :=
    NLS.Coeff.memℓp_and_norm_ofFunctionOrZero_le_of_two_sequence_bound
      (classicalHillCandidateRowCoordinates N n k t) NLS.Coeff.positiveReciprocalHilbert
      (NLS.Coeff.shift (k : ℤ) (NLS.Coeff.puncturedLattice 2 (by norm_num)))
      (16*(1+(n : ℝ)^2)) (by positivity) (D.candidateRow_bound n k t ht)
  have he (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) (ht : t ∈ classicalHillCandidateDomain V) (m : ℤ) :
      classicalHillCandidateRow N n k t m = classicalHillCandidateRowCoordinates N n k t m :=
    NLS.Coeff.ofFunctionOrZero_apply_of_mem 2 _ (hmem t ht).1 m
  have hn (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) (ht : t ∈ classicalHillCandidateDomain V) :
      ‖classicalHillCandidateRow N n k t‖ ≤ 64*(1+(n : ℝ)^2) := by
    have hb := (hmem t ht).2
    rw [LinearIsometryEquiv.norm_map] at hb
    change ‖classicalHillCandidateRow N n k t‖ ≤ 16*(1+(n : ℝ)^2)*
      (‖NLS.Coeff.positiveReciprocalHilbert‖+‖NLS.Coeff.puncturedLattice 2 (by norm_num)‖) at hb
    have hu := NLS.Coeff.norm_positiveReciprocalHilbert_le
    have hv := NLS.Coeff.norm_puncturedLattice_two_le
    nlinarith
  have hU : IsOpen (classicalHillCandidateDomain V) := isOpen_ball.prod D.isOpen
  have hcoord (m : ℤ) : AnalyticOnNhd ℂ (fun t => classicalHillCandidateRow N n k t m)
      (classicalHillCandidateDomain V) := by
    have hraw : AnalyticOnNhd ℂ (fun t => classicalHillCandidateRowCoordinates N n k t m)
        (classicalHillCandidateDomain V) := by
      by_cases hm : 0 < m
      · let j := positiveIntegerIndex m hm
        by_cases hj : j = k ∨ j = n
        · have heq : (fun t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ => classicalHillCandidateRowCoordinates N n k t m) = fun _ => (0 : ℂ) := by
            funext t
            rw [classicalHillCandidateRowCoordinates,dif_pos hm]
            change (if j = k ∨ j = n then (0 : ℂ) else _) = 0
            rw [if_pos hj]
          rw [heq]
          exact (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ => (0 : ℂ)) (classicalHillCandidateDomain V))
        · intro t ht
          have hjq := (D.critical_analytic j t.2 ht.2).comp
            (f := fun s : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ => s.2) analyticAt_snd
          have hnq := (D.critical_analytic n t.2 ht.2).comp
            (f := fun s : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ => s.2) analyticAt_snd
          have hlam := D.candidate_energy_analytic k t ht
          have heq : (fun s : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ => classicalHillCandidateRowCoordinates N n k s m) =
              fun s => (classicalHillCandidateEnergy N k s-classicalHillUniformCriticalPoint N n s.2)/
                ((m : ℂ)*(classicalHillCandidateEnergy N k s-classicalHillUniformCriticalPoint N j s.2)) := by
            funext s
            rw [classicalHillCandidateRowCoordinates,dif_pos hm]
            change (if j = k ∨ j = n then (0 : ℂ) else _) = _
            rw [if_neg hj]
          rw [heq]
          exact (hlam.sub hnq).div ((analyticAt_const (v := (m : ℂ))).mul (hlam.sub hjq))
            (mul_ne_zero (by exact_mod_cast ne_of_gt hm : (m : ℂ) ≠ 0) (D.candidate_energy_sub_ne_zero k j (Ne.symm (not_or.mp hj).1) t ht))
      · simpa only [classicalHillCandidateRowCoordinates,dif_neg hm] using
          (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ => (0 : ℂ)) (classicalHillCandidateDomain V))
    intro t ht
    exact (hraw t ht).congr (by
      filter_upwards [hU.mem_nhds ht] with s hs
      exact (he s hs m).symm)
  exact ⟨he,hn,NLS.Coeff.analyticOnNhd_of_bounded_coordinatewise _ hU hcoord _ hn⟩

end ClassicalAllContourPeriodData
end NLS.KdV
