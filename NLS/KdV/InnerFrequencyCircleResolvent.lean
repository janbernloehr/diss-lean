import NLS.ComplexAnalysis.RightHalfPlaneSquareRoot
import NLS.KdV.HighEnergyDiscSeparation
import NLS.KdV.PositiveEnergyResolventKernel
import NLS.SequenceSpaces.TwoSequenceBound
import NLS.SequenceSpaces.PuncturedLattice
/-! # Uniform Hilbert bounds for inner-circle critical resolvents

The own denominator is separated explicitly. All other indices use the
quadratic disc separation. A single basis vector and a translated reciprocal
lattice control the complete output Hilbert norm with constant 48/pi^2.
-/
noncomputable section
open Set Metric Complex
namespace NLS.KdV

theorem innerFrequencyCircle_diagonal_separation (k : ℕ+) (z w : ℂ)
    (hz : z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/8))
    (hw : w ∈ closedBall ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/16)) :
    Real.pi^2/16*(k : ℝ) ≤ ‖z^2-w^2‖ := by
  have hzn := mem_sphere_iff_norm.mp hz
  have hwn := mem_closedBall_iff_norm.mp hw
  have hminus : Real.pi/16 ≤ ‖z-w‖ := by
    have ht := norm_sub_le_norm_sub_add_norm_sub z w ((Real.pi : ℂ)*(k : ℕ))
    rw [hzn] at ht
    linarith
  have hplus : Real.pi*(k : ℝ) ≤ ‖z+w‖ := by
    have ha := norm_add_le (((Real.pi : ℂ)*(k : ℕ)-z)+(z+w)) (((Real.pi : ℂ)*(k : ℕ)-w))
    have ht := ha.trans (add_le_add (norm_add_le _ _) le_rfl)
    rw [show ((Real.pi : ℂ)*(k : ℕ)-z)+(z+w)+((Real.pi : ℂ)*(k : ℕ)-w) =
      2*((Real.pi : ℂ)*(k : ℕ)) by ring,norm_mul,norm_ofNat,norm_mul,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,Complex.norm_natCast] at ht
    rw [norm_sub_rev ((Real.pi : ℂ)*(k : ℕ)) z,hzn,
      norm_sub_rev ((Real.pi : ℂ)*(k : ℕ)) w] at ht
    have hk : (1 : ℝ) ≤ k := by exact_mod_cast k.property
    nlinarith [Real.pi_pos]
  rw [show z^2-w^2=(z-w)*(z+w) by ring,norm_mul]
  nlinarith [mul_le_mul hminus hplus (by positivity) (norm_nonneg (z-w))]

theorem innerFrequencyCircle_resolvent_bound (μ : ℕ+ → ℂ)
    (hμ : ∀ m : ℕ+, ‖sqrt (μ m)-(Real.pi : ℂ)*(m : ℕ)‖ ≤ Real.pi/16)
    (k m : ℕ+) (z : ℂ)
    (hz : z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/8)) :
    z^2-μ m ≠ 0 ∧
    ‖(m : ℂ)/(z^2-μ m)‖ ≤
      if m = k then 16/Real.pi^2 else (4/Real.pi^2)/|(m : ℝ)-(k : ℝ)| := by
  have hm : (0 : ℝ) < m := by positivity
  have hk : (0 : ℝ) < k := by positivity
  have hwd : sqrt (μ m) ∈ closedBall ((Real.pi : ℂ)*(m : ℕ)) (Real.pi/16) :=
    mem_closedBall_iff_norm.mpr (hμ m)
  by_cases he : m = k
  · subst m
    have hs := innerFrequencyCircle_diagonal_separation k z (sqrt (μ k)) hz hwd
    rw [NLS.ComplexAnalysis.sq_sqrt] at hs
    have hp : 0 < Real.pi^2/16*(k : ℝ) := by positivity
    refine ⟨norm_pos_iff.mp (hp.trans_le hs),?_⟩
    rw [if_pos rfl,norm_div,Complex.norm_natCast]
    calc
      _ ≤ (k : ℝ)/(Real.pi^2/16*(k : ℝ)) := div_le_div_of_nonneg_left hk.le hp hs
      _ = _ := by field_simp
  · have hzq : z ∈ closedBall ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4) :=
      closedBall_subset_closedBall (by linarith [Real.pi_pos]) (sphere_subset_closedBall hz)
    have hwq : sqrt (μ m) ∈ closedBall ((Real.pi : ℂ)*(m : ℕ)) (Real.pi/4) :=
      closedBall_subset_closedBall (by linarith [Real.pi_pos]) hwd
    have hs := highEnergyDiscs_separation m k he z (sqrt (μ m)) hzq hwq
    rw [NLS.ComplexAnalysis.sq_sqrt] at hs
    have hd : 0 < |(k : ℝ)-(m : ℝ)| := lt_of_lt_of_le (by norm_num) (positiveIndex_abs_sub_ge_one k m (Ne.symm he))
    have hf : |(k : ℝ)^2-(m : ℝ)^2| = ((k : ℝ)+(m : ℝ))*|(k : ℝ)-(m : ℝ)| := by
      rw [sq_sub_sq,abs_mul,abs_of_pos (add_pos hk hm)]
    rw [hf] at hs
    have hp : 0 < Real.pi^2/4*(((k : ℝ)+(m : ℝ))*|(k : ℝ)-(m : ℝ)|) := by positivity
    refine ⟨norm_pos_iff.mp (hp.trans_le hs),?_⟩
    rw [if_neg he,norm_div,Complex.norm_natCast,abs_sub_comm (m : ℝ) (k : ℝ)]
    calc
      _ ≤ (m : ℝ)/(Real.pi^2/4*(((k : ℝ)+(m : ℝ))*|(k : ℝ)-(m : ℝ)|)) :=
        div_le_div_of_nonneg_left hm.le hp hs
      _ ≤ (4/Real.pi^2)/|(k : ℝ)-(m : ℝ)| := by
        apply (div_le_iff₀ hp).mpr
        have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
        have heq : ((4/Real.pi^2)/|(k : ℝ)-(m : ℝ)|)*
            (Real.pi^2/4*(((k : ℝ)+(m : ℝ))*|(k : ℝ)-(m : ℝ)|)) = (k : ℝ)+(m : ℝ) := by
          field_simp
        rw [heq]
        linarith

/-- The full Hilbert norm follows from one diagonal basis vector and a
translated punctured reciprocal lattice, uniformly in the moving index. -/
theorem innerFrequencyCircle_hilbert_norm_bound (μ : ℕ+ → ℂ)
    (hμ : ∀ m : ℕ+, ‖sqrt (μ m)-(Real.pi : ℂ)*(m : ℕ)‖ ≤ Real.pi/16)
    (k : ℕ+) (z : ℂ) (hz : z ∈ sphere ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/8))
    (a : NLS.Coeff 2) (H : ℝ) (hH : 0 ≤ H)
    (hapos : ∀ m : ℕ+, ‖a (m : ℤ)‖ ≤ H*‖(m : ℂ)/(z^2-μ m)‖)
    (hazero : ∀ j : ℤ, j ≤ 0 → a j = 0) : ‖a‖ ≤ (48/Real.pi^2)*H := by
  let e : NLS.Coeff 2 := lp.single 2 (k : ℤ) 1
  let v := NLS.Coeff.shift (k : ℤ) (NLS.Coeff.puncturedLattice 2 (by norm_num))
  have hpoint (m : ℕ+) : ‖a (m : ℤ)‖ ≤ ((16/Real.pi^2)*H)*(‖e (m : ℤ)‖+‖v (m : ℤ)‖) := by
    have hr := (innerFrequencyCircle_resolvent_bound μ hμ k m z hz).2
    by_cases he : m = k
    · subst m
      simp only [ite_true] at hr
      simpa [e,v,mul_comm] using (hapos k).trans (mul_le_mul_of_nonneg_left hr hH)
    · have hem : (m : ℤ) ≠ (k : ℤ) := by
        intro h
        apply he
        exact_mod_cast h
      simp only [if_neg he] at hr
      have hv : ‖v (m : ℤ)‖ = 1/|(m : ℝ)-(k : ℝ)| := by
        change ‖if (m : ℤ)-(k : ℤ) = 0 then (0 : ℂ) else (((m : ℤ)-(k : ℤ) : ℤ) : ℂ)⁻¹‖ = _
        rw [if_neg (sub_ne_zero.mpr hem),norm_inv,Complex.norm_intCast]
        simp only [Int.cast_sub,Int.cast_natCast,one_div]
      rw [hv,show e (m : ℤ) = 0 by simp [e,hem],norm_zero,zero_add]
      have hconst : 4/Real.pi^2 ≤ 16/Real.pi^2 := by gcongr; norm_num
      calc
        _ ≤ H*((4/Real.pi^2)/|(m : ℝ)-(k : ℝ)|) := (hapos m).trans (mul_le_mul_of_nonneg_left hr hH)
        _ ≤ H*((16/Real.pi^2)/|(m : ℝ)-(k : ℝ)|) := by gcongr
        _ = _ := by ring
  have hall (j : ℤ) : ‖a j‖ ≤ ((16/Real.pi^2)*H)*(‖e j‖+‖v j‖) := by
    by_cases hj : 0 < j
    · let m : ℕ+ := ⟨j.toNat,by omega⟩
      have hm : (m : ℤ) = j := by change (j.toNat : ℤ) = j; omega
      simpa only [hm] using hpoint m
    · rw [hazero j (by omega),norm_zero]
      positivity
  obtain ⟨hmem,hbound⟩ := NLS.Coeff.memℓp_and_norm_ofFunctionOrZero_le_of_two_sequence_bound
    (fun j => a j) e v ((16/Real.pi^2)*H) (by positivity) hall
  have heq : NLS.Coeff.ofFunctionOrZero 2 (fun j => a j) = a := by
    ext j
    exact NLS.Coeff.ofFunctionOrZero_apply_of_mem 2 _ hmem j
  rw [heq] at hbound
  have he : ‖e‖ = 1 := by simp only [e,lp.norm_single (by norm_num : 0 < (2 : ENNReal)),norm_one]
  have hv : ‖v‖ ≤ 2 := by
    simpa only [v,NLS.Coeff.norm_shift] using NLS.Coeff.norm_puncturedLattice_two_le
  rw [he] at hbound
  calc
    _ ≤ ((16/Real.pi^2)*H)*(1+‖v‖) := hbound
    _ ≤ ((16/Real.pi^2)*H)*(1+2) := by gcongr
    _ = _ := by ring
end NLS.KdV
