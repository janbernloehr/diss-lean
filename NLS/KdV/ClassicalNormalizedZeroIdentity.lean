import NLS.KdV.ClassicalNormalizedRootBranches

/-! # The filled sequence equation gives actual normalized numerator zeros

The resolvent identity is used off the own critical energy. At the filled
critical point the entire numerator factor identity gives the same zero
conclusion directly, so no division by a vanishing factor is made.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

private theorem tsum_omit_two (f : ℕ+ → ℂ) (hs : Summable (fun j => ‖f j‖))
    (k n : ℕ+) (hkn : k ≠ n) :
    f n+(∑' j, if j = k ∨ j = n then 0 else f j) = (∑' j, f j)-f k := by
  classical
  let g (j : ℕ+) := if j = n then (0 : ℂ) else f j
  have hg : Summable (fun j => ‖g j‖) := hs.of_nonneg_of_le (fun _ => norm_nonneg _) (by
    intro j
    dsimp only [g]
    split_ifs
    · simpa only [norm_zero] using norm_nonneg (f j)
    · exact le_rfl)
  have hn := hs.of_norm.tsum_eq_add_tsum_ite n
  have hk := hg.of_norm.tsum_eq_add_tsum_ite k
  have htail : (∑' j, if j = k then 0 else g j) = ∑' j, if j = k ∨ j = n then 0 else f j := by
    apply tsum_congr
    intro j
    by_cases hjk : j = k <;> by_cases hjn : j = n <;> simp [g,hjk,hjn]
  change (∑' j, g j) = g k+∑' j, if j = k then 0 else g j at hk
  rw [htail,show g k = f k by simp only [g,if_neg hkn]] at hk
  change (∑' j, f j) = f n+∑' j, g j at hn
  rw [hn,hk]
  abel

theorem zeroCoefficients_div_eq
    (R Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (q : NLS.LinearVolterra.Curve ℂ)
    (hcompat : ∀ m j : ℤ,
      NLS.Coeff.positiveIndexWeight m^2*(R q (lp.single 2 j 1)) m =
        NLS.Coeff.positiveIndexWeight j^2*(Q q (lp.single 2 j 1)) m) (n k : ℕ+) :
    classicalHillZeroCoefficients Q n q (k : ℤ)/(k : ℂ) =
      ((k : ℂ)/(n : ℂ))*(R q (lp.single 2 (n : ℤ) 1)) (k : ℤ) := by
  have hn : (0 : ℤ) < n := by exact_mod_cast n.pos
  have hk : (0 : ℤ) < k := by exact_mod_cast k.pos
  have hwn : NLS.Coeff.positiveIndexWeight (n : ℤ) = (n : ℂ) := by
    simp only [NLS.Coeff.positiveIndexWeight,if_pos hn,Int.cast_natCast]
  have hwk : NLS.Coeff.positiveIndexWeight (k : ℤ) = (k : ℂ) := by
    simp only [NLS.Coeff.positiveIndexWeight,if_pos hk,Int.cast_natCast]
  have he := hcompat (k : ℤ) (n : ℤ)
  rw [hwn,hwk] at he
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast n.ne_zero
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast k.ne_zero
  change (n : ℂ)*(Q q (lp.single 2 (n : ℤ) 1)) (k : ℤ)/(k : ℂ) = _
  field_simp
  simpa only [pow_two,mul_assoc,mul_comm,mul_left_comm] using he.symm

namespace ClassicalAllContourPeriodData
variable {N : ℕ} {V : Set (NLS.LinearVolterra.Curve ℂ)} {A : ℝ}
variable (D : ClassicalAllContourPeriodData N V A)
include D

theorem zeroMap_filled_equation
    (Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (hQa : AnalyticOnNhd ℂ Q V) (hQ : ∀ q ∈ V, ‖Q q‖ ≤ 2)
    (n k : ℕ+) (hkn : k ≠ n) (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ)
    (ht : t ∈ classicalHillCandidateDomain V) (hzero : classicalHillZeroMap N Q n t = 0) :
    (classicalHillCandidateEnergy N k t-classicalHillUniformCriticalPoint N n t.2)/(k : ℂ)*
      classicalHillZeroCoefficients Q n t.2 (k : ℤ)+
      (classicalHillCandidateEnergy N k t-classicalHillUniformCriticalPoint N k t.2)*
        classicalHillZeroBracket N Q n k t = 0 := by
  have hk : (0 : ℤ) < k := by exact_mod_cast k.pos
  have hi : positiveIntegerIndex (k : ℤ) hk = k := by
    apply Subtype.ext
    exact Int.toNat_natCast _
  have hv := congrArg (fun x : NLS.Coeff 2 => x (k : ℤ)) hzero
  rw [(D.zeroMap_spec Q hQa hQ n).1 t ht,classicalHillZeroCoordinates,dif_pos hk,hi,if_neg hkn] at hv
  simp only [lp.coeFn_zero,Pi.zero_apply] at hv
  have hxi := D.critical_frequency_ne_zero k t.2 ht.2
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast k.ne_zero
  have hs : (classicalHillCriticalFrequency N k t.2)^2 = classicalHillUniformCriticalPoint N k t.2 := sq_sqrt _
  calc
    _ = (2*classicalHillCriticalFrequency N k t.2)*
        (((classicalHillCandidateEnergy N k t-classicalHillUniformCriticalPoint N n t.2)/
          (2*classicalHillCriticalFrequency N k t.2*(k : ℂ)))*classicalHillZeroCoefficients Q n t.2 (k : ℤ)+
          t.1 (k : ℤ)*(1+t.1 (k : ℤ)/(2*classicalHillCriticalFrequency N k t.2))*classicalHillZeroBracket N Q n k t) := by
      dsimp only [classicalHillCandidateEnergy,classicalHillCandidateFrequency]
      rw [← hs]
      field_simp
      ring
    _ = 0 := by rw [hv,mul_zero]

theorem zeroBracket_resolvent
    (R Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (n k : ℕ+) (hkn : k ≠ n) (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ)
    (ht : t ∈ classicalHillCandidateDomain V)
    (hcompat : ∀ m j : ℤ,
      NLS.Coeff.positiveIndexWeight m^2*(R t.2 (lp.single 2 j 1)) m =
        NLS.Coeff.positiveIndexWeight j^2*(Q t.2 (lp.single 2 j 1)) m) :
    classicalHillZeroBracket N Q n k t =
      ((classicalHillCandidateEnergy N k t-classicalHillUniformCriticalPoint N n t.2)/(n : ℂ))*
        ((∑' j : ℕ+, (j : ℂ)*(R t.2 (lp.single 2 (n : ℤ) 1)) (j : ℤ)/
          (classicalHillCandidateEnergy N k t-classicalHillUniformCriticalPoint N j t.2))-
          (k : ℂ)*(R t.2 (lp.single 2 (n : ℤ) 1)) (k : ℤ)/
            (classicalHillCandidateEnergy N k t-classicalHillUniformCriticalPoint N k t.2)) := by
  let num := classicalHillCandidateEnergy N k t-classicalHillUniformCriticalPoint N n t.2
  let a : ℂ := num/(n : ℂ)
  let f (j : ℕ+) : ℂ := (j : ℂ)*(R t.2 (lp.single 2 (n : ℤ) 1)) (j : ℤ)/
    (classicalHillCandidateEnergy N k t-classicalHillUniformCriticalPoint N j t.2)
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast n.ne_zero
  have hnum : num ≠ 0 := D.candidate_energy_sub_ne_zero k n hkn t ht
  have hterm (j : ℕ+) : classicalHillCandidateRow N n k t (j : ℤ)*classicalHillZeroCoefficients Q n t.2 (j : ℤ) =
      if j = k ∨ j = n then 0 else a*f j := by
    have hj : (0 : ℤ) < j := by exact_mod_cast j.pos
    have hi : positiveIntegerIndex (j : ℤ) hj = j := by apply Subtype.ext; exact Int.toNat_natCast _
    rw [(D.candidateRow_spec n k).1 t ht,classicalHillCandidateRowCoordinates,dif_pos hj,hi]
    by_cases hje : j = k ∨ j = n
    · rw [if_pos hje,zero_mul,if_pos hje]
    · rw [if_neg hje,if_neg hje]
      have hd := zeroCoefficients_div_eq R Q t.2 hcompat n j
      change (num/((j : ℂ)*(classicalHillCandidateEnergy N k t-classicalHillUniformCriticalPoint N j t.2)))*
        classicalHillZeroCoefficients Q n t.2 (j : ℤ) = a*f j
      calc
        _ = num*(classicalHillZeroCoefficients Q n t.2 (j : ℤ)/(j : ℂ))/
            (classicalHillCandidateEnergy N k t-classicalHillUniformCriticalPoint N j t.2) := by
          simp only [div_eq_mul_inv,mul_inv_rev]
          ring
        _ = _ := by rw [hd]; dsimp only [a,f]; simp only [div_eq_mul_inv]; ring
  have hz (j : ℤ) (hj : j ≤ 0) : classicalHillCandidateRow N n k t j*classicalHillZeroCoefficients Q n t.2 j = 0 := by
    rw [(D.candidateRow_spec n k).1 t ht,classicalHillCandidateRowCoordinates,dif_neg (by omega : ¬ 0 < j),zero_mul]
  have hpair : NLS.Coeff.dualPairing (classicalHillCandidateRow N n k t) (classicalHillZeroCoefficients Q n t.2) =
      a*∑' j : ℕ+, if j = k ∨ j = n then 0 else f j := by
    rw [NLS.Coeff.dualPairing_apply,tsum_eq_positive_of_nonpositive_zero _ hz]
    calc
      _ = ∑' j : ℕ+, a*(if j = k ∨ j = n then 0 else f j) := by
        apply tsum_congr
        intro j
        rw [hterm]
        split_ifs <;> simp only [mul_zero]
      _ = _ := tsum_mul_left
  have hfirst : classicalHillZeroCoefficients Q n t.2 (n : ℤ)/(n : ℂ) = a*f n := by
    rw [zeroCoefficients_div_eq R Q t.2 hcompat n n,div_self hn0,one_mul]
    have hnum' : classicalHillCandidateEnergy N k t-classicalHillUniformCriticalPoint N n t.2 ≠ 0 := hnum
    dsimp only [a,f,num]
    field_simp [hnum']
  rw [classicalHillZeroBracket,hpair,hfirst,← mul_add]
  exact congrArg (fun z : ℂ => a*z)
    (tsum_omit_two f (D.summable_norm_normalized_resolvent R Q t.2 ht.2 hcompat n _) k n hkn)

/-- Every solved retained sequence equation is a zero of the actual
normalized entire numerator, including its filled own critical energy. -/
theorem normalizedNumerator_zero_of_zeroMap
    (R Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (hQa : AnalyticOnNhd ℂ Q V) (hQ : ∀ q ∈ V, ‖Q q‖ ≤ 2)
    (n k : ℕ+) (hkn : k ≠ n) (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ)
    (ht : t ∈ classicalHillCandidateDomain V)
    (hcompat : ∀ m j : ℤ,
      NLS.Coeff.positiveIndexWeight m^2*(R t.2 (lp.single 2 j 1)) m =
        NLS.Coeff.positiveIndexWeight j^2*(Q t.2 (lp.single 2 j 1)) m)
    (hzero : classicalHillZeroMap N Q n t = 0) :
    classicalHillNormalizedNumerator N R n (classicalHillCandidateEnergy N k t,t.2) = 0 := by
  let lambda := classicalHillCandidateEnergy N k t
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast n.ne_zero
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast k.ne_zero
  have hnum : lambda-classicalHillUniformCriticalPoint N n t.2 ≠ 0 := D.candidate_energy_sub_ne_zero k n hkn t ht
  have hE := D.zeroMap_filled_equation Q hQa hQ n k hkn t ht hzero
  by_cases hkcrit : lambda-classicalHillUniformCriticalPoint N k t.2 = 0
  · have hb : classicalHillZeroCoefficients Q n t.2 (k : ℤ) = 0 := by
      change (lambda-classicalHillUniformCriticalPoint N n t.2)/(k : ℂ)*_+(lambda-classicalHillUniformCriticalPoint N k t.2)*_ = 0 at hE
      rw [hkcrit,zero_mul,add_zero] at hE
      exact (mul_eq_zero.mp hE).resolve_left (div_ne_zero hnum hk0)
    have ha : (R t.2 (lp.single 2 (n : ℤ) 1)) (k : ℤ) = 0 := by
      have he := zeroCoefficients_div_eq R Q t.2 hcompat n k
      rw [hb,zero_div] at he
      exact (mul_eq_zero.mp he.symm).resolve_left (div_ne_zero hk0 hn0)
    have hcrit : deriv (classicalHillDiscriminant t.2) lambda = 0 := by
      rw [sub_eq_zero.mp hkcrit]
      exact D.critical_zero k t.2 ht.2
    rw [(D.normalizedNumerator_positive_series R n (lambda,t.2) ⟨mem_univ _,ht.2⟩).2]
    have hzsum (j : ℕ+) : (R t.2 (lp.single 2 (n : ℤ) 1)) (j : ℤ)*classicalHillUniformNumerator N j (lambda,t.2) = 0 := by
      by_cases hj : j = k
      · subst j
        rw [ha,zero_mul]
      · have hfac := D.numerator_factor j t.2 ht.2 lambda
        rw [hcrit,mul_zero] at hfac
        have hz := (mul_eq_zero.mp hfac).resolve_left (D.candidate_energy_sub_ne_zero k j (Ne.symm hj) t ht)
        rw [hz,mul_zero]
    simp only [hzsum,tsum_zero]
  · have hlam (j : ℕ+) : lambda ≠ classicalHillUniformCriticalPoint N j t.2 := by
      by_cases hj : j = k
      · subst j
        exact sub_ne_zero.mp hkcrit
      · exact sub_ne_zero.mp (D.candidate_energy_sub_ne_zero k j (Ne.symm hj) t ht)
    let S : ℂ := ∑' j : ℕ+, (j : ℂ)*(R t.2 (lp.single 2 (n : ℤ) 1)) (j : ℤ)/
      (lambda-classicalHillUniformCriticalPoint N j t.2)
    have heq : (lambda-classicalHillUniformCriticalPoint N n t.2)/(k : ℂ)*classicalHillZeroCoefficients Q n t.2 (k : ℤ)+
        (lambda-classicalHillUniformCriticalPoint N k t.2)*classicalHillZeroBracket N Q n k t =
        ((lambda-classicalHillUniformCriticalPoint N n t.2)/(n : ℂ))*
          (lambda-classicalHillUniformCriticalPoint N k t.2)*S := by
      rw [D.zeroBracket_resolvent R Q n k hkn t ht hcompat]
      have hb := zeroCoefficients_div_eq R Q t.2 hcompat n k
      have hfirst : (lambda-classicalHillUniformCriticalPoint N n t.2)/(k : ℂ)*
          classicalHillZeroCoefficients Q n t.2 (k : ℤ) =
          ((lambda-classicalHillUniformCriticalPoint N n t.2)/(n : ℂ))*
            ((k : ℂ)*(R t.2 (lp.single 2 (n : ℤ) 1)) (k : ℤ)) := by
        calc
          _ = (lambda-classicalHillUniformCriticalPoint N n t.2)*
              (classicalHillZeroCoefficients Q n t.2 (k : ℤ)/(k : ℂ)) := by ring
          _ = _ := by rw [hb]; ring
      rw [hfirst]
      change ((lambda-classicalHillUniformCriticalPoint N n t.2)/(n : ℂ))*
          ((k : ℂ)*(R t.2 (lp.single 2 (n : ℤ) 1)) (k : ℤ))+
        (lambda-classicalHillUniformCriticalPoint N k t.2)*
          (((lambda-classicalHillUniformCriticalPoint N n t.2)/(n : ℂ))*
            (S-(k : ℂ)*(R t.2 (lp.single 2 (n : ℤ) 1)) (k : ℤ)/
              (lambda-classicalHillUniformCriticalPoint N k t.2))) = _
      field_simp [hkcrit]
      ring
    have hS : S = 0 := by
      change (lambda-classicalHillUniformCriticalPoint N n t.2)/(k : ℂ)*_+(lambda-classicalHillUniformCriticalPoint N k t.2)*_ = 0 at hE
      rw [heq] at hE
      exact (mul_eq_zero.mp hE).resolve_left (mul_ne_zero (div_ne_zero hnum hn0) hkcrit)
    rw [D.normalizedNumerator_resolvent R n t.2 ht.2 lambda hlam]
    change _*S = 0
    rw [hS,mul_zero]

end ClassicalAllContourPeriodData
end NLS.KdV
