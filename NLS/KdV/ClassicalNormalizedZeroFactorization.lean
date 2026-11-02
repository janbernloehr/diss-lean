import NLS.KdV.ClassicalCandidateNumeratorUnits

/-! # Exact filled factorization of the actual normalized zero equation

The scalar equation and the normalized entire numerator differ by proved
nonzero factors throughout the candidate domain, including at own critical
energies. This retains multiplicities, rather than merely zero sets.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV
namespace ClassicalAllContourPeriodData
variable {N : ℕ} {V : Set (NLS.LinearVolterra.Curve ℂ)} {A : ℝ}
variable (D : ClassicalAllContourPeriodData N V A)
include D

theorem zeroMap_filled_identity
    (Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (hQa : AnalyticOnNhd ℂ Q V) (hQ : ∀ q ∈ V, ‖Q q‖ ≤ 2)
    (n k : ℕ+) (hkn : k ≠ n) (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ)
    (ht : t ∈ classicalHillCandidateDomain V) :
    (classicalHillCandidateEnergy N k t-classicalHillUniformCriticalPoint N n t.2)/(k : ℂ)*
      classicalHillZeroCoefficients Q n t.2 (k : ℤ)+
      (classicalHillCandidateEnergy N k t-classicalHillUniformCriticalPoint N k t.2)*
        classicalHillZeroBracket N Q n k t =
      (2*classicalHillCriticalFrequency N k t.2)*classicalHillZeroMap N Q n t (k : ℤ) := by
  have hk : (0 : ℤ) < k := by exact_mod_cast k.pos
  have hi : positiveIntegerIndex (k : ℤ) hk = k := by apply Subtype.ext; exact Int.toNat_natCast _
  rw [(D.zeroMap_spec Q hQa hQ n).1 t ht,classicalHillZeroCoordinates,dif_pos hk,hi,if_neg hkn]
  have hxi := D.critical_frequency_ne_zero k t.2 ht.2
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast k.ne_zero
  have hs : (classicalHillCriticalFrequency N k t.2)^2 = classicalHillUniformCriticalPoint N k t.2 := sq_sqrt _
  dsimp only [classicalHillCandidateEnergy,classicalHillCandidateFrequency]
  rw [← hs]
  field_simp
  ring

theorem normalizedNumerator_at_candidate_critical
    (R : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (n k : ℕ+) (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ)
    (ht : t ∈ classicalHillCandidateDomain V)
    (hcrit : classicalHillCandidateEnergy N k t = classicalHillUniformCriticalPoint N k t.2) :
    classicalHillNormalizedNumerator N R n (classicalHillCandidateEnergy N k t,t.2) =
      (R t.2 (lp.single 2 (n : ℤ) 1)) (k : ℤ)*classicalHillUniformNumerator N k (classicalHillCandidateEnergy N k t,t.2) := by
  rw [(D.normalizedNumerator_positive_series R n _ ⟨mem_univ _,ht.2⟩).2]
  apply tsum_eq_single k
  intro j hj
  have hfac := D.numerator_factor j t.2 ht.2 (classicalHillCandidateEnergy N k t)
  have hd : deriv (classicalHillDiscriminant t.2) (classicalHillCandidateEnergy N k t) = 0 := by
    rw [hcrit]
    exact D.critical_zero k t.2 ht.2
  rw [hd,mul_zero] at hfac
  have hz := (mul_eq_zero.mp hfac).resolve_left (D.candidate_energy_sub_ne_zero k j (Ne.symm hj) t ht)
  rw [hz,mul_zero]

/-- The filled numerator identity is exact for every candidate, not only
for a selected root of the equation. -/
theorem normalizedNumerator_filled_factorization
    (R Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (hQa : AnalyticOnNhd ℂ Q V) (hQ : ∀ q ∈ V, ‖Q q‖ ≤ 2)
    (n k : ℕ+) (hkn : k ≠ n) (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ)
    (ht : t ∈ classicalHillCandidateDomain V)
    (hcompat : ∀ m j : ℤ,
      NLS.Coeff.positiveIndexWeight m^2*(R t.2 (lp.single 2 j 1)) m =
        NLS.Coeff.positiveIndexWeight j^2*(Q t.2 (lp.single 2 j 1)) m) :
    (classicalHillCandidateEnergy N k t-classicalHillUniformCriticalPoint N n t.2)*
      classicalHillNormalizedNumerator N R n (classicalHillCandidateEnergy N k t,t.2) =
        (2*(n : ℂ)*classicalHillCriticalFrequency N k t.2/(k : ℂ))*
          classicalHillUniformNumerator N k (classicalHillCandidateEnergy N k t,t.2)*
            classicalHillZeroMap N Q n t (k : ℤ) := by
  let lambda := classicalHillCandidateEnergy N k t
  let B := classicalHillUniformNumerator N k (lambda,t.2)
  let E := (lambda-classicalHillUniformCriticalPoint N n t.2)/(k : ℂ)*classicalHillZeroCoefficients Q n t.2 (k : ℤ)+
    (lambda-classicalHillUniformCriticalPoint N k t.2)*classicalHillZeroBracket N Q n k t
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast n.ne_zero
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast k.ne_zero
  have hb := zeroCoefficients_div_eq R Q t.2 hcompat n k
  have hEF : E = (2*classicalHillCriticalFrequency N k t.2)*classicalHillZeroMap N Q n t (k : ℤ) :=
    D.zeroMap_filled_identity Q hQa hQ n k hkn t ht
  have hmain : (lambda-classicalHillUniformCriticalPoint N n t.2)*classicalHillNormalizedNumerator N R n (lambda,t.2) =
      ((n : ℂ)/(k : ℂ))*B*E := by
    by_cases hc : lambda-classicalHillUniformCriticalPoint N k t.2 = 0
    · rw [D.normalizedNumerator_at_candidate_critical R n k t ht (sub_eq_zero.mp hc)]
      have ha : ((n : ℂ)/(k : ℂ))*(classicalHillZeroCoefficients Q n t.2 (k : ℤ)/(k : ℂ)) =
          (R t.2 (lp.single 2 (n : ℤ) 1)) (k : ℤ) := by
        rw [hb]
        field_simp
      dsimp only [E]
      rw [hc,zero_mul,add_zero]
      change (lambda-classicalHillUniformCriticalPoint N n t.2)*
        ((R t.2 (lp.single 2 (n : ℤ) 1)) (k : ℤ)*B) = _
      rw [← ha]
      ring
    · have hlam (j : ℕ+) : lambda ≠ classicalHillUniformCriticalPoint N j t.2 := by
        by_cases hj : j = k
        · subst j; exact sub_ne_zero.mp hc
        · exact sub_ne_zero.mp (D.candidate_energy_sub_ne_zero k j (Ne.symm hj) t ht)
      let S : ℂ := ∑' j : ℕ+, (j : ℂ)*(R t.2 (lp.single 2 (n : ℤ) 1)) (j : ℤ)/
        (lambda-classicalHillUniformCriticalPoint N j t.2)
      have hES : E = ((lambda-classicalHillUniformCriticalPoint N n t.2)/(n : ℂ))*
          (lambda-classicalHillUniformCriticalPoint N k t.2)*S := by
        dsimp only [E]
        rw [D.zeroBracket_resolvent R Q n k hkn t ht hcompat]
        have hfirst : (lambda-classicalHillUniformCriticalPoint N n t.2)/(k : ℂ)*classicalHillZeroCoefficients Q n t.2 (k : ℤ) =
            ((lambda-classicalHillUniformCriticalPoint N n t.2)/(n : ℂ))*((k : ℂ)*(R t.2 (lp.single 2 (n : ℤ) 1)) (k : ℤ)) := by
          calc
            _ = (lambda-classicalHillUniformCriticalPoint N n t.2)*(classicalHillZeroCoefficients Q n t.2 (k : ℤ)/(k : ℂ)) := by ring
            _ = _ := by rw [hb]; ring
        rw [hfirst]
        change ((lambda-classicalHillUniformCriticalPoint N n t.2)/(n : ℂ))*((k : ℂ)*(R t.2 (lp.single 2 (n : ℤ) 1)) (k : ℤ))+
          (lambda-classicalHillUniformCriticalPoint N k t.2)*(((lambda-classicalHillUniformCriticalPoint N n t.2)/(n : ℂ))*
            (S-(k : ℂ)*(R t.2 (lp.single 2 (n : ℤ) 1)) (k : ℤ)/(lambda-classicalHillUniformCriticalPoint N k t.2))) = _
        field_simp [hc]
        ring
      rw [D.normalizedNumerator_resolvent R n t.2 ht.2 lambda hlam,hES]
      have hfac := D.numerator_factor k t.2 ht.2 lambda
      change (lambda-classicalHillUniformCriticalPoint N k t.2)*B = _ at hfac
      calc
        _ = ((lambda-classicalHillUniformCriticalPoint N n t.2)*S/(k : ℂ))*
            ((lambda-classicalHillUniformCriticalPoint N k t.2)*B) := by
          rw [hfac]
          field_simp
          ring
        _ = _ := by field_simp
  change (lambda-classicalHillUniformCriticalPoint N n t.2)*classicalHillNormalizedNumerator N R n (lambda,t.2) =
    (2*(n : ℂ)*classicalHillCriticalFrequency N k t.2/(k : ℂ))*B*classicalHillZeroMap N Q n t (k : ℤ)
  rw [hmain,hEF]
  ring

end ClassicalAllContourPeriodData
end NLS.KdV
