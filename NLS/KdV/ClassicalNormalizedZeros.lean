import NLS.KdV.ClassicalNormalizedZeroIdentity

/-! # Constructed actual infinite normalized zero families near the free source

For each omitted numerator mode, one analytic Hilbert displacement selects
all other positive zeros simultaneously. Their actual energy values are
analytic and distinct. The source neighborhood may depend on the omitted
mode; completeness, product identity and the full rough domain remain open.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV
namespace ClassicalAllContourPeriodData
variable {N : ℕ} {V : Set (NLS.LinearVolterra.Curve ℂ)} {A : ℝ}
variable (D : ClassicalAllContourPeriodData N V A)
include D

theorem candidate_energies_injective
    (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) (ht : t ∈ classicalHillCandidateDomain V) :
    Function.Injective (fun k : ℕ+ => classicalHillCandidateEnergy N k t) := by
  intro k m he
  change classicalHillCandidateEnergy N k t = classicalHillCandidateEnergy N m t at he
  by_contra hkm
  have hb := highEnergyDiscs_separation m k (Ne.symm hkm) (classicalHillCandidateFrequency N k t)
    (classicalHillCandidateFrequency N m t) (D.candidate_frequency_mem_disc k t ht) (D.candidate_frequency_mem_disc m t ht)
  change Real.pi^2/4*|(k : ℝ)^2-(m : ℝ)^2| ≤ ‖classicalHillCandidateEnergy N k t-classicalHillCandidateEnergy N m t‖ at hb
  rw [he,sub_self,norm_zero] at hb
  have hp : 0 < Real.pi^2/4*|(k : ℝ)^2-(m : ℝ)^2| :=
    mul_pos (by positivity) (abs_pos.mpr (positiveIndex_squared_sub_ne_zero k m hkm))
  linarith

/-- Actual normalized entire numerators, rather than an abstract spectral
model, vanish at the simultaneously constructed analytic root sequence. -/
theorem exists_actual_normalized_zero_family
    (R Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (hQa : AnalyticOnNhd ℂ Q V) (hQ : ∀ q ∈ V, ‖Q q‖ ≤ 2)
    (hQ0 : Q 0 = ContinuousLinearMap.id ℂ (NLS.Coeff 2))
    (hcompat : ∀ q ∈ V, ∀ m j : ℤ,
      NLS.Coeff.positiveIndexWeight m^2*(R q (lp.single 2 j 1)) m =
        NLS.Coeff.positiveIndexWeight j^2*(Q q (lp.single 2 j 1)) m) (n : ℕ+) :
    ∃ U : Set (NLS.LinearVolterra.Curve ℂ), ∃ s : NLS.LinearVolterra.Curve ℂ → NLS.Coeff 2,
      U ⊆ V ∧ IsOpen U ∧ 0 ∈ U ∧ s 0 = 0 ∧ AnalyticOnNhd ℂ s U ∧
      (∀ k : ℕ+, AnalyticOnNhd ℂ (fun q => classicalHillCandidateEnergy N k (s q,q)) U) ∧
      (∀ k : ℕ+, classicalHillCandidateEnergy N k (s 0,0) = freeHillEnergy k) ∧
      ∀ q ∈ U, ‖s q‖ < Real.pi/16 ∧
        (∀ j : ℤ, j ≤ 0 ∨ j = (n : ℤ) → s q j = 0) ∧
        Function.Injective (fun k : ℕ+ => classicalHillCandidateEnergy N k (s q,q)) ∧
        ∀ k : ℕ+, k ≠ n →
          classicalHillNormalizedNumerator N R n (classicalHillCandidateEnergy N k (s q,q),q) = 0 := by
  obtain ⟨s,U,hUV,hU,h0U,hs0,hsa,hs⟩ := D.exists_analytic_normalized_root_displacements Q hQa hQ hQ0 n
  have ht (q : NLS.LinearVolterra.Curve ℂ) (hq : q ∈ U) : (s q,q) ∈ classicalHillCandidateDomain V :=
    ⟨by simpa only [mem_ball,dist_zero_right] using (hs q hq).1,hUV hq⟩
  refine ⟨U,s,hUV,hU,h0U,hs0,hsa,?_,?_,?_⟩
  · intro k q hq
    exact (D.candidate_energy_analytic k (s q,q) (ht q hq)).comp
      (f := fun a : NLS.LinearVolterra.Curve ℂ => (s a,a)) ((hsa q hq).prod analyticAt_id)
  · intro k
    rw [classicalHillCandidateEnergy,classicalHillCandidateFrequency,hs0,lp.coeFn_zero,
      Pi.zero_apply,add_zero,classicalHillCriticalFrequency,sq_sqrt,D.critical_free]
  intro q hq
  refine ⟨(hs q hq).1,?_,D.candidate_energies_injective (s q,q) (ht q hq),?_⟩
  · intro j hj
    have ha := D.zeroMap_auxiliary Q hQa hQ n (s q,q) (ht q hq) j hj
    rw [(hs q hq).2] at ha
    simpa only [lp.coeFn_zero,Pi.zero_apply] using ha.symm
  intro k hkn
  exact D.normalizedNumerator_zero_of_zeroMap R Q hQa hQ n k hkn (s q,q) (ht q hq) (hcompat q (hUV hq)) (hs q hq).2

end ClassicalAllContourPeriodData

/-- One constructed normalization neighborhood precedes the omitted mode;
for each mode a subneighborhood supports its entire infinite analytic zero
sequence. All original exact normalization periods are retained. -/
theorem exists_classicalHill_local_normalized_zeros :
    ∃ N : ℕ, ∃ V : Set (NLS.LinearVolterra.Curve ℂ),
      ∃ R : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2),
        0 < N ∧ IsOpen V ∧ 0 ∈ V ∧ AnalyticOnNhd ℂ R V ∧
        R 0 = ContinuousLinearMap.id ℂ (NLS.Coeff 2) ∧
        (∀ n k : ℕ+, ∀ q ∈ V,
          (2*(Real.pi : ℂ))⁻¹ * ∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
            classicalHillNormalizedNumerator N R n (z^2,q)/classicalHillContinuedRoot (z^2,q)*(2*z) =
              if n = k then 1 else 0) ∧
        ∀ n : ℕ+, ∃ U : Set (NLS.LinearVolterra.Curve ℂ), ∃ s : NLS.LinearVolterra.Curve ℂ → NLS.Coeff 2,
          U ⊆ V ∧ IsOpen U ∧ 0 ∈ U ∧ s 0 = 0 ∧ AnalyticOnNhd ℂ s U ∧
          (∀ k : ℕ+, AnalyticOnNhd ℂ (fun q => classicalHillCandidateEnergy N k (s q,q)) U) ∧
          (∀ k : ℕ+, classicalHillCandidateEnergy N k (s 0,0) = freeHillEnergy k) ∧
          ∀ q ∈ U, ‖s q‖ < Real.pi/16 ∧
            (∀ j : ℤ, j ≤ 0 ∨ j = (n : ℤ) → s q j = 0) ∧
            Function.Injective (fun k : ℕ+ => classicalHillCandidateEnergy N k (s q,q)) ∧
            ∀ k : ℕ+, k ≠ n →
              classicalHillNormalizedNumerator N R n (classicalHillCandidateEnergy N k (s q,q),q) = 0 := by
  obtain ⟨N,V,T,R,S,Q,hN,hV,h0V,_,hRa,_,hQa,_,hR0,_,hQ0,hinv,hentry,hcompat,A,D⟩ :=
    exists_classicalHill_twoWeighted_period_inverse
  refine ⟨N,V,R,hN,hV,h0V,hRa,hR0,?_,?_⟩
  · intro n k q hq
    exact D.normalizedNumerator_period n k q hq T R (fun m j => (hentry q hq m j).1) (hinv q hq).1
  intro n
  exact D.exists_actual_normalized_zero_family R Q hQa (fun q hq => (hinv q hq).2.2.2.2.2) hQ0 hcompat n

end NLS.KdV
