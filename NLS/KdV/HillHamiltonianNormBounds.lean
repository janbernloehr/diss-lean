import NLS.KdV.HillNativeIntegerLower

/-! # Actual Hamiltonian bounds by top and lower native Sobolev norms. -/

noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology NLS.Fourier NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.KdV
theorem hill_polynomial_norm_error (m : ℕ) (r L t : ℝ) (hr : 0 ≤ r) (hL : 0 ≤ L)
    (ht : 0 ≤ t) (h : r ≤ L*t) :
    (1+r^(2*m))*r^2 ≤ L^2*(1+L^(2*m))*((1+t)^(2*m)*t^2) := by
  have hp : 1 ≤ (1+t)^(2*m) := one_le_pow₀ (by linarith)
  have hpow : r^(2*m) ≤ L^(2*m)*(1+t)^(2*m) := by
    have h1 := pow_le_pow_left₀ hr (h.trans (show L*t ≤ L*(1+t) by nlinarith)) (2*m)
    simpa only [mul_pow] using h1
  have hf : 1+r^(2*m) ≤ (1+L^(2*m))*(1+t)^(2*m) := by nlinarith
  have hs : r^2 ≤ L^2*t^2 := by simpa only [mul_pow] using pow_le_pow_left₀ hr h 2
  have hb := mul_le_mul hf hs (sq_nonneg r) (by positivity : 0 ≤ (1+L^(2*m))*(1+t)^(2*m))
  nlinarith

theorem exists_hillNativeHamiltonianFamily_norm_bound_positive (M j : ℕ) (hj : j ≤ M)
    (hjpos : 1 ≤ j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : WeightedCoeff (hillIntegerWeight M).doubleIndex.toWeight 2,
      ‖hillSobolevHamiltonianFamily M (hillNativeIntegerToScalar M p) j‖ ≤
        C*(1+‖p‖)^(2*j)*‖p‖^2 := by
  obtain ⟨CK,hCK,hbound⟩ := exists_hillSobolevHamiltonian_norm_bound j hjpos
  let F := (hillScalarSobolevLower M j hj).comp (hillNativeIntegerToScalar M)
  let J := (hierarchySobolevJetL2 j j le_rfl).comp F
  let L := (WeightedCoeff.sobolevToL2 (Nat.cast_nonneg j)).comp F
  let C : ℝ := ‖J‖^2+CK*‖L‖^2*(1+‖L‖^(2*j))
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C,hC,?_⟩
  intro p
  have ht := hbound (F p)
  have hJ := J.le_opNorm p
  have hL := L.le_opNorm p
  have hs := pow_le_pow_left₀ (norm_nonneg (J p)) hJ 2
  rw [mul_pow] at hs
  have he := hill_polynomial_norm_error j ‖L p‖ ‖L‖ ‖p‖ (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hL
  have hp : 1 ≤ (1+‖p‖)^(2*j) := one_le_pow₀ (by linarith [norm_nonneg p])
  have hb := mul_le_mul_of_nonneg_left he hCK
  have htop := mul_le_mul_of_nonneg_right hp (mul_nonneg (sq_nonneg ‖J‖) (sq_nonneg ‖p‖))
  simp only [hillSobolevHamiltonianFamily,dif_pos hj,hillSobolevHamiltonianAt,
    dif_neg (by omega : j ≠ 0)]
  change ‖hillSobolevHamiltonian j hjpos (F p)‖ ≤ C*(1+‖p‖)^(2*j)*‖p‖^2
  change ‖hillSobolevHamiltonian j hjpos (F p)‖ ≤ ‖J p‖^2+CK*(1+‖L p‖^(2*j))*‖L p‖^2 at ht
  dsimp only [C]
  nlinarith


theorem norm_hillNativeHamiltonianFamily_zero (M : ℕ)
    (p : RealHillWeightedPotential (hillIntegerWeight M)) (hmean : p.val.val 0 = 0) :
    ‖hillSobolevHamiltonianFamily M (hillNativeIntegerToScalar M p.val) 0‖ =
      hillNativeActionMass M 0 p := by
  have ht := tsum_hillHierarchyMomentTerm_hierarchy_sobolev_of_le M 0 (Nat.zero_le M) p hmean
  have hterm (n : ℕ) : hillHierarchyMomentTerm (hillIntegerWeight M) p 0 n =
      hillGapActionTerm (hillPeriodOneUnitPotential (hillIntegerWeight M) p.val)
        (hillPeriodOneUnitPotential_even (hillIntegerWeight M) p.val)
        (hillPeriodOneUnitPotential_real (hillIntegerWeight M) p.val p.property) 0 n := by
    simp only [hillHierarchyMomentTerm,hillGapActionTerm,mul_zero,zero_add,pow_one]
  rw [funext hterm] at ht
  simp only [hillSobolevTraceValue,hillHierarchyTraceCoefficient_zero] at ht
  calc
    _ = ‖(hillNativeActionMass M 0 p : ℂ)‖ := congrArg norm ht.symm
    _ = _ := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hillNativeActionMass_nonneg M 0 p)]

theorem exists_hillNativeHamiltonianFamily_norm_bound (M j : ℕ) (hj : j ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : RealHillWeightedPotential (hillIntegerWeight M),
      p.val.val 0 = 0 → ‖hillSobolevHamiltonianFamily M (hillNativeIntegerToScalar M p.val) j‖ ≤
        C*(1+‖p.val‖)^(2*j)*‖p.val‖^2 := by
  by_cases hz : j = 0
  · subst j
    refine ⟨1,by norm_num,?_⟩
    intro p hmean
    rw [norm_hillNativeHamiltonianFamily_zero M p hmean]
    have hm := tsum_hillNativeBaseActions_eq_half_norm M p hmean
    have hb := norm_hillPeriodOneUnitPotential_le (hillIntegerWeight M) p.val
    change hillNativeActionMass M 0 p = (1/2 : ℝ)*
      ‖hillPeriodOneUnitPotential (hillIntegerWeight M) p.val‖^2 at hm
    have hs := pow_le_pow_left₀ (norm_nonneg _) hb 2
    simp only [mul_zero,pow_zero,mul_one,one_mul]
    nlinarith [sq_nonneg ‖p.val‖]
  · obtain ⟨C,hC,hbound⟩ := exists_hillNativeHamiltonianFamily_norm_bound_positive M j hj (by omega)
    exact ⟨C,hC,fun p _ => hbound p.val⟩



theorem exists_hillNativeHamiltonianTop_mixed_bound (m : ℕ) (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : WeightedCoeff (hillIntegerWeight m).doubleIndex.toWeight 2,
      let b := hillNativeIntegerLower m (m-1) (by omega) p
      ‖hillSobolevHamiltonian m hm (hillNativeIntegerToScalar m p)‖ ≤
        C*(‖p‖^2+(1+‖b‖)^(2*m)*‖b‖^2) := by
  obtain ⟨CK,hCK,hbound⟩ := exists_hillSobolevHamiltonian_norm_bound m hm
  let J := (hierarchySobolevJetL2 m m le_rfl).comp (hillNativeIntegerToScalar m)
  let C : ℝ := ‖J‖^2+2*CK
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C,hC,?_⟩
  intro p
  dsimp only
  let a := hillNativeIntegerToScalar m p
  let b := hillNativeIntegerLower m (m-1) (by omega) p
  let r := ‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) a‖
  have hr : r ≤ ‖b‖ := by
    change ‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg m) (hillNativeIntegerToScalar m p)‖ ≤ ‖b‖
    rw [← norm_hillPeriodOneUnitPotential_eq_sharedL2 m p,
      ← hillPeriodOneUnitPotential_lower m (m-1) (by omega) p]
    exact norm_hillPeriodOneUnitPotential_le (hillIntegerWeight (m-1)) b
  have he := hill_polynomial_norm_error m r 1 ‖b‖ (norm_nonneg _) (by norm_num) (norm_nonneg _)
    (by simpa only [one_mul] using hr)
  simp only [one_pow,one_mul] at he
  have hJ := pow_le_pow_left₀ (norm_nonneg (J p)) (J.le_opNorm p) 2
  rw [mul_pow] at hJ
  have ht := hbound a
  change ‖hillSobolevHamiltonian m hm a‖ ≤ ‖J p‖^2+CK*(1+r^(2*m))*r^2 at ht
  have hc := mul_le_mul_of_nonneg_left he hCK
  change ‖hillSobolevHamiltonian m hm a‖ ≤ C*(‖p‖^2+(1+‖b‖)^(2*m)*‖b‖^2)
  dsimp only [C]
  nlinarith [mul_nonneg (sq_nonneg ‖J‖) (show 0 ≤ (1+‖b‖)^(2*m)*‖b‖^2 by positivity),
    mul_nonneg hCK (sq_nonneg ‖p‖)]


end NLS.KdV
