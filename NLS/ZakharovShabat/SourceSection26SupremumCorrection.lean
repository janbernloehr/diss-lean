import NLS.ZakharovShabat.SobolevSourceFourierSums
import NLS.ZakharovShabat.SourceSection26Original

/-! # The supremum endpoint in (5.11) is false

Finite Fourier sums have uniformly bounded physical H¹ norm and nonzero
mass, while their first derivatives grow without bound. Thus the printed
m=i=1 estimate has no source-independent constant, even on real H²
sources whose first derivative is continuous.
-/
noncomputable section
open scoped BigOperators ENNReal
namespace NLS.ZakharovShabat

/-- Frequencies 1 through N², with amplitudes 1/(Nn). -/
def section26EndpointBlock (N : ℕ) : ScalarSobolev 2 :=
  sobolevSourceFourierSum 2 (Finset.Icc 1 ((N:ℤ)^2)) (fun n => 1/((N:ℝ)*(n:ℝ)))

/-- Adding a constant mode keeps the scalar mass bounded away from zero. -/
def section26EndpointSource (N : ℕ) : ScalarSobolev 2 := sobolevSourceScalarMode 2 0 1+section26EndpointBlock N

/-- The block has a uniform physical H¹ energy bound. -/
theorem section26EndpointBlock_pi_sq (N : ℕ) (hN : 1 ≤ N) :
    ‖sourcePiSobolevScalar 2 1 (by omega) (section26EndpointBlock N)‖^2 ≤ (1+2*Real.pi)^2 := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  rw [section26EndpointBlock,sobolevSourceFourierSum_pi_sq]
  have hterm (n : ℤ) (hn : n ∈ Finset.Icc 1 ((N:ℤ)^2)) :
      ((1+2*Real.pi*|(n:ℝ)|)^1*(1/((N:ℝ)*n)))^2 ≤ ((1+2*Real.pi)/(N:ℝ))^2 := by
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hn0 : (0:ℝ) < n := by linarith
    simp only [pow_one,abs_of_pos hn0]
    apply pow_le_pow_left₀ (by positivity)
    rw [mul_one_div,div_le_div_iff₀ (mul_pos hN0 hn0) hN0]
    nlinarith [Real.pi_pos]
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 ((N:ℤ)^2), ((1+2*Real.pi)/(N:ℝ))^2 := Finset.sum_le_sum hterm
    _ = (N:ℝ)^2*((1+2*Real.pi)/(N:ℝ))^2 := by
      have hc : (Finset.Icc 1 ((N:ℤ)^2)).card = N^2 := by
        rw [Int.card_Icc,← Nat.cast_pow]
        omega
      simp only [Finset.sum_const,nsmul_eq_mul,hc,Nat.cast_pow]
    _ = _ := by field_simp

/-- The block first derivative at zero grows linearly with N. -/
theorem section26EndpointBlock_jet_zero (N : ℕ) (hN : 1 ≤ N) :
    hierarchySobolevJetContinuous 2 1 (by omega) (section26EndpointBlock N) 0 =
      2*Complex.I*(Real.pi:ℂ)*N := by
  have hN0 : (N:ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  rw [section26EndpointBlock,sobolevSourceFourierSum_jet_zero]
  have he (n : ℤ) (hn : n ∈ Finset.Icc 1 ((N:ℤ)^2)) :
      2*Complex.I*(Real.pi:ℂ)*n*(1/((N:ℝ)*(n:ℝ)):ℝ) = 2*Complex.I*(Real.pi:ℂ)/N := by
    have hn0 : (n:ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by have := (Finset.mem_Icc.mp hn).1; omega)
    push_cast
    field_simp
  rw [Finset.sum_congr rfl he]
  simp only [Finset.sum_const,nsmul_eq_mul]
  have hc : ((Finset.Icc 1 ((N:ℤ)^2)).card:ℂ) = (N:ℂ)^2 := by
    have hc' : (Finset.Icc 1 ((N:ℤ)^2)).card = N^2 := by
      rw [Int.card_Icc,← Nat.cast_pow]
      omega
    rw [hc',Nat.cast_pow]
  rw [hc]
  field_simp

/-- The full source has a uniform physical H¹ norm bound. -/
theorem section26EndpointSource_H1 (N : ℕ) (hN : 1 ≤ N) :
    ‖sourcePiSobolevScalar 2 1 (by omega) (section26EndpointSource N)‖ ≤ 2+2*Real.pi := by
  have hb := section26EndpointBlock_pi_sq N hN
  have hb' : ‖sourcePiSobolevScalar 2 1 (by omega) (section26EndpointBlock N)‖ ≤ 1+2*Real.pi := by
    nlinarith [norm_nonneg (sourcePiSobolevScalar 2 1 (by omega) (section26EndpointBlock N)), Real.pi_pos]
  have he : sourcePiSobolevScalar 2 1 (by omega) (section26EndpointSource N) =
      sourcePiSobolevScalar 2 1 (by omega) (sobolevSourceScalarMode 2 0 1)+
      sourcePiSobolevScalar 2 1 (by omega) (section26EndpointBlock N) := by
    ext j; simp [section26EndpointSource,WeightedCoeff.add_val,mul_add]
  rw [he]
  apply (norm_add_le _ _).trans
  have h0 := norm_sobolevSourceScalarMode_piCoordinates 2 1 (by omega) 0 1
  norm_num at h0
  rw [h0]
  linarith

/-- The constant coefficient gives a scalar mass lower bound of one. -/
theorem section26EndpointSource_mass (N : ℕ) :
    1 ≤ ‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg 2) (section26EndpointSource N)‖ := by
  have hb : WeightedCoeff.sobolevToL2 (Nat.cast_nonneg 2) (section26EndpointBlock N) 0 = 0 := by
    rw [section26EndpointBlock,sobolevSourceFourierSum_L2]
    simp only [lp.coeFn_sum,Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro j hj
    have hj0 : j ≠ 0 := by have := (Finset.mem_Icc.mp hj).1; omega
    simp [lp.single_apply,Ne.symm hj0]
  have h0 : WeightedCoeff.sobolevToL2 (Nat.cast_nonneg 2) (section26EndpointSource N) 0 = 1 := by
    simp only [section26EndpointSource,map_add,lp.coeFn_add,Pi.add_apply,sobolevSourceScalarMode_L2,hb,
      lp.single_apply,Pi.single_eq_same,add_zero,Complex.ofReal_one]
  have h := lp.norm_apply_le_norm (by norm_num : (2:ENNReal) ≠ 0)
    (WeightedCoeff.sobolevToL2 (Nat.cast_nonneg 2) (section26EndpointSource N)) 0
  simpa only [h0,norm_one] using h

/-- Exact growth of the physical derivative at zero. -/
theorem section26EndpointSource_jet_zero_norm (N : ℕ) (hN : 1 ≤ N) :
    ‖hierarchySobolevJetContinuous 2 1 (by omega) (section26EndpointSource N) 0‖ = 2*Real.pi*N := by
  rw [section26EndpointSource,map_add,ContinuousMap.add_apply,sobolevSourceScalarMode_firstJet_zero,section26EndpointBlock_jet_zero N hN]
  simp [abs_of_nonneg Real.pi_pos.le,mul_assoc]

/-- Every nonnegative proposed constant fails on an actual H² scalar source. -/
theorem section26_supremum_scalar_counterexample (C : ℝ) (hC : 0 ≤ C) :
    ∃ a : ScalarSobolev 2,
      1 ≤ ‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg 2) a‖ ∧
      ‖sourcePiSobolevScalar 2 1 (by omega) a‖ ≤ 2+2*Real.pi ∧
      C*‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg 2) a‖^(-(1/2:ℝ))*
        ‖sourcePiSobolevScalar 2 1 (by omega) a‖^(3/2:ℝ) <
          ‖hierarchySobolevJetContinuous 2 1 (by omega) a‖ := by
  let B : ℝ := 2+2*Real.pi
  have hB : 0 ≤ B := by dsimp [B]; positivity
  obtain ⟨N,hN⟩ := exists_nat_gt (C*B^(3/2:ℝ)+1)
  have hn1 : (1:ℝ) < N := by
    have hp : 0 ≤ C*B^(3/2:ℝ) := by positivity
    linarith
  have hn : 1 ≤ N := by exact_mod_cast hn1.le
  let a := section26EndpointSource N
  have hL : ‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg 2) a‖^(-(1/2:ℝ)) ≤ 1 := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow_of_nonpos
      zero_lt_one (section26EndpointSource_mass N) (by norm_num : -(1/2:ℝ) ≤ 0)
  have hP : ‖sourcePiSobolevScalar 2 1 (by omega) a‖^(3/2:ℝ) ≤ B^(3/2:ℝ) :=
    Real.rpow_le_rpow (norm_nonneg _) (section26EndpointSource_H1 N hn) (by norm_num)
  have hb : C*‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg 2) a‖^(-(1/2:ℝ))*
      ‖sourcePiSobolevScalar 2 1 (by omega) a‖^(3/2:ℝ) ≤ C*B^(3/2:ℝ) := by
    simpa only [mul_one] using mul_le_mul (mul_le_mul_of_nonneg_left hL hC) hP
      (by positivity) (by positivity)
  have hjet := (hierarchySobolevJetContinuous 2 1 (by omega) a).norm_coe_le_norm 0
  have he := section26EndpointSource_jet_zero_norm N hn
  change ‖hierarchySobolevJetContinuous 2 1 (by omega) a 0‖ = 2*Real.pi*N at he
  rw [he] at hjet
  refine ⟨a,section26EndpointSource_mass N,section26EndpointSource_H1 N hn,?_⟩
  have hp : 1 < 2*Real.pi := by linarith [Real.pi_gt_three]
  nlinarith

/-- Every proposed constant fails on an original real source with a continuous first derivative. -/
theorem section26_supremum_real_counterexample (C : ℝ) (hC : 0 ≤ C) :
    ∃ a : realTypeHigherSobolevSourceLocus 2,
      1 ≤ ‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg 2) a.val.1‖ ∧
      ‖sourcePiSobolevScalar 2 1 (by omega) a.val.1‖ ≤ 2+2*Real.pi ∧
      C*‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg 2) a.val.1‖^(-(1/2:ℝ))*
        ‖sourcePiSobolevScalar 2 1 (by omega) a.val.1‖^(3/2:ℝ) <
          ‖hierarchySobolevJetContinuous 2 1 (by omega) a.val.1‖ := by
  obtain ⟨a,hL,hH,ha⟩ := section26_supremum_scalar_counterexample C hC
  exact ⟨sobolevSourceRealCompletion 2 a,hL,hH,ha⟩

/-- The printed m=i=1 supremum estimate has no uniform nonnegative constant. -/
theorem section26_supremum_no_uniform_constant :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ a : realTypeHigherSobolevSourceLocus 2,
      ‖hierarchySobolevJetContinuous 2 1 (by omega) a.val.1‖ ≤
        C*‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg 2) a.val.1‖^(-(1/2:ℝ))*
          ‖sourcePiSobolevScalar 2 1 (by omega) a.val.1‖^(3/2:ℝ) := by
  rintro ⟨C,hC,hbound⟩
  obtain ⟨a,_,_,ha⟩ := section26_supremum_real_counterexample C hC
  exact (not_le_of_gt ha) (hbound a)

/-- The same endpoint obstruction occurs in every retained original domain, with nonzero mass. -/
theorem SourceSection26Data.supremum_counterexample
    {W₀ W V Wa B U T : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    {D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s}
    {A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa s}
    (Q : SourceSection26Data D A B U T) (C : ℝ) (hC : 0 ≤ C) :
    ∃ a : realTypeHigherSobolevSourceLocus 2,
      higherSobolevSourceInclusion 2 a.val ∈ U ∩ T ∧
      1 ≤ ‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg 2) a.val.1‖ ∧
      ‖sourcePiSobolevScalar 2 1 (by omega) a.val.1‖ ≤ 2+2*Real.pi ∧
      C*‖WeightedCoeff.sobolevToL2 (Nat.cast_nonneg 2) a.val.1‖^(-(1/2:ℝ))*
        ‖sourcePiSobolevScalar 2 1 (by omega) a.val.1‖^(3/2:ℝ) <
          ‖hierarchySobolevJetContinuous 2 1 (by omega) a.val.1‖ := by
  obtain ⟨a,hL,hH,ha⟩ := section26_supremum_real_counterexample C hC
  exact ⟨a,⟨Q.real_subset a.property,Q.gap_real_subset a.property⟩,hL,hH,ha⟩

end NLS.ZakharovShabat
