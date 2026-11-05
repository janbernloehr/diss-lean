import NLS.KdV.HillCriticalCentralCensus
import NLS.SequenceSpaces.IntegerSymmetricSums
import NLS.ZakharovShabat.DiscriminantDerivativeProduct

/-! # Complete original signed critical-frequency labels, l2 displacements and their normalized entire product. -/

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
open NLS.ZakharovShabat NLS.ComplexAnalysis
namespace NLS.KdV
def hillSignedCriticalFrequency
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℤ) : ℂ :=
  if n = 0 then 0 else if n < 0 then -Complex.sqrt (hillGapCriticalPoint q hq hr n.natAbs)
    else Complex.sqrt (hillGapCriticalPoint q hq hr n.natAbs)

@[simp] theorem hillSignedCriticalFrequency_natSucc
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (k : ℕ) :
    hillSignedCriticalFrequency q hq hr ((k+1 : ℕ) : ℤ) = Complex.sqrt (hillGapCriticalPoint q hq hr (k+1)) := by
  unfold hillSignedCriticalFrequency
  rw [if_neg (by omega : ((k+1 : ℕ) : ℤ) ≠ 0),if_neg (by omega : ¬((k+1 : ℕ) : ℤ) < 0),Int.natAbs_natCast]

@[simp] theorem hillSignedCriticalFrequency_negNatSucc
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (k : ℕ) :
    hillSignedCriticalFrequency q hq hr (-((k+1 : ℕ) : ℤ)) = -Complex.sqrt (hillGapCriticalPoint q hq hr (k+1)) := by
  unfold hillSignedCriticalFrequency
  rw [if_neg (by omega : -((k+1 : ℕ) : ℤ) ≠ 0),if_pos (by omega : -((k+1 : ℕ) : ℤ) < 0),
    Int.natAbs_neg,Int.natAbs_natCast]

theorem hillSignedCriticalFrequency_sq_of_ne_zero
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℤ) (hn : n ≠ 0) :
    hillSignedCriticalFrequency q hq hr n^2 = (hillGapCriticalPoint q hq hr n.natAbs : ℂ) := by
  have hs : (Complex.sqrt (hillGapCriticalPoint q hq hr n.natAbs))^2 = (hillGapCriticalPoint q hq hr n.natAbs : ℂ) := by
    have h := Complex.cpow_nat_inv_pow (hillGapCriticalPoint q hq hr n.natAbs : ℂ) (Nat.succ_ne_zero 1)
    norm_num at h
    simpa only [Complex.sqrt,one_div] using h
  unfold hillSignedCriticalFrequency
  rw [if_neg hn]
  split_ifs <;> simpa only [neg_sq] using hs

theorem hillSignedCriticalFrequency_is_critical
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℤ) :
    deriv (canonicalDiscriminant (by simp : (2 : ℝ≥0∞) ≠ ⊤)
      (hillL2CoefficientPotential (SpectralWeight.one.toCoeff q))) (hillSignedCriticalFrequency q hq hr n) = 0 := by
  rw [deriv_canonicalDiscriminant_hillL2CoefficientPotential]
  by_cases hn : n = 0
  · subst n
    simp only [hillSignedCriticalFrequency,if_true,mul_zero,zero_mul]
  · rw [hillSignedCriticalFrequency_sq_of_ne_zero q hq hr n hn,
      (hillGapCriticalPoint_spec q hq hr n.natAbs (by omega)).2,mul_zero]

theorem sum_hillSignedCriticalFrequency_central
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (N : ℕ) :
    (∑ n ∈ Finset.Icc (-(N : ℤ)) N, ({hillSignedCriticalFrequency q hq hr n} : Multiset ℂ)) =
      hillCentralGapCriticalRoots q hq hr N := by
  rw [NLS.SequenceSpaces.sum_symmetric_interval]
  have hk (k : ℕ) : (k : ℤ)+1 = ((k+1 : ℕ) : ℤ) := by omega
  simp only [hk,hillSignedCriticalFrequency_natSucc,hillSignedCriticalFrequency_negNatSucc]
  change ({0} : Multiset ℂ)+∑ k ∈ Finset.range N,
    ({Complex.sqrt (hillGapCriticalPoint q hq hr (k+1))}+
      {-Complex.sqrt (hillGapCriticalPoint q hq hr (k+1))}) = _
  rfl

theorem hillSignedCriticalFrequency_mem_high_disc
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℤ)
    (hn : 2 ≤ n.natAbs) (hcut : 16*‖q‖ ≤ (n.natAbs : ℝ)) :
    hillSignedCriticalFrequency q hq hr n ∈ refinedResonantDisk n := by
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n.natAbs ≠ 0)
  have hk' : n.natAbs = k+1 := hk
  have hncase : n = ((k+1 : ℕ) : ℤ) ∨ n = -((k+1 : ℕ) : ℤ) := by omega
  have hpos : (0 : ℝ) < (k+1 : ℕ) := by positivity
  have hc : 0 < Real.pi*(k+1 : ℕ) := mul_pos Real.pi_pos hpos
  have hsmall : 4*‖q‖/(Real.pi*(k+1 : ℕ)) < Real.pi/4 := by
    apply (div_lt_iff₀ hc).mpr
    rw [hk'] at hcut
    have hp := mul_pos (show 0 < Real.pi^2-2 by nlinarith [Real.pi_gt_three]) hpos
    nlinarith
  have hbd := (hillGapCriticalPoint_sqrt_frequency_bound q hq hr (k+1) (by omega)
    (by simpa only [hk'] using hcut)).trans_lt hsmall
  rcases hncase with rfl | rfl
  · simpa only [refinedResonantDisk,mem_ball,dist_eq_norm,hillSignedCriticalFrequency_natSucc,Int.cast_natCast] using hbd
  · simp only [refinedResonantDisk,mem_ball,dist_eq_norm]
    rw [hillSignedCriticalFrequency_negNatSucc]
    simp only [Int.cast_neg,Int.cast_natCast]
    rw [show -Complex.sqrt (hillGapCriticalPoint q hq hr (k+1))-(Real.pi : ℂ)*(-((k+1 : ℕ) : ℂ)) =
      -(Complex.sqrt (hillGapCriticalPoint q hq hr (k+1))-(Real.pi : ℂ)*(k+1 : ℕ)) by ring,norm_neg]
    exact hbd


theorem exists_hillSignedCriticalFrequency_labeling
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) :
    ∃ N : ℕ, CriticalPointLabeling (by simp : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num : 1 < (2 : ℝ≥0∞))
      (hillL2CoefficientPotential (SpectralWeight.one.toCoeff q)) (hillL2CoefficientPotential_even _) N
      (hillSignedCriticalFrequency q hq hr) := by
  let φ := hillL2CoefficientPotential (SpectralWeight.one.toCoeff q)
  obtain ⟨N0,_,U,_,_,hφ,_,hdata⟩ := exists_uniform_discriminant_critical_distribution
    (by simp : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num : 1 < (2 : ℝ≥0∞)) φ
    (r := Real.pi/4) (by positivity) le_rfl
  obtain ⟨hd,hcount,hex⟩ := hdata φ hφ (hillL2CoefficientPotential_even _)
  let N := max N0 (hillRealLabelCutoff q)
  have hN0 : N0 ≤ N := le_max_left _ _
  have hN : 2 ≤ N := (hillRealLabelCutoff_ge_two q).trans (le_max_right _ _)
  have hcut : 16*‖q‖ ≤ (N : ℝ) := (hillRealLabelCutoff_bound q).trans
    (by exact_mod_cast (le_max_right N0 (hillRealLabelCutoff q)))
  have hcentral := (sum_hillSignedCriticalFrequency_central q hq hr N).trans
    (hillCentralGapCriticalRoots_eq_original q hq hr N hN hcut (hcount N hN0).1)
  have hfar (n : ℤ) (hn : N < n.natAbs) :
      hillSignedCriticalFrequency q hq hr n ∈ ball ((Real.pi : ℂ)*n) (Real.pi/4) ∧
      deriv (canonicalDiscriminant (by simp : (2 : ℝ≥0∞) ≠ ⊤) φ) (hillSignedCriticalFrequency q hq hr n) = 0 ∧
      analyticOrderAt (deriv (canonicalDiscriminant (by simp : (2 : ℝ≥0∞) ≠ ⊤) φ)) (hillSignedCriticalFrequency q hq hr n) = 1 ∧
      ∀ z ∈ closedBall ((Real.pi : ℂ)*n) (Real.pi/4),
        deriv (canonicalDiscriminant (by simp : (2 : ℝ≥0∞) ≠ ⊤) φ) z = 0 ↔ z = hillSignedCriticalFrequency q hq hr n := by
    obtain ⟨x,hx,hcrit,horder,hunique⟩ := hd n (lt_of_le_of_lt hN0 hn)
    have hmem := hillSignedCriticalFrequency_mem_high_disc q hq hr n (by omega)
      (hcut.trans (by exact_mod_cast hn.le))
    have he : hillSignedCriticalFrequency q hq hr n = x :=
      (hunique _ (ball_subset_closedBall hmem)).mp (hillSignedCriticalFrequency_is_critical q hq hr n)
    rw [he]
    exact ⟨hx,hcrit,horder,hunique⟩
  refine ⟨N,hcentral,hfar,?_⟩
  intro z
  constructor
  · intro hz
    rcases hex N hN0 z hz with hc | ⟨n,hn,hzn⟩
    · have hm := (mem_centralCriticalRoots (by simp : (2 : ℝ≥0∞) ≠ ⊤)
        (by norm_num : 1 < (2 : ℝ≥0∞)) φ (hillL2CoefficientPotential_even _) N z).mpr
        ⟨ball_subset_closedBall hc,hz⟩
      rw [← hcentral] at hm
      simp only [Multiset.mem_sum,Multiset.mem_singleton] at hm
      obtain ⟨n,_,he⟩ := hm
      exact ⟨n,he.symm⟩
    · exact ⟨n,((hfar n hn).2.2.2 z (ball_subset_closedBall hzn)).mp hz |>.symm⟩
  · rintro ⟨n,rfl⟩
    exact hillSignedCriticalFrequency_is_critical q hq hr n

theorem memℓp_hillGapCriticalPoint_sqrt_displacement
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) :
    Memℓp (fun k : ℕ => Complex.sqrt (hillGapCriticalPoint q hq hr (k+1))-(Real.pi : ℂ)*(k+1 : ℕ)) 2 := by
  rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_ofNat,Real.rpow_two]
  have hs0 : Summable (fun n : ℕ => 1/(n : ℝ)^2) := Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hs : Summable (fun k : ℕ => (4*‖q‖/Real.pi)^2/((k+1 : ℕ) : ℝ)^2) := by
    simpa only [div_eq_mul_inv,one_mul] using ((summable_nat_add_iff 1).mpr hs0).mul_left ((4*‖q‖/Real.pi)^2)
  apply hs.of_norm_bounded_eventually_nat
  obtain ⟨N,hN⟩ := exists_nat_gt (16*‖q‖+2)
  filter_upwards [eventually_ge_atTop N] with k hk
  have hkR : (N : ℝ) ≤ k := by exact_mod_cast hk
  have hn2 : 2 ≤ k+1 := by
    have hn : (2 : ℝ) < k := by linarith [norm_nonneg q]
    exact_mod_cast (show (2 : ℝ) ≤ (k+1 : ℕ) by push_cast; linarith)
  have hcut : 16*‖q‖ ≤ (k+1 : ℕ) := by push_cast; linarith
  have hbound : ‖Complex.sqrt (hillGapCriticalPoint q hq hr (k+1))-(Real.pi : ℂ)*(k+1 : ℕ)‖ ≤
      4*‖q‖/(Real.pi*(k+1 : ℕ)) := by
    exact hillGapCriticalPoint_sqrt_frequency_bound q hq hr (k+1) hn2 hcut
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hbound 2
  simpa only [div_pow,mul_pow,div_div] using hsq


theorem memℓp_hillSignedCriticalFrequency_displacement
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) :
    Memℓp (fun n : ℤ => hillSignedCriticalFrequency q hq hr n-(Real.pi : ℂ)*n) 2 := by
  have hs := (memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)).mp
    (memℓp_hillGapCriticalPoint_sqrt_displacement q hq hr)
  simp only [ENNReal.toReal_ofNat,Real.rpow_two] at hs
  rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_ofNat,Real.rpow_two]
  apply Summable.of_nat_of_neg
  · apply (summable_nat_add_iff 1).mp
    simpa only [hillSignedCriticalFrequency_natSucc,Int.cast_natCast] using hs
  · apply (summable_nat_add_iff 1).mp
    convert! hs using 1
    funext k
    rw [hillSignedCriticalFrequency_negNatSucc]
    simp only [Int.cast_neg,Int.cast_natCast]
    rw [show -Complex.sqrt (hillGapCriticalPoint q hq hr (k+1))-(Real.pi : ℂ)*(-((k+1 : ℕ) : ℂ)) =
      -(Complex.sqrt (hillGapCriticalPoint q hq hr (k+1))-(Real.pi : ℂ)*(k+1 : ℕ)) by ring,norm_neg]




theorem entireSingleSpectralProduct_hillSignedCriticalFrequency
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (z : ℂ) :
    entireSingleSpectralProduct (hillSignedCriticalFrequency q hq hr) z =
      deriv (canonicalDiscriminant (by simp : (2 : ℝ≥0∞) ≠ ⊤)
        (hillL2CoefficientPotential (SpectralWeight.one.toCoeff q))) z := by
  obtain ⟨N,hN⟩ := exists_hillSignedCriticalFrequency_labeling q hq hr
  exact hN.product_eq_derivative (memℓp_hillSignedCriticalFrequency_displacement q hq hr) z



end NLS.KdV
