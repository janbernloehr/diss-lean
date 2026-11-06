import NLS.KdV.HillSignedEnergyLabels
import NLS.SequenceSpaces.IntegerSymmetricSums
import NLS.ComplexAnalysis.RealSquareRootCensus
import NLS.ZakharovShabat.CentralPeriodicRoots
import NLS.ZakharovShabat.CentralPeriodicOrdering

/-! # Actual central signed energy-root multisets equal the original central periodic roots, with all multiplicities and a proved admissible-cutoff family. -/

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
open NLS.ZakharovShabat NLS.ComplexAnalysis NLS.SequenceSpaces
namespace NLS.KdV
def hillSignedCentralRoots
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (N : ℕ) : Multiset ℂ :=
  ∑ n ∈ Finset.Icc (-(N : ℤ)) N, {hillSignedEnergyRoot q hq hr false n,hillSignedEnergyRoot q hq hr true n}

theorem hillSignedCentralRoots_eq_energy_pairs
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (N : ℕ) :
    hillSignedCentralRoots q hq hr N = ∑ j ∈ Finset.range (2*N+1),
      ({Complex.sqrt (hillRealLabels q hq hr j),-Complex.sqrt (hillRealLabels q hq hr j)} : Multiset ℂ) := by
  classical
  rw [hillSignedCentralRoots,sum_symmetric_interval,sum_range_one_and_pairs]
  apply congrArg₂ (fun a b : Multiset ℂ => a+b)
  · rfl
  · apply Finset.sum_congr rfl
    intro k _
    have hidx : 2*k+2-1 = 2*k+1 := by omega
    have hidx' : 2*(k+1) = 2*k+2 := by omega
    have hk : (k : ℤ)+1 = ((k+1 : ℕ) : ℤ) := by omega
    simp only [hk,hillSignedEnergyRoot_natSucc,hillSignedEnergyRoot_negNatSucc,
      hillEnergyFrequencyRoot,Bool.false_eq_true,if_false,if_true,hidx,hidx']
    apply Multiset.ext.mpr
    intro z
    simp only [Multiset.count_add,Multiset.insert_eq_cons,Multiset.count_cons,Multiset.count_singleton]
    omega

theorem hillSignedEnergyRoot_mem_centralSpectrum
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (N : ℕ) (hN : 2 ≤ N) (hcut : 8*‖q‖ ≤ (N : ℝ))
    (upper : Bool) (n : ℤ) (hn : n.natAbs ≤ N) :
    hillSignedEnergyRoot q hq hr upper n ∈ centralPeriodicSpectrum
      (by simp : (2 : ℝ≥0∞) ≠ ⊤) (hillL2CoefficientPotential (SpectralWeight.one.toCoeff q)) N := by
  let j := if n = 0 then 0 else if upper then 2*n.natAbs else 2*n.natAbs-1
  have hj : j ≤ 2*N := by dsimp only [j]; split_ifs <;> omega
  have hw : hillSignedEnergyRoot q hq hr upper n^2 = (hillRealLabels q hq hr j : ℂ) := hillSignedEnergyRoot_sq q hq hr upper n
  have hground := (hillLowestEnergy_mem_centralInterval q hq hr N hN hcut).1
  change -(N : ℝ)^2 < hillRealLabels q hq hr 0 at hground
  have hlo : -(N : ℝ)^2 < hillRealLabels q hq hr j :=
    hground.trans_le (monotone_hillRealLabels q hq hr (Nat.zero_le j))
  obtain ⟨p,_,hu⟩ := hillRealLabels_high_pair q hq hr N hN hcut
  have hp := (abs_le.mp (p.localization q hq N (by omega) hcut).2).2
  have htop : hillRealLabels q hq hr (2*N) ≤ Real.pi^2*(N : ℝ)^2+4*‖q‖ := by
    rw [hu]
    simpa only [freeHillValue,Int.cast_natCast] using (show p.right ≤ freeHillValue N+4*‖q‖ by linarith)
  have hcross : (N : ℝ) ≤ Real.pi^2*N := by
    have h := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ Real.pi^2 by nlinarith [Real.pi_gt_three]) (Nat.cast_nonneg (α := ℝ) N)
    simpa only [one_mul] using h
  have hup : hillRealLabels q hq hr j < ((N : ℝ)*Real.pi+Real.pi/2)^2 := by
    have hjtop := (monotone_hillRealLabels q hq hr hj).trans htop
    nlinarith [Real.pi_gt_three]
  have hcoord := square_root_real_coordinate_bounds (hillSignedEnergyRoot q hq hr upper n)
    (hillRealLabels q hq hr j) ((N : ℝ)*Real.pi+Real.pi/2) (N : ℝ)
    (by positivity) (by exact_mod_cast (show 0 < N by omega)) hw hlo hup
  rw [mem_centralPeriodicSpectrum]
  refine ⟨?_,⟨hcoord.1,hcoord.2.le⟩⟩
  apply (periodicSpectrum_hillSignedEnergyRoots q hq hr _).mpr
  cases upper with
  | false => exact ⟨n,Or.inl rfl⟩
  | true => exact ⟨n,Or.inr rfl⟩

theorem count_hillSignedCentralRoots_of_sq_real
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (N : ℕ) (z : ℂ) (x : ℝ)
    (hx : z^2 = (x : ℂ)) :
    (hillSignedCentralRoots q hq hr N).count z = (if z = 0 then 2 else 1)*
      (∑ j ∈ Finset.range (2*N+1), if hillRealLabels q hq hr j = x then (1 : ℕ) else 0) := by
  classical
  rw [hillSignedCentralRoots_eq_energy_pairs,Multiset.count_sum']
  simp_rw [count_opposite_square_root_pair]
  have he (j : ℕ) : (Complex.sqrt (hillRealLabels q hq hr j))^2 = z^2 ↔ hillRealLabels q hq hr j = x := by
    have hs : (Complex.sqrt (hillRealLabels q hq hr j))^2 = (hillRealLabels q hq hr j : ℂ) := by
      have h := Complex.cpow_nat_inv_pow (hillRealLabels q hq hr j : ℂ) (Nat.succ_ne_zero 1)
      norm_num at h
      simpa only [Complex.sqrt,one_div] using h
    rw [hs,hx,Complex.ofReal_inj]
  simp_rw [he]
  rw [Finset.mul_sum]

theorem hillEnergy_occurrence_sum_le_full
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (N : ℕ) (x : ℝ) :
    (∑ j ∈ Finset.range (2*N+1), if hillRealLabels q hq hr j = x then (1 : ℕ) else 0) ≤
      ∑ᶠ j : ℕ, if hillRealLabels q hq hr j = x then (1 : ℕ) else 0 := by
  classical
  let f : ℕ → ℕ := fun j => if hillRealLabels q hq hr j = x then 1 else 0
  have hfin := (hillRealLabels_global_multiplicity q hq hr x).1
  let T := hfin.toFinset ∪ Finset.range (2*N+1)
  have hsub : Function.support f ⊆ (T : Set ℕ) := by
    intro j hj
    by_cases he : hillRealLabels q hq hr j = x
    · exact Finset.mem_union_left _ (hfin.mem_toFinset.mpr he)
    · exact False.elim (hj (by simp only [f,if_neg he]))
  change (∑ j ∈ Finset.range (2*N+1), f j) ≤ ∑ᶠ j : ℕ, f j
  rw [finsum_eq_sum_of_support_subset f hsub]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right (fun _ _ _ => Nat.zero_le _)

theorem hillSignedCentralRoots_le_original
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (N : ℕ) (hN : 2 ≤ N) (hcut : 8*‖q‖ ≤ (N : ℝ)) :
    hillSignedCentralRoots q hq hr N ≤ centralPeriodicRoots
      (by simp : (2 : ℝ≥0∞) ≠ ⊤) (hillL2CoefficientPotential (SpectralWeight.one.toCoeff q)) N := by
  classical
  apply Multiset.le_iff_count.mpr
  intro z
  by_cases hc : (hillSignedCentralRoots q hq hr N).count z = 0
  · rw [hc]; exact Nat.zero_le _
  have hm : z ∈ hillSignedCentralRoots q hq hr N := Multiset.count_pos.mp (Nat.pos_of_ne_zero hc)
  have hcentral : z ∈ centralPeriodicSpectrum
      (by simp : (2 : ℝ≥0∞) ≠ ⊤) (hillL2CoefficientPotential (SpectralWeight.one.toCoeff q)) N := by
    have hmem := hm
    simp only [hillSignedCentralRoots,Multiset.mem_sum,Multiset.insert_eq_cons,Multiset.mem_cons,Multiset.mem_singleton] at hmem
    obtain ⟨n,hn,hz | hz⟩ := hmem
    · have hnabs : n.natAbs ≤ N := by simp only [Finset.mem_Icc] at hn; omega
      rw [hz]
      exact hillSignedEnergyRoot_mem_centralSpectrum q hq hr N hN hcut false n hnabs
    · have hnabs : n.natAbs ≤ N := by simp only [Finset.mem_Icc] at hn; omega
      rw [hz]
      exact hillSignedEnergyRoot_mem_centralSpectrum q hq hr N hN hcut true n hnabs
  have hreal : ∃ x : ℝ, z^2 = (x : ℂ) := by
    rw [hillSignedCentralRoots_eq_energy_pairs] at hm
    simp only [Multiset.mem_sum,Multiset.insert_eq_cons,Multiset.mem_cons,Multiset.mem_singleton] at hm
    obtain ⟨j,_,hz | hz⟩ := hm
    all_goals
      refine ⟨hillRealLabels q hq hr j,?_⟩
      have hs : (Complex.sqrt (hillRealLabels q hq hr j))^2 = (hillRealLabels q hq hr j : ℂ) := by
        have h := Complex.cpow_nat_inv_pow (hillRealLabels q hq hr j : ℂ) (Nat.succ_ne_zero 1)
        norm_num at h
        simpa only [Complex.sqrt,one_div] using h
      simpa only [hz,neg_sq] using hs
  obtain ⟨x,hx⟩ := hreal
  rw [count_centralPeriodicRoots,if_pos hcentral,count_hillSignedCentralRoots_of_sq_real q hq hr N z x hx,
    periodicAlgebraicMultiplicity_hill_energy_census q hq hr z x hx]
  exact Nat.mul_le_mul_left _ (hillEnergy_occurrence_sum_le_full q hq hr N x)

theorem hillSignedCentralRoots_eq_original
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (N : ℕ) (hN : 2 ≤ N) (hcut : 8*‖q‖ ≤ (N : ℝ))
    (hcount : PeriodicCountingData (by simp : (2 : ℝ≥0∞) ≠ ⊤) (hillL2CoefficientPotential (SpectralWeight.one.toCoeff q)) N) :
    hillSignedCentralRoots q hq hr N = centralPeriodicRoots
      (by simp : (2 : ℝ≥0∞) ≠ ⊤) (hillL2CoefficientPotential (SpectralWeight.one.toCoeff q)) N := by
  classical
  apply Multiset.eq_of_le_of_card_le (hillSignedCentralRoots_le_original q hq hr N hN hcut)
  rw [hcount.card_centralPeriodicRoots]
  simp [hillSignedCentralRoots,Multiset.card_sum,mul_comm]

theorem hillSignedEnergyRoot_centralLabeling
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (N : ℕ) (hN : 2 ≤ N) (hcut : 8*‖q‖ ≤ (N : ℝ))
    (hcount : PeriodicCountingData (by simp : (2 : ℝ≥0∞) ≠ ⊤) (hillL2CoefficientPotential (SpectralWeight.one.toCoeff q)) N) :
    CentralPeriodicLabeling (by simp : (2 : ℝ≥0∞) ≠ ⊤) (hillL2CoefficientPotential (SpectralWeight.one.toCoeff q)) N
      (hillSignedEnergyRoot q hq hr false) (hillSignedEnergyRoot q hq hr true) :=
  ⟨hillSignedCentralRoots_eq_original q hq hr N hN hcut hcount⟩

theorem exists_hillSignedEnergyRoot_centralLabeling
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) :
    ∃ N : ℕ, 2 ≤ N ∧ 8*‖q‖ ≤ (N : ℝ) ∧ ∀ M : ℕ, N ≤ M →
      CentralPeriodicLabeling (by simp : (2 : ℝ≥0∞) ≠ ⊤) (hillL2CoefficientPotential (SpectralWeight.one.toCoeff q)) M
        (hillSignedEnergyRoot q hq hr false) (hillSignedEnergyRoot q hq hr true) := by
  let φ := hillL2CoefficientPotential (SpectralWeight.one.toCoeff q)
  obtain ⟨N0,U,_,_,_,hφ,_,_,_,hd⟩ := exists_uniform_periodicCountingData (by simp : (2 : ℝ≥0∞) ≠ ⊤) φ
  let N := max N0 (hillRealLabelCutoff q)
  have hN : 2 ≤ N := (hillRealLabelCutoff_ge_two q).trans (le_max_right _ _)
  have hcut : 8*‖q‖ ≤ (N : ℝ) := (hillRealLabelCutoff_bound q).trans (by exact_mod_cast (le_max_right N0 (hillRealLabelCutoff q)))
  refine ⟨N,hN,hcut,?_⟩
  intro M hM
  exact hillSignedEnergyRoot_centralLabeling q hq hr M (hN.trans hM)
    (hcut.trans (by exact_mod_cast hM)) (hd φ hφ M ((le_max_left _ _).trans hM))

end NLS.KdV
