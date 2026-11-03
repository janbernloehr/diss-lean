import NLS.KdV.HillEnergyFrequencyBounds
import NLS.KdV.HillL2HighGapPairs
import NLS.ZakharovShabat.PerturbedSpectralProducts
import NLS.ComplexAnalysis.AnalyticSquarePullback

/-! # Signed actual energy square-root labels, full frequency l2 errors, exact finite product pairing, original spectrum exhaustion and energy multiplicity census. -/

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
open NLS.ZakharovShabat NLS.ComplexAnalysis
namespace NLS.KdV
def hillSignedEnergyRoot
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (upper : Bool) (n : ℤ) : ℂ :=
  if n = 0 then (if upper then -Complex.sqrt (hillRealLabels q hq hr 0) else Complex.sqrt (hillRealLabels q hq hr 0))
  else if n < 0 then -hillEnergyFrequencyRoot q hq hr upper n.natAbs
  else hillEnergyFrequencyRoot q hq hr upper n.natAbs

@[simp] theorem hillSignedEnergyRoot_natSucc
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (upper : Bool) (k : ℕ) :
    hillSignedEnergyRoot q hq hr upper ((k+1 : ℕ) : ℤ) = hillEnergyFrequencyRoot q hq hr upper (k+1) := by
  unfold hillSignedEnergyRoot
  rw [if_neg (by omega : ((k+1 : ℕ) : ℤ) ≠ 0),if_neg (by omega : ¬((k+1 : ℕ) : ℤ) < 0)]
  rw [Int.natAbs_natCast]

@[simp] theorem hillSignedEnergyRoot_negNatSucc
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (upper : Bool) (k : ℕ) :
    hillSignedEnergyRoot q hq hr upper (-((k+1 : ℕ) : ℤ)) = -hillEnergyFrequencyRoot q hq hr upper (k+1) := by
  unfold hillSignedEnergyRoot
  rw [if_neg (by omega : -((k+1 : ℕ) : ℤ) ≠ 0),if_pos (by omega : -((k+1 : ℕ) : ℤ) < 0)]
  rw [Int.natAbs_neg,Int.natAbs_natCast]

theorem memℓp_hillSignedEnergyRoot_displacement
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (upper : Bool) :
    Memℓp (fun n : ℤ => hillSignedEnergyRoot q hq hr upper n-(Real.pi : ℂ)*n) 2 := by
  have hs := (memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)).mp
    (memℓp_hillEnergyFrequencyRoot_displacement q hq hr upper)
  simp only [ENNReal.toReal_ofNat,Real.rpow_two] at hs
  rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_ofNat,Real.rpow_two]
  apply Summable.of_nat_of_neg
  · apply (summable_nat_add_iff 1).mp
    simpa only [hillSignedEnergyRoot_natSucc,Int.cast_natCast] using hs
  · apply (summable_nat_add_iff 1).mp
    convert! hs using 1
    funext k
    rw [hillSignedEnergyRoot_negNatSucc]
    simp only [Int.cast_neg,Int.cast_natCast]
    rw [show -hillEnergyFrequencyRoot q hq hr upper (k+1)-(Real.pi : ℂ)*(-((k+1 : ℕ) : ℂ)) =
      -(hillEnergyFrequencyRoot q hq hr upper (k+1)-(Real.pi : ℂ)*(k+1 : ℕ)) by ring,norm_neg]


theorem hillEnergyFrequencyRoot_sq
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (upper : Bool) (n : ℕ) :
    hillEnergyFrequencyRoot q hq hr upper n^2 = (hillRealLabels q hq hr (if upper then 2*n else 2*n-1) : ℂ) := by
  have h := Complex.cpow_nat_inv_pow (hillRealLabels q hq hr (if upper then 2*n else 2*n-1) : ℂ) (Nat.succ_ne_zero 1)
  norm_num at h
  simpa only [hillEnergyFrequencyRoot,Complex.sqrt,one_div] using h

theorem hillSignedEnergyRoot_centralFactor
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (z : ℂ) :
    spectralPairFactor (hillSignedEnergyRoot q hq hr false) (hillSignedEnergyRoot q hq hr true) z 0 =
      z^2-hillRealLabels q hq hr 0 := by
  have hs := hillEnergyFrequencyRoot_sq q hq hr false 0
  simp only [hillEnergyFrequencyRoot, Bool.false_eq_true,if_false,mul_zero,Nat.zero_sub] at hs
  simp only [spectralPairFactor,hillSignedEnergyRoot,Bool.false_eq_true,if_false,if_true]
  linear_combination -hs

def hillEnergyPeriodicPartialProduct
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (z : ℂ) (N : ℕ) : ℂ :=
  -4*(z-hillRealLabels q hq hr 0)*∏ k ∈ Finset.range N,
    ((hillRealLabels q hq hr (2*(k+1)-1) : ℂ)-z)*((hillRealLabels q hq hr (2*(k+1)) : ℂ)-z)/(freeHillValue (k+1) : ℂ)^2

theorem hillSignedEnergyRoot_pairedFactor
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (z : ℂ) (k : ℕ) :
    spectralPairFactor (hillSignedEnergyRoot q hq hr false) (hillSignedEnergyRoot q hq hr true) z ((k+1 : ℕ) : ℤ)*
      spectralPairFactor (hillSignedEnergyRoot q hq hr false) (hillSignedEnergyRoot q hq hr true) z (-((k+1 : ℕ) : ℤ)) =
      ((hillRealLabels q hq hr (2*(k+1)-1) : ℂ)-z^2)*((hillRealLabels q hq hr (2*(k+1)) : ℂ)-z^2)/(freeHillValue (k+1) : ℂ)^2 := by
  have hL := hillEnergyFrequencyRoot_sq q hq hr false (k+1)
  have hU := hillEnergyFrequencyRoot_sq q hq hr true (k+1)
  simp only [Bool.false_eq_true,if_false,if_true] at hL hU
  simp only [spectralPairFactor,if_neg (by omega : ((k+1 : ℕ) : ℤ) ≠ 0),if_neg (by omega : -((k+1 : ℕ) : ℤ) ≠ 0),
    hillSignedEnergyRoot_natSucc,hillSignedEnergyRoot_negNatSucc]
  have hd : (freeHillValue (k+1) : ℂ)^2 = ((Real.pi : ℂ)*(k+1 : ℕ))^4 := by
    simp only [freeHillValue,ofReal_mul,ofReal_pow,ofReal_intCast]
    push_cast
    ring
  rw [hd]
  push_cast
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hk : ((k : ℂ)+1) ≠ 0 := Nat.cast_add_one_ne_zero k
  have hp := congrArg₂ (fun x y : ℂ => x*y) hL hU
  field_simp
  linear_combination hp-z^2*hL-z^2*hU

theorem spectralPairPartialProduct_hillSignedEnergyRoot
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (z : ℂ) (N : ℕ) :
    spectralPairPartialProduct (hillSignedEnergyRoot q hq hr false) (hillSignedEnergyRoot q hq hr true) z N =
      hillEnergyPeriodicPartialProduct q hq hr (z^2) N := by
  rw [spectralPairPartialProduct,prod_symmetric_interval,hillSignedEnergyRoot_centralFactor]
  have hp (k : ℕ) := hillSignedEnergyRoot_pairedFactor q hq hr z k
  simp only [Nat.cast_add,Nat.cast_one] at hp
  simp only [hp,hillEnergyPeriodicPartialProduct]
  ring

theorem hillSignedEnergyRoot_sq
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (upper : Bool) (n : ℤ) :
    hillSignedEnergyRoot q hq hr upper n^2 =
      (hillRealLabels q hq hr (if n = 0 then 0 else if upper then 2*n.natAbs else 2*n.natAbs-1) : ℂ) := by
  by_cases hn : n = 0
  · subst n
    have hs := hillEnergyFrequencyRoot_sq q hq hr false 0
    simp only [hillEnergyFrequencyRoot,Bool.false_eq_true,if_false,mul_zero,Nat.zero_sub] at hs
    cases upper <;> simpa only [hillSignedEnergyRoot,if_true,Bool.false_eq_true,if_false,neg_sq] using hs
  · simp only [hillSignedEnergyRoot,if_neg hn]
    by_cases hneg : n < 0
    · rw [if_pos hneg,neg_sq,hillEnergyFrequencyRoot_sq]
    · rw [if_neg hneg,hillEnergyFrequencyRoot_sq]

theorem exists_hillSignedEnergyRoot_of_sq_label
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (z : ℂ) (j : ℕ)
    (hz : z^2 = (hillRealLabels q hq hr j : ℂ)) :
    ∃ n : ℤ, z = hillSignedEnergyRoot q hq hr false n ∨ z = hillSignedEnergyRoot q hq hr true n := by
  let r := Complex.sqrt (hillRealLabels q hq hr j)
  have hs : r^2 = (hillRealLabels q hq hr j : ℂ) := by
    have h := Complex.cpow_nat_inv_pow (hillRealLabels q hq hr j : ℂ) (Nat.succ_ne_zero 1)
    norm_num at h
    simpa only [r,Complex.sqrt,one_div] using h
  have hm : (z-r)*(z+r) = 0 := by linear_combination hz-hs
  have hpm : z = r ∨ z = -r := by
    rcases mul_eq_zero.mp hm with hl | hu
    · exact Or.inl (sub_eq_zero.mp hl)
    · exact Or.inr (eq_neg_iff_add_eq_zero.mpr hu)
  by_cases hj : j = 0
  · rcases hpm with hp | hp
    · refine ⟨0,Or.inl ?_⟩
      change z = Complex.sqrt (hillRealLabels q hq hr 0)
      simpa only [r,hj] using hp
    · refine ⟨0,Or.inr ?_⟩
      change z = -Complex.sqrt (hillRealLabels q hq hr 0)
      simpa only [r,hj] using hp
  · let n := (j+1)/2
    have hn : 1 ≤ n := by dsimp only [n]; omega
    have hidx : j = 2*n-1 ∨ j = 2*n := by dsimp only [n]; omega
    obtain ⟨k,hkn⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    have hkn' : n = k+1 := hkn
    rw [hkn'] at hidx
    rcases hidx with hi | hi
    · have hf : hillEnergyFrequencyRoot q hq hr false (k+1) = r := by
        change Complex.sqrt (hillRealLabels q hq hr (2*(k+1)-1)) = Complex.sqrt (hillRealLabels q hq hr j)
        rw [← hi]
      rcases hpm with hp | hp
      · refine ⟨((k+1 : ℕ) : ℤ),Or.inl ?_⟩
        rw [hillSignedEnergyRoot_natSucc,hf]
        exact hp
      · refine ⟨-((k+1 : ℕ) : ℤ),Or.inl ?_⟩
        rw [hillSignedEnergyRoot_negNatSucc,hf]
        exact hp
    · have hf : hillEnergyFrequencyRoot q hq hr true (k+1) = r := by
        change Complex.sqrt (hillRealLabels q hq hr (2*(k+1))) = Complex.sqrt (hillRealLabels q hq hr j)
        rw [← hi]
      rcases hpm with hp | hp
      · refine ⟨((k+1 : ℕ) : ℤ),Or.inr ?_⟩
        rw [hillSignedEnergyRoot_natSucc,hf]
        exact hp
      · refine ⟨-((k+1 : ℕ) : ℤ),Or.inr ?_⟩
        rw [hillSignedEnergyRoot_negNatSucc,hf]
        exact hp

theorem periodicSpectrum_hillSignedEnergyRoots
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (z : ℂ) :
    z ∈ periodicSpectrum (by simp : (2 : ℝ≥0∞) ≠ ⊤) (hillL2CoefficientPotential (SpectralWeight.one.toCoeff q)) ↔
      ∃ n : ℤ, z = hillSignedEnergyRoot q hq hr false n ∨ z = hillSignedEnergyRoot q hq hr true n := by
  rw [← hillL2Radicand_sq_eq_zero_iff_periodicSpectrum, hillRealLabels_root_iff]
  constructor
  · rintro ⟨j,hj⟩
    exact exists_hillSignedEnergyRoot_of_sq_label q hq hr z j hj
  · rintro ⟨n,hz | hz⟩
    · exact ⟨_,by simpa only [hz] using hillSignedEnergyRoot_sq q hq hr false n⟩
    · exact ⟨_,by simpa only [hz] using hillSignedEnergyRoot_sq q hq hr true n⟩

theorem periodicAlgebraicMultiplicity_hill_zero_frequency (q : Coeff 2) :
    periodicAlgebraicMultiplicity (by simp : (2 : ℝ≥0∞) ≠ ⊤) (hillL2CoefficientPotential q) 0 =
      2*analyticOrderNatAt (hillL2Radicand q) 0 := by
  rw [← analyticOrderNatAt_hillL2Radicand_sq q 0]
  exact analyticOrderNatAt_comp_sq_zero _ (analyticOnNhd_hillL2Radicand q 0 (mem_univ _))

theorem periodicAlgebraicMultiplicity_hill_energy_census
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (z : ℂ) (x : ℝ)
    (hx : z^2 = (x : ℂ)) :
    periodicAlgebraicMultiplicity (by simp : (2 : ℝ≥0∞) ≠ ⊤) (hillL2CoefficientPotential (SpectralWeight.one.toCoeff q)) z =
      (if z = 0 then 2 else 1)*(∑ᶠ j : ℕ, if hillRealLabels q hq hr j = x then (1 : ℕ) else 0) := by
  rw [(hillRealLabels_global_multiplicity q hq hr x).2]
  by_cases hz : z = 0
  · subst z
    have hx0 : x = 0 := by
      have h := congrArg Complex.re hx
      simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0),zero_re,ofReal_re] using h.symm
    subst x
    simpa only [if_true,ofReal_zero] using periodicAlgebraicMultiplicity_hill_zero_frequency (SpectralWeight.one.toCoeff q)
  · simp only [if_neg hz,one_mul]
    rw [← analyticOrderNatAt_hillL2Radicand_energy _ z hz,hx]

end NLS.KdV
