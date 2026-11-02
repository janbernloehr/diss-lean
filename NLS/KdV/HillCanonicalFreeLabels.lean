import NLS.KdV.HillCanonicalRealLabels

/-! # Free normalization of the intrinsic Hill labels

The full actual ordered labeling has the source normalization at zero
potential: one lowest energy followed by each positive free energy twice.
-/

noncomputable section
open Set
namespace NLS.KdV

theorem hillRealLabels_zero_ground
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2))) :
    hillRealLabels 0 hq hreal 0 = 0 := by
  have hz : hillL2Radicand (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)) 0 = 0 := by
    rw [map_zero, hillL2Radicand_zero]
    simp
  have hhi := hillLowestEnergy_le_root 0 hq hreal 0 hz
  have hr := (hillRealLabels_spec 0 hq hreal).root 0
  rw [map_zero] at hr
  obtain ⟨k,hk⟩ := (hillL2Radicand_free_zero_iff _).mp hr
  have hk' := Complex.ofReal_injective hk
  have hhi' : hillRealLabels 0 hq hreal 0 ≤ 0 := hhi
  apply le_antisymm hhi'
  rw [hk']
  unfold freeHillValue
  positivity

theorem hillRealLabels_zero
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
    (j : ℕ) : hillRealLabels 0 hq hreal j = freeHillValue ((j+1)/2 : ℕ) := by
  let L := hillRealLabels 0 hq hreal
  have h0 := hillRealLabels_zero_ground hq hreal
  have hs := hillRealLabels_spec_at 0 hq hreal 2 (by omega) (by simp)
  have hmem0 : (0 : ℂ) ∈ hillCentralDisc 2 := by
    simpa [freeHillValue] using
      (freeHillValue_mem_hillCentralDisc_iff 2 (by omega) 0).mpr (by omega)
  have hc := hs.central_counts 0
  have hc' : 1+(if L 1 = 0 then 1 else 0)+(if L 2 = 0 then 1 else 0) = (1 : ℕ) := by
    simpa only [show 2*(2 : ℕ)-1 = 3 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add, h0, if_pos rfl, ite_true, Complex.ofReal_zero, if_pos hmem0, map_zero,
      hillL2Radicand_free_order_zero] using hc
  have h1 : L 1 ≠ 0 := by intro he; rw [if_pos he] at hc'; omega
  have h2 : L 2 ≠ 0 := by intro he; rw [if_pos he] at hc'; omega
  have hsmall (i : ℕ) (hi : i = 1 ∨ i = 2) : L i = freeHillValue (1 : ℕ) := by
    have hroot := hs.root i
    rw [map_zero] at hroot
    obtain ⟨k,hk⟩ := (hillL2Radicand_free_zero_iff _).mp hroot
    have hval : L i = freeHillValue k := Complex.ofReal_injective hk
    have hb := hs.central_mem i (by rcases hi with rfl | rfl <;> omega)
    have hdisc : (freeHillValue k : ℂ) ∈ hillCentralDisc 2 := by
      rw [← hval]
      exact (ofReal_mem_hillCentralDisc_iff 2 _).mpr ⟨hb.1.le,hb.2.le⟩
    have hklt := (freeHillValue_mem_hillCentralDisc_iff 2 (by omega) k).mp hdisc
    have hkne : k ≠ 0 := by
      intro hk0
      have hzero : L i = 0 := by simpa [hk0,freeHillValue] using hval
      rcases hi with rfl | rfl
      · exact h1 hzero
      · exact h2 hzero
    have hk1 : k = 1 := by omega
    rwa [hk1] at hval
  by_cases hj : j < 3
  · have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj' with rfl | rfl | rfl
    · simpa [freeHillValue] using h0
    · exact hsmall 1 (Or.inl rfl)
    · exact hsmall 2 (Or.inr rfl)
  · let n := (j+1)/2
    have hn : 2 ≤ n := by dsimp [n]; omega
    obtain ⟨p,hl,hr⟩ := hillRealLabels_high_pair 0 hq hreal n hn (by simp)
    have hp := p.localization 0 hq n (by omega) (by simp)
    have hpl : p.left = freeHillValue n := by
      have hh := hp.1
      simp only [norm_zero,mul_zero] at hh
      exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hh (abs_nonneg _)))
    have hpr : p.right = freeHillValue n := by
      have hh := hp.2
      simp only [norm_zero,mul_zero] at hh
      exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hh (abs_nonneg _)))
    have hslot : j = 2*n-1 ∨ j = 2*n := by dsimp [n]; omega
    change L j = freeHillValue n
    rcases hslot with hslot | hslot
    · exact (congrArg L hslot).trans (hl.trans hpl)
    · exact (congrArg L hslot).trans (hr.trans hpr)

/-- The exact periodic/antiperiodic free trace level at every canonical slot. -/
theorem hillRealLabels_zero_trace
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
    (j : ℕ) : hillL2Discriminant 0 (hillRealLabels 0 hq hreal j) = 2*(-1 : ℂ)^((j+1)/2) := by
  rw [hillRealLabels_zero, hillL2Discriminant_zero]
  let n := (j+1)/2
  change 2*Complex.cos (Complex.sqrt (freeHillValue n : ℂ)) = 2*(-1 : ℂ)^n
  have hs : Complex.sqrt (freeHillValue n : ℂ)^2 = ((n : ℂ)*(Real.pi : ℂ))^2 := by
    rw [ComplexAnalysis.complex_sqrt_sq]
    simp only [freeHillValue,Int.cast_natCast,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_natCast]
    ring
  have hcos : Complex.cos ((n : ℂ)*(Real.pi : ℂ)) = (-1 : ℂ)^n := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, ← Complex.ofReal_cos, Real.cos_nat_mul_pi,
      Complex.ofReal_pow]
    norm_num
  rcases eq_or_eq_neg_of_sq_eq_sq _ _ hs with h | h
  · rw [h,hcos]
  · rw [h,Complex.cos_neg,hcos]

end NLS.KdV
