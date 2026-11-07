import NLS.Articles.KdVPseudomeasures.OriginalHillNativeCompactFibers
import NLS.Articles.KdVPseudomeasures.OriginalCanonicalGapSquares
import NLS.Articles.KdVPseudomeasures.OriginalMiuraGapComparison
import NLS.KdV.HillNativeFiniteGap
import NLS.ZakharovShabat.SourceFiniteGapSobolev

/-! ACTUAL native Hill finite-gap data imply ACTUAL original Dirac finite-gap
data for every genuine real Miura lift. The verified real Dirac bootstrap
therefore supplies all Sobolev orders for that SAME scalar lift. -/
noncomputable section
open Set Complex NLS.KdV NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures

/-- Eventual vanishing of the actual original positive gaps is equivalent
to actual native finite-gap membership; signed tails use the original even extension. -/
theorem hillRealFiniteGap_original_gap_tail (q : HillRealMeanZeroSource)
    (hf : q ∈ hillRealFiniteGapLocus) :
    ∃ N : ℕ, ∀ k : ℤ, N ≤ k.natAbs →
      originalCanonicalGapValues (originalHillPotentialOfRealSource q) k=0 := by
  obtain ⟨N,hN⟩ := hf
  refine ⟨max N 1,fun k hk => ?_⟩
  let n : ℕ+ := ⟨k.natAbs,by omega⟩
  have hs := originalCanonicalGapSquare_eq (originalHillPotentialOfRealSource q) n
  rw [originalHillPotentialOfRealSource_coefficients] at hs
  have hg : originalCanonicalGapValues (originalHillPotentialOfRealSource q) (n:ℤ)=0 := by
    exact (pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0)).mp (hs.symm.trans (hN n (by change N ≤ k.natAbs; exact (le_max_left _ _).trans hk)))
  by_cases hkp : 0 ≤ k
  · have he : (n:ℤ)=k := by dsimp [n]; omega
    exact he ▸ hg
  · have he : -(n:ℤ)=k := by
      have h : (n:ℤ)= -k := by dsimp [n]; omega
      omega
    rw [← he,originalCanonicalGapValues_neg]
    exact hg

/-- Every actual real scalar Miura lift of an actual Hill finite-gap source
has only finitely many ACTUAL signed Dirac gaps open, including the central block. -/
theorem hillMiuraRealSource_finiteGap_of_hillRealFiniteGap
    (q : HillRealMeanZeroSource) (hf : q ∈ hillRealFiniteGapLocus)
    (u : PeriodOneRealL2) (c : ℝ)
    (hu : periodOneMiura u.val=hillRealMeanZeroInclusion q+
      periodOneL2Inclusion (lp.single 2 0 (c:ℂ))) :
    hillMiuraRealSource u ∈ sourceFiniteGapLocus (by simp) (by norm_num) := by
  obtain ⟨N,hN⟩ := hillRealFiniteGap_original_gap_tail q hf
  have himage : periodOneMiura u.val=originalPeriodOneCoefficients (originalHillPotentialOfRealSource q)+
      periodOneL2Inclusion (lp.single 2 0 (c:ℂ)) := by
    rw [originalHillPotentialOfRealSource_coefficients]
    exact hu
  obtain ⟨M,hM,hgap⟩ := exists_originalCanonicalGapValues_miura_signed_norm
    (originalHillPotentialOfRealSource q) u c himage
  change {k : ℤ | canonicalPeriodicGap (by simp) (by norm_num)
    (periodOnePotential (hillMiuraRealSource u).val) (periodOnePotential_mem _) k ≠ 0}.Finite
  apply (Set.finite_Icc (-(max N M:ℕ):ℤ) (max N M)).subset
  intro k hk
  by_contra hnot
  have hlarge : max N M ≤ k.natAbs := by
    simp only [mem_Icc,not_and_or,not_le] at hnot
    rcases hnot with h | h <;> omega
  have hh := (hgap k ((le_max_right _ _).trans hlarge)).1
  rw [hN k ((le_max_left _ _).trans hlarge)] at hh
  have hpos : 0 < ‖hillMiuraDiracRight u.val k+hillMiuraDiracLeft u.val k‖ :=
    (mul_pos Real.pi_pos (by have := hM.trans ((le_max_right _ _).trans hlarge); positivity)).trans_le
      (hgap k ((le_max_right _ _).trans hlarge)).2
  simp only [norm_zero] at hh
  have hz : hillMiuraDiracRight u.val k-hillMiuraDiracLeft u.val k=0 :=
    norm_eq_zero.mp ((mul_eq_zero.mp hh.symm).resolve_right (ne_of_gt hpos))
  exact hk hz

/-- The SAME actual scalar lift has every nonnegative Sobolev order. -/
theorem hillRealFiniteGap_miura_mem_all_sobolev
    (q : HillRealMeanZeroSource) (hf : q ∈ hillRealFiniteGapLocus)
    (u : PeriodOneRealL2) (c : ℝ)
    (hu : periodOneMiura u.val=hillRealMeanZeroInclusion q+
      periodOneL2Inclusion (lp.single 2 0 (c:ℂ))) (s : ℝ) (hs : 0 ≤ s) :
    Memℓp (fun k => (Weight.sobolev s k:ℂ)*u.val k) 2 := by
  have h := (sourceFiniteGap_mem_all_sobolev (by simp) (by norm_num) (hillMiuraRealSource u)
    (hillMiuraRealSource_finiteGap_of_hillRealFiniteGap q hf u c hu) s hs).1
  simpa only [hillMiuraRealSource,hillMiuraDiagonal_fst] using h

end NLS.Articles.KdVPseudomeasures
