import NLS.KdV.HillHminusOneCanonicalRealLabels
import NLS.KdV.HillCanonicalFreeLabels

/-! # Exact free normalization of the intrinsic H^-1 labels

The existing free L2 enumeration describes the same entire free
characteristic. Exact high multiplicities identify both free endpoints;
intrinsic uniqueness then fixes every central and high slot.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped Classical
namespace NLS.KdV

theorem hillHminusRadicand_zero_eq_hillL2 : hillHminusRadicand 0 = hillL2Radicand 0 := by
  funext z
  simpa only [map_zero] using hillHminusRadicand_eq_hillL2 (0 : Coeff 2) z

theorem HillHminusRealHighPair.zero_endpoints {n : ℕ+} {r : ℝ}
    (p : HillHminusRealHighPair 0 n r) (hr : 0 < r) :
    p.left = freeHillValue (n : ℕ) ∧ p.right = freeHillValue (n : ℕ) := by
  have hcenter : ((Real.pi : ℂ)*(n : ℕ))^2 = (freeHillValue (n : ℕ) : ℂ) := by
    dsimp only [freeHillValue]; push_cast; ring
  have hz : (freeHillValue (n : ℕ) : ℂ) ∈ hillHminusGapSquareDisc n r := by
    change (freeHillValue (n : ℕ) : ℂ) ∈ closedBall (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r)
    rw [hcenter]
    exact mem_closedBall_self (by positivity)
  have ho : analyticOrderNatAt (hillHminusRadicand 0) (freeHillValue (n : ℕ) : ℂ) = 2 := by
    rw [hillHminusRadicand_zero_eq_hillL2]
    exact hillL2Radicand_free_order (n : ℕ) n.property
  have hc := (p.pair.multiplicity (freeHillValue (n : ℕ)) hz).symm.trans ho
  by_cases hl : p.left = freeHillValue (n : ℕ) <;>
    by_cases hu : p.right = freeHillValue (n : ℕ) <;>
    simp [ofReal_inj,eq_comm,hl,hu] at hc ⊢

theorem hillHminusRealLabels_zero (hq : IsRealPeriodOneHminusOne 0) (j : ℕ) :
    hillHminusRealLabels 0 hq j = freeHillValue ((j+1)/2 : ℕ) := by
  obtain ⟨N,r,h⟩ := hillHminusRealLabels_spec 0 hq
  have hp0 : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈
      Coeff.paritySubspace 0 := by simp
  have hr0 : IsRealHillPotential
      (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)) := by
    intro k
    simp
  let L := hillRealLabels 0 hp0 hr0
  have g := hillRealLabels_spec_at 0 hp0 hr0 N h.cutoff_ge_two (by simp)
  have ht : HillHminusRealCharacteristicLabeling 0 N r L := by
    refine ⟨h.central_control,h.radius_pos,h.radius_le,g.monotone,?_,?_,?_,g.central_mem⟩
    · intro z
      rw [hillHminusRadicand_zero_eq_hillL2]
      simpa only [map_zero] using g.roots z
    · intro n hn
      obtain ⟨p,_,_⟩ := h.high_pair n hn
      have hp := p.zero_endpoints h.radius_pos
      refine ⟨p,?_,?_⟩
      · change hillRealLabels 0 hp0 hr0 (2*(n : ℕ)-1) = p.left
        rw [hillRealLabels_zero]
        have hi : (2*(n : ℕ)-1+1)/2 = (n : ℕ) := by have hnn := hn; have hN := h.cutoff_ge_two; omega
        rw [hi,hp.1]
      · change hillRealLabels 0 hp0 hr0 (2*(n : ℕ)) = p.right
        rw [hillRealLabels_zero]
        have hi : (2*(n : ℕ)+1)/2 = (n : ℕ) := by omega
        rw [hi,hp.2]
    · intro x
      rw [hillHminusRadicand_zero_eq_hillL2]
      simpa only [map_zero] using g.central_counts x
  have he := congrFun (ht.eq_canonical hq) j
  exact he.symm.trans (hillRealLabels_zero hp0 hr0 j)

theorem hillHminusRealLabels_zero_trace (hq : IsRealPeriodOneHminusOne 0) (j : ℕ) :
    hillHminusDiscriminant 0 (hillHminusRealLabels 0 hq j) = 2*(-1 : ℂ)^((j+1)/2) := by
  rw [hillHminusRealLabels_zero,hillHminusDiscriminant_zero]
  let n := (j+1)/2
  change 2*cos (sqrt (freeHillValue n : ℂ)) = 2*(-1 : ℂ)^n
  have hs : sqrt (freeHillValue n : ℂ)^2 = ((n : ℂ)*(Real.pi : ℂ))^2 := by
    rw [NLS.ComplexAnalysis.complex_sqrt_sq]
    simp only [freeHillValue,Int.cast_natCast,ofReal_mul,ofReal_pow,ofReal_natCast]
    ring
  have hcos : cos ((n : ℂ)*(Real.pi : ℂ)) = (-1 : ℂ)^n := by
    rw [← ofReal_natCast,← ofReal_mul,← ofReal_cos,Real.cos_nat_mul_pi,ofReal_pow]
    norm_num
  rcases eq_or_eq_neg_of_sq_eq_sq _ _ hs with h | h
  · rw [h,hcos]
  · rw [h,cos_neg,hcos]

end NLS.KdV
