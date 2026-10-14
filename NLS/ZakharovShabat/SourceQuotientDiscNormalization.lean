import NLS.ZakharovShabat.SourceLemma10_8Estimates
import NLS.ZakharovShabat.SourceSingleRootQuotientNormalization

/-!
# Actual free and colliding-numerator checks for the disk supremum

The free quotient gives zero error on every actual disk. Moving the
zeroth numerator root onto the negative free center gives error one
on a central selected disk, even though two numerator roots coincide.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem SourceQuotientDiscEstimates.free_sup_zero
    {hp : p ≠ ⊤} {hp1 : 1 < p} {U : Set (Coeff p × CoeffPair p)}
    {D : ℤ → Set ℂ} {c R H M : ℝ} {N K : ℕ}
    (h : SourceQuotientDiscEstimates hp hp1 U D c R H M N K)
    (h0 : (0,0) ∈ U) (n : ℤ) : sourceQuotientDiscSup hp hp1 D (0,0) n = 0 := by
  apply le_antisymm _ (h.sup_nonneg (0,0) h0 n)
  apply h.sup_le (0,0) n 0
  intro z hz
  rw [sourceSingleRootQuotient_zero_free hp hp1 n z (h.domain (0,0) h0 n z hz)]
  simp

/-- A nonzero actual supremum in the finite head, with colliding numerator roots. -/
theorem exists_sourceQuotientDiscSup_collision (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ a : Coeff p, displacedRoots a 0 = -(Real.pi:ℂ) ∧ displacedRoots a (-1) = -(Real.pi:ℂ) ∧
      ∃ U : Set (Coeff p × CoeffPair p), IsOpen U ∧ (a,0) ∈ U ∧
        ∃ D : ℤ → Set ℂ, ∃ c R H M : ℝ, ∃ N K : ℕ,
          SourceQuotientDiscEstimates hp hp1 U D c R H M N K ∧ 1 ≤ K ∧
          -(Real.pi:ℂ) ∈ D (-1) ∧ 1 ≤ sourceQuotientDiscSup hp hp1 D (a,0) (-1) := by
  let a : Coeff p := Coeff.ofFinsupp (Finsupp.single 0 (-(Real.pi:ℂ)))
  have ha0 : displacedRoots a 0 = -(Real.pi:ℂ) := by simp [a,displacedRoots,Coeff.ofFinsupp_apply]
  have han : displacedRoots a (-1) = -(Real.pi:ℂ) := by simp [a,displacedRoots,Coeff.ofFinsupp_apply]
  obtain ⟨W,_,_,hr,h⟩ := sourceLemma10_8_estimates hp hp1
  have h0 : (0 : CoeffPair p) ∈ W := hr (by simp [realTypeSourceLocus])
  obtain ⟨V,_,_,h0V,_,D,c,hD,ha⟩ := h.neighborhoods 0 h0
  obtain ⟨U,ho,hbase,_,R,H,M,N,K,hE⟩ := ha a
  have hcenter : -(Real.pi:ℂ) ∈ D (-1) := by
    apply hD.gap 0 h0V (-1)
    simp [sourcePeriodicSegment,map_zero,canonicalPeriodicLeft_zero,canonicalPeriodicRight_zero,segment_same]
  have hQ : sourceSingleRootQuotientJointProduct hp hp1 (-1) (-(Real.pi:ℂ),(a,0)) = 0 := by
    rw [← ha0]
    exact sourceSingleRootQuotient_other_root_zero hp hp1 0 (-1) 0 (by decide) a
  refine ⟨a,ha0,han,U,ho,hbase,D,c,R,H,M,N,K,hE,
    by have := hE.threshold; omega,hcenter,?_⟩
  simpa only [hQ,zero_sub,norm_neg,norm_one] using hE.norm_le_sup (a,0) hbase (-1) _ hcenter

end NLS.ZakharovShabat
