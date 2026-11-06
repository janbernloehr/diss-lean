import NLS.KdV.HillFullLowPeriodMap
import NLS.KdV.HillFreeFullPeriodMatching
import NLS.KdV.HillFullComplexPeriodError

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- The full mixed period map uses the actual full product in each finite
physical contour and the genuine free and complex error Hilbert tails. -/
def hillFullMixedComplexPeriodSequence (N : ℕ) (t : Coeff 2 × Coeff 2) : Coeff 2 :=
  hillFullLowComplexPeriodSequence q hq hr N t+
    Coeff.fourierTail N (hillFreeFullPeriodSequence t.1)+
      hillFullComplexPeriodErrorSequence h0q h0r N t

theorem analyticOnNhd_hillFullMixedComplexPeriodSequence
    (N : ℕ) (hN : 1 ≤ N) (B D : ℝ) (hB : 0 < B) (hD : 0 ≤ D)
    (hc : HillComplexTailPeriodControl h0q h0r N B D) (U : Set (Coeff 2))
    (hperiods : ∀ k : ℕ, 1 ≤ k → k < N →
      AnalyticOnNhd ℂ (hillAbelianProductComplexPeriod q hq hr 0 k) (univ ×ˢ U)) :
    AnalyticOnNhd ℂ (hillFullMixedComplexPeriodSequence q hq hr h0q h0r N) (univ ×ˢ (U ∩ ball 0 B)) := by
  have hlo := analyticOnNhd_hillFullLowComplexPeriodSequence q hq hr N U hperiods
  have hhi := analyticOnNhd_hillFullComplexPeriodErrorSequence h0q h0r N hN B D hB hD hc
  intro t ht
  have hf := (analyticOnNhd_hillFreeFullPeriodSequence t.1 (mem_univ _)).comp
    (f := fun v : Coeff 2 × Coeff 2 => v.1) analyticAt_fst
  have htail : AnalyticAt ℂ (fun v : Coeff 2 × Coeff 2 =>
      Coeff.fourierTail N (hillFreeFullPeriodSequence v.1)) t := by
    exact hf.sub (((Coeff.truncateCLM (p := 2) (Coeff.lowFrequencies N)).analyticAt _).comp hf)
  exact ((hlo t ⟨mem_univ _,ht.2.1⟩).add htail).add (hhi t ⟨mem_univ _,ht.2.2⟩)

theorem exists_hillFullMixedComplexPeriodSequence_analytic_neighborhood :
    ∃ N : ℕ, ∃ B D : ℝ, ∃ U : Set (Coeff 2),
      1 ≤ N ∧ 0 < B ∧ 0 < D ∧ HillComplexTailPeriodControl h0q h0r N B D ∧
        IsOpen U ∧ SpectralWeight.one.toCoeff q ∈ U ∧ U ⊆ ball 0 B ∧
          AnalyticOnNhd ℂ (hillFullMixedComplexPeriodSequence q hq hr h0q h0r N) (univ ×ˢ U) := by
  let B : ℝ := ‖SpectralWeight.one.toCoeff q‖+1
  have hB : 0 < B := by dsimp only [B];positivity
  obtain ⟨N,hN,D,hD,hcontrol⟩ := exists_hillComplexTailPeriodControl h0q h0r B
  obtain ⟨V,hV,hqV,hperiods⟩ := exists_hillAbelianProductComplexPeriods_common_finite_neighborhood q hq hr N
  refine ⟨N,B,D,V ∩ ball 0 B,hN,hB,hD,hcontrol,hV.inter isOpen_ball,?_,inter_subset_right,?_⟩
  · refine ⟨hqV,?_⟩
    rw [mem_ball,dist_zero_right]
    dsimp only [B]
    linarith
  · exact analyticOnNhd_hillFullMixedComplexPeriodSequence q hq hr h0q h0r N hN B D hB hD.le hcontrol V (hperiods 0)

theorem hillFullMixedComplexPeriodSequence_apply_nat
    (N k : ℕ) (hN : 1 ≤ N) (hk : 1 ≤ k) (B D : ℝ) (hD : 0 ≤ D)
    (hc : HillComplexTailPeriodControl h0q h0r N B D) (a p : Coeff 2) (hp : ‖p‖ ≤ B) :
    hillFullMixedComplexPeriodSequence q hq hr h0q h0r N (a,p) (k : ℤ) =
      (-2*(Real.pi : ℂ))*(if k < N then hillAbelianProductComplexPeriod q hq hr 0 k (a,p)
        else hillAbelianProductComplexPeriod 0 h0q h0r 0 k (a,p)) := by
  rw [hillFullMixedComplexPeriodSequence,lp.coeFn_add,Pi.add_apply,lp.coeFn_add,Pi.add_apply,
    hillFullLowComplexPeriodSequence_apply_nat q hq hr N k hk,Coeff.fourierTail_apply,
    hillFullComplexPeriodErrorSequence_apply h0q h0r N hN B D hD hc a p hp]
  simp only [Int.natAbs_natCast,hillFullComplexPeriodErrorCoordinate,Int.toNat_natCast]
  have hkz : (0 : ℤ) < (k : ℤ) := by omega
  by_cases hkN : k < N
  · simp only [if_pos hkN,if_neg (by omega : ¬ N ≤ k),if_neg (by omega : ¬((0 : ℤ)<k ∧ N≤k)),add_zero]
  · simp only [if_neg hkN]
    rw [if_pos (by omega : N ≤ k),if_pos ⟨hkz,by omega⟩,
      hillFreeFullPeriodSequence_eq_original_full_period h0q h0r k hk a,hillFullComplexPeriodError]
    ring

theorem hillFullMixedComplexPeriodSequence_apply_nonpositive
    (N : ℕ) (hN : 1 ≤ N) (B D : ℝ) (hD : 0 ≤ D)
    (hc : HillComplexTailPeriodControl h0q h0r N B D) (a p : Coeff 2) (hp : ‖p‖ ≤ B)
    (m : ℤ) (hm : m ≤ 0) :
    hillFullMixedComplexPeriodSequence q hq hr h0q h0r N (a,p) m = 0 := by
  rw [hillFullMixedComplexPeriodSequence,lp.coeFn_add,Pi.add_apply,lp.coeFn_add,Pi.add_apply,
    hillFullLowComplexPeriodSequence_apply_nonpositive q hq hr N (a,p) m hm,
    Coeff.fourierTail_apply,hillFreeFullPeriodSequence_apply,
    hillFullComplexPeriodErrorSequence_apply h0q h0r N hN B D hD hc a p hp]
  simp only [hillFreeFullPeriodCoordinate,hillFullComplexPeriodErrorCoordinate,
    if_neg (by omega : ¬(0<m ∧ m≠0)),if_neg (by omega : ¬(0<m ∧ N≤m.toNat)),ite_self,add_zero]

end NLS.KdV
