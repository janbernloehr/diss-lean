import NLS.KdV.HillComplexWeightedActionTails
import NLS.SequenceSpaces.NatL1AnalyticRealization

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

def hillNativeComplexWeightedActionTail (w : SpectralWeight) (N : ℕ)
    (q : WeightedCoeff w.doubleIndex.toWeight 2) : Coeff 1 :=
  Coeff.natL1OfFunction (fun k => hillNativeComplexWeightedActionTerm h0q h0r w (k+N) q)

theorem exists_hillNativeComplexWeightedActionTail_analytic_bound :
    ∃ C : ℝ, 0<C ∧ ∀ w : SpectralWeight, ∀ B : ℝ, ∃ N0 : ℕ, 1≤N0 ∧ ∀ N : ℕ, N0≤N →
      AnalyticOnNhd ℂ (hillNativeComplexWeightedActionTail h0q h0r w N)
        (ball (0 : WeightedCoeff w.doubleIndex.toWeight 2) B) ∧
      ∀ q∈ball (0 : WeightedCoeff w.doubleIndex.toWeight 2) B,
        ‖hillNativeComplexWeightedActionTail h0q h0r w N q‖≤C*(9*B^2+2304*B^4) ∧
        ∀ k : ℕ, hillNativeComplexWeightedActionTail h0q h0r w N q (Equiv.intEquivNat.symm k)=
          hillNativeComplexWeightedActionTerm h0q h0r w (k+N) q := by
  obtain ⟨C,hC,hbound⟩ := exists_hillNativeComplexWeightedActionTerm_uniform_tail_bound h0q h0r
  refine ⟨C,hC,?_⟩
  intro w B
  obtain ⟨Nb,hNb,hb⟩ := hbound w B
  obtain ⟨Na,hNa,ha⟩ := exists_hillNativeComplexWeightedActionTerm_common_analytic h0q h0r w B
  refine ⟨Nb+Na,hNb.trans (by omega),?_⟩
  intro N hN
  have hp (q : WeightedCoeff w.doubleIndex.toWeight 2)
      (hq : q∈ball (0 : WeightedCoeff w.doubleIndex.toWeight 2) B) : ‖q‖≤B :=
    (show ‖q‖<B by simpa only [mem_ball,dist_zero_right] using hq).le
  refine ⟨?_,?_⟩
  · exact Coeff.analyticOnNhd_natL1OfFunction_of_summable_bound
      (fun q k => hillNativeComplexWeightedActionTerm h0q h0r w (k+N) q) _ isOpen_ball
      (fun k => ha (k+N) (by omega)) (C*(9*B^2+2304*B^4))
      (fun q hq => hb N (by omega) q (hp q hq))
  · intro q hq
    obtain ⟨hs,hm⟩ := hb N (by omega) q (hp q hq)
    exact ⟨(Coeff.norm_natL1OfFunction_eq_tsum _ hs).le.trans hm,
      Coeff.natL1OfFunction_apply_of_summable _ hs⟩

def hillRealWeightedActionSequence (w : SpectralWeight) (q : RealHillWeightedPotential w) : Coeff 1 :=
  Coeff.natL1OfFunction (fun n => (hillWeightedActionTerm w q n:ℂ))

theorem summable_norm_hillWeightedActionTerm (w : SpectralWeight) (q : RealHillWeightedPotential w) :
    Summable (fun n : ℕ => ‖(hillWeightedActionTerm w q n:ℂ)‖) := by
  have he (n : ℕ) : ‖(hillWeightedActionTerm w q n:ℂ)‖=hillWeightedActionTerm w q n := by
    rw [norm_real,Real.norm_eq_abs,abs_of_nonneg (hillWeightedActionTerm_nonneg w q n)]
  simpa only [he] using summable_hillWeightedActionTerm w q

theorem hillRealWeightedActionSequence_apply (w : SpectralWeight) (q : RealHillWeightedPotential w) (n : ℕ) :
    hillRealWeightedActionSequence w q (Equiv.intEquivNat.symm n)=(hillWeightedActionTerm w q n:ℂ) :=
  Coeff.natL1OfFunction_apply_of_summable _ (summable_norm_hillWeightedActionTerm w q) n

theorem norm_hillRealWeightedActionSequence (w : SpectralWeight) (q : RealHillWeightedPotential w) :
    ‖hillRealWeightedActionSequence w q‖=∑' n : ℕ, hillWeightedActionTerm w q n := by
  rw [hillRealWeightedActionSequence,Coeff.norm_natL1OfFunction_eq_tsum _ (summable_norm_hillWeightedActionTerm w q)]
  apply tsum_congr
  intro n
  rw [norm_real,Real.norm_eq_abs,abs_of_nonneg (hillWeightedActionTerm_nonneg w q n)]

end NLS.KdV
