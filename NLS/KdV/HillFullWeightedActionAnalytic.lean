import NLS.KdV.HillComplexWeightedActionSequence
import NLS.KdV.HillRealActionAnalytic

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
include h0q h0r

theorem exists_hillRealWeightedActionSequence_analytic_extension
    (w : SpectralWeight) (q : RealHillWeightedPotential w) :
    ∃ G : WeightedCoeff w.doubleIndex.toWeight 2 → Coeff 1, AnalyticAt ℂ G q.val ∧
      ∀ᶠ r : RealHillWeightedPotential w in 𝓝 q, G r.val=hillRealWeightedActionSequence w r := by
  let B := ‖q.val‖+1
  have hB : 0<B := by dsimp only [B];positivity
  obtain ⟨C,hC,htail⟩ := exists_hillNativeComplexWeightedActionTerm_uniform_tail_bound h0q h0r
  obtain ⟨Nb,hNb,hb⟩ := htail w B
  obtain ⟨Na,hNa,ha⟩ := exists_hillNativeComplexWeightedActionTerm_common_analytic h0q h0r w B
  obtain ⟨Nm,hNm,hm⟩ := exists_hillNativeComplexWeightedActionTerm_bounded_real_physical_matching h0q h0r w B
  let N := Nb+Na+Nm
  have hN : 1≤N := hNb.trans (by dsimp only [N];omega)
  have hNbN : Nb≤N := by dsimp only [N];omega
  have hNaN : Na≤N := by dsimp only [N];omega
  have hNmN : Nm≤N := by dsimp only [N];omega
  have hhead (n : ℕ) := exists_hillWeightedActionTerm_analytic_extension w q n
  choose F hFa hFm using hhead
  have hgood : ∀ᶠ p : WeightedCoeff w.doubleIndex.toWeight 2 in 𝓝 q.val,
      p∈ball 0 B ∧ ∀ n∈Finset.range N, AnalyticAt ℂ (F n) p ∧ ‖F n p‖≤‖F n q.val‖+1 := by
    have hc (n : ℕ) : ∀ᶠ p in 𝓝 q.val, AnalyticAt ℂ (F n) p ∧ ‖F n p‖≤‖F n q.val‖+1 := by
      have hnorm : ∀ᶠ p in 𝓝 q.val, ‖F n p‖<‖F n q.val‖+1 :=
        (hFa n).continuousAt.norm.eventually (gt_mem_nhds (by linarith))
      filter_upwards [(hFa n).eventually_analyticAt,hnorm] with p hp hn
      exact ⟨hp,hn.le⟩
    have hball : ball (0 : WeightedCoeff w.doubleIndex.toWeight 2) B∈𝓝 q.val :=
      isOpen_ball.mem_nhds (by rw [mem_ball,dist_zero_right];dsimp only [B];linarith)
    filter_upwards [hball,((Filter.eventually_all_finset _).mpr (fun n _ => hc n))] with p hp hhead
    exact ⟨hp,hhead⟩
  obtain ⟨U,hUsub,hU,hqU⟩ := _root_.mem_nhds_iff.mp hgood
  let f : WeightedCoeff w.doubleIndex.toWeight 2 → ℕ → ℂ :=
    fun p n => if n<N then F n p else hillNativeComplexWeightedActionTerm h0q h0r w n p
  let D := (∑ n∈Finset.range N, (‖F n q.val‖+1))+C*(9*B^2+2304*B^4)
  have hsum (p : WeightedCoeff w.doubleIndex.toWeight 2) (hp : p∈U) :
      Summable (fun n : ℕ => ‖f p n‖) ∧ (∑' n : ℕ, ‖f p n‖)≤D := by
    have hpB : ‖p‖≤B := (show ‖p‖<B by simpa only [mem_ball,dist_zero_right] using (hUsub hp).1).le
    obtain ⟨hs,ht⟩ := hb N hNbN p hpB
    have hshift (k : ℕ) : f p (k+N)=hillNativeComplexWeightedActionTerm h0q h0r w (k+N) p := by
      simp only [f,if_neg (show ¬k+N<N by omega)]
    have hs' : Summable (fun n : ℕ => ‖f p n‖) := by
      apply (summable_nat_add_iff N).mp
      simpa only [hshift] using hs
    refine ⟨hs',?_⟩
    rw [← hs'.sum_add_tsum_nat_add N]
    have hfinite : (∑ n∈Finset.range N, ‖f p n‖)≤∑ n∈Finset.range N, (‖F n q.val‖+1) := by
      apply Finset.sum_le_sum
      intro n hn
      have hlt : n<N := Finset.mem_range.mp hn
      simpa only [f,if_pos hlt] using ((hUsub hp).2 n hn).2
    simpa only [D,hshift] using add_le_add hfinite ht
  have hf (n : ℕ) : AnalyticOnNhd ℂ (fun p => f p n) U := by
    by_cases hn : n<N
    · intro p hp
      simpa only [f,if_pos hn] using ((hUsub hp).2 n (Finset.mem_range.mpr hn)).1
    · intro p hp
      simpa only [f,if_neg hn] using ha n (hNaN.trans (by omega)) p (hUsub hp).1
  let G : WeightedCoeff w.doubleIndex.toWeight 2 → Coeff 1 := fun p => Coeff.natL1OfFunction (f p)
  have hG : AnalyticOnNhd ℂ G U := Coeff.analyticOnNhd_natL1OfFunction_of_summable_bound f U hU hf D hsum
  have hheadmatch : ∀ᶠ r : RealHillWeightedPotential w in 𝓝 q,
      ∀ n∈Finset.range N, F n r.val=(hillWeightedActionTerm w r n:ℂ) :=
    (Filter.eventually_all_finset _).mpr (fun n _ => hFm n)
  have hrealU : ∀ᶠ r : RealHillWeightedPotential w in 𝓝 q, r.val∈U :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds (hU.mem_nhds hqU)
  refine ⟨G,hG q.val hqU,?_⟩
  filter_upwards [hheadmatch,hrealU] with r hrhead hrU
  have hrB : ‖r.val‖≤B := (show ‖r.val‖<B by simpa only [mem_ball,dist_zero_right] using (hUsub hrU).1).le
  have hmatch (n : ℕ) : f r.val n=(hillWeightedActionTerm w r n:ℂ) := by
    by_cases hn : n<N
    · simpa only [f,if_pos hn] using hrhead n (Finset.mem_range.mpr hn)
    · simpa only [f,if_neg hn] using hm r hrB n (hNmN.trans (by omega))
  apply lp.ext
  funext j
  have hleft := Coeff.natL1OfFunction_apply_of_summable (f r.val) (hsum r.val hrU).1 (Equiv.intEquivNat j)
  have hright := hillRealWeightedActionSequence_apply w r (Equiv.intEquivNat j)
  simp only [Equiv.symm_apply_apply] at hleft hright
  exact hleft.trans ((hmatch _).trans hright.symm)

theorem continuous_hillRealWeightedActionSequence (w : SpectralWeight) :
    Continuous (hillRealWeightedActionSequence w) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  obtain ⟨G,hG,hmatch⟩ := exists_hillRealWeightedActionSequence_analytic_extension h0q h0r w q
  have hc : ContinuousAt (fun r : RealHillWeightedPotential w => G r.val) q :=
    hG.continuousAt.comp continuous_subtype_val.continuousAt
  exact hc.congr_of_eventuallyEq (Filter.EventuallyEq.symm hmatch)

omit h0q h0r in
theorem tsum_hillRealWeightedActionSequence (w : SpectralWeight) (q : RealHillWeightedPotential w) :
    (∑' j : ℤ, hillRealWeightedActionSequence w q j)=(∑' n : ℕ, hillWeightedActionTerm w q n:ℝ) := by
  have he (j : ℤ) : hillRealWeightedActionSequence w q j=(hillWeightedActionTerm w q (Equiv.intEquivNat j):ℂ) := by
    have hh := hillRealWeightedActionSequence_apply w q (Equiv.intEquivNat j)
    simpa only [Equiv.symm_apply_apply] using hh
  calc
    _ = ∑' j : ℤ, (hillWeightedActionTerm w q (Equiv.intEquivNat j):ℂ) := tsum_congr he
    _ = ∑' n : ℕ, (hillWeightedActionTerm w q n:ℂ) := Equiv.intEquivNat.tsum_eq (fun n : ℕ => (hillWeightedActionTerm w q n:ℂ))
    _ = _ := (Complex.ofReal_tsum _).symm

theorem exists_hillWeightedActionMass_analytic_extension (w : SpectralWeight) (q : RealHillWeightedPotential w) :
    ∃ F : WeightedCoeff w.doubleIndex.toWeight 2 → ℂ, AnalyticAt ℂ F q.val ∧
      ∀ᶠ r : RealHillWeightedPotential w in 𝓝 q, F r.val=(∑' n : ℕ, hillWeightedActionTerm w r n:ℝ) := by
  let : Fact (1≤(1:ℝ≥0∞)) := ⟨le_rfl⟩
  obtain ⟨G,hG,hmatch⟩ := exists_hillRealWeightedActionSequence_analytic_extension h0q h0r w q
  let F := fun p => (lp.tsumCLM ℂ ℤ ℂ) (G p)
  refine ⟨F,((lp.tsumCLM ℂ ℤ ℂ).analyticAt (G q.val)).comp hG,?_⟩
  filter_upwards [hmatch] with r hr
  dsimp only [F]
  rw [hr]
  exact tsum_hillRealWeightedActionSequence w r

end NLS.KdV
