import NLS.KdV.HillUniformOffDiagonalPhases
import NLS.KdV.HillUniformOwnRegularPhase
import NLS.KdV.HillFiniteGapUniformRegularCorrections
import NLS.KdV.HillSummedRegularCorrection
import NLS.SequenceSpaces.FiniteHeadOwnTail

noncomputable section
set_option autoImplicit false
open Set Metric Filter Topology
open Complex NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

include h0q h0r in
/-- Exact decomposition of the original absolutely convergent regular
phase into low gaps, the own gap and high off-diagonal gaps. -/
theorem hillSummedRegularAbelianCorrection_eq_low_own_high
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (N : ℕ) (hN : 1≤N) (n : ℕ) (hn : N≤n) :
    hillSummedRegularAbelianCorrection q hq hr n (hN.trans hn)=
      (∑ k∈(Finset.range N).filter (fun k => 1≤k), if hk : 1≤k then
        hillRegularAbelianCorrection q hq hr n (hN.trans hn) k hk else 0)+
      hillRegularAbelianCorrection q hq hr n (hN.trans hn) n (hN.trans hn)+
      hillHighOffDiagonalRegularCorrection q hq hr N hN n (hN.trans hn) := by
  let f : ℕ → ℂ := fun k => if hk : 1≤k then
    hillRegularAbelianCorrection q hq hr n (hN.trans hn) k hk else 0
  have hshift : Summable (fun j : ℕ => f (j+1)) := by
    convert summable_hillRegularAbelianCorrection h0q h0r q hq hr n (hN.trans hn) using 1
    ext j
    exact dif_pos (by omega : 1≤j+1)
  have hf : Summable f := (summable_nat_add_iff 1).mp hshift
  have htsum : (∑' k, f k)=hillSummedRegularAbelianCorrection q hq hr n (hN.trans hn) := by
    have hfirst : f 0=0 := dif_neg (by omega : ¬1≤(0:ℕ))
    have heq : (∑' j : ℕ, f (j+1))=hillSummedRegularAbelianCorrection q hq hr n (hN.trans hn) :=
      tsum_congr (fun j => dif_pos (by omega : 1≤j+1))
    have hh := Summable.sum_add_tsum_nat_add 1 hf
    rw [Finset.sum_range_one,hfirst,zero_add,heq] at hh
    exact hh.symm
  have hlow : (∑ k∈Finset.range N, f k)=∑ k∈(Finset.range N).filter (fun k => 1≤k), f k := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : 1≤k
    · rw [if_pos hk]
    · rw [if_neg hk]
      exact dif_neg hk
  have hhigh : (∑' k : ℕ, if N≤k ∧ k≠n then f k else 0)=
      hillHighOffDiagonalRegularCorrection q hq hr N hN n (hN.trans hn) := by
    unfold hillHighOffDiagonalRegularCorrection
    apply tsum_congr
    intro k
    by_cases hk : N≤k ∧ k≠n
    · rw [if_pos hk,dif_pos hk]
      exact dif_pos (hN.trans hk.1)
    · rw [if_neg hk,dif_neg hk]
  rw [←htsum]
  have hh := NLS.sum_head_add_own_add_tsum_tail f hf N n hn
  rw [hlow,hhigh] at hh
  simpa only [f,dif_pos (hN.trans hn)] using hh.symm

include h0q h0r in
/-- The full original summed regular phase has one bounded analytic
native source chart before every sufficiently large differential index
and every spectral weight. -/
theorem exists_hillSummedRegularAbelianCorrection_uniform_native_analytic :
    ∃ δ M : ℝ, ∃ N : ℕ, 0<δ ∧ 0<M ∧ ∃ hN : 1≤N,
      ∀ n : ℕ, ∀ hn : N≤n, ∀ w : SpectralWeight,
      ∃ F : WeightedCoeff w.doubleIndex.toWeight 2 → ℂ,
        AnalyticOnNhd ℂ F (ball 0 δ) ∧
        (∀ q∈ball 0 δ, ‖F q‖≤M) ∧
        (∀ q : RealHillWeightedPotential w, ‖q.val‖<δ →
          F q.val=hillSummedRegularAbelianCorrection (hillPeriodOneUnitPotential w q.val)
            (hillPeriodOneUnitPotential_even w q.val) (hillPeriodOneUnitPotential_real w q.val q.property)
            n (hN.trans hn)) ∧
        AnalyticOnNhd ℂ (fun q => Complex.exp (I*F q)) (ball 0 δ) ∧
        (∀ q∈ball 0 δ, ‖Complex.exp (I*F q)‖≤Real.exp M) ∧
        AnalyticOnNhd ℂ (fun q => Complex.exp (-I*F q)) (ball 0 δ) ∧
        ∀ q∈ball 0 δ, ‖Complex.exp (-I*F q)‖≤Real.exp M := by
  obtain ⟨δh,Mh,Nh,hδh,hMh,hNh,hhigh⟩ := exists_hillHighOffDiagonalRegularCorrection_uniform_native_analytic h0q h0r
  obtain ⟨δo,Mo,No,hδo,hMo,hNo,hown⟩ := exists_hillOwnRegularAbelianCorrection_uniform_native_charts h0q h0r
  let S := (Finset.range Nh).filter (fun k => 1≤k)
  obtain ⟨δl,Cl,hδl,hCl,hlow⟩ := exists_hillFinite_regularAbelianCorrection_uniform_charts h0q h0r S
    (fun k hk => (Finset.mem_filter.mp hk).2)
  let δ := min δh (min δo δl)
  let M := Cl+Mo+4*Mh/Real.pi^2
  let N := max Nh No
  have hδ : 0<δ := lt_min hδh (lt_min hδo hδl)
  have hM : 0<M := by dsimp only [M];positivity
  have hN : 1≤N := hNh.trans (le_max_left _ _)
  have hdh : δ≤δh := min_le_left _ _
  have hdo : δ≤δo := (min_le_right _ _).trans (min_le_left _ _)
  have hdl : δ≤δl := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ,M,N,hδ,hM,hN,?_⟩
  intro n hn w
  have hn1 : 1≤n := hN.trans hn
  have hnH : Nh≤n := (le_max_left _ _).trans hn
  have hnO : No≤n := (le_max_right _ _).trans hn
  obtain ⟨H,hHa,hHb,hHr,_,_⟩ := hhigh n hn1 w
  obtain ⟨O,hOa,hOb,hOr⟩ := hown n hnO
  obtain ⟨L,hLa,hLb,hLr⟩ := hlow n hn1
  let F : WeightedCoeff w.doubleIndex.toWeight 2 → ℂ := fun q =>
    L (hillPeriodOneCoefficientMap w q)+O (hillPeriodOneCoefficientMap w q)+H q
  have hmap (q : WeightedCoeff w.doubleIndex.toWeight 2) (hq : q∈ball 0 δ) :
      hillPeriodOneCoefficientMap w q∈ball 0 δ := by
    rw [mem_ball,dist_zero_right]
    exact (norm_hillPeriodOneCoefficientMap_le w q).trans_lt
      (show ‖q‖<δ by simpa only [mem_ball,dist_zero_right] using hq)
  have hFa : AnalyticOnNhd ℂ F (ball 0 δ) := by
    intro q hq
    have hLa' := (hLa _ (ball_subset_ball hdl (hmap q hq))).comp ((hillPeriodOneCoefficientMap w).analyticAt q)
    have hOa' := (hOa _ (ball_subset_ball hdo (hmap q hq))).comp ((hillPeriodOneCoefficientMap w).analyticAt q)
    exact (hLa'.add hOa').add (hHa q (ball_subset_ball hdh hq))
  have hFb (q : WeightedCoeff w.doubleIndex.toWeight 2) (hq : q∈ball 0 δ) : ‖F q‖≤M := by
    have hqnorm : ‖q‖<δ := by simpa only [mem_ball,dist_zero_right] using hq
    have hL := hLb _ (ball_subset_ball hdl (hmap q hq))
    have hnreal : (1:ℝ)≤n := by exact_mod_cast hn1
    have hO := (hOb w q (hqnorm.trans_le hdo)).trans (div_le_self hMo.le hnreal)
    have hH : ‖H q‖≤4*Mh/Real.pi^2 := (hHb q (ball_subset_ball hdh hq)).trans
      ((mul_le_mul_of_nonneg_left (tsum_hillOffDiagonalPeriodKernel_le n) hMh.le).trans_eq (by ring))
    exact (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans (add_le_add (add_le_add hL hO) hH))
  refine ⟨F,hFa,hFb,?_,?_,?_,?_,?_⟩
  · intro q hq
    let r : RealPeriodOneHillPotential := ⟨hillPeriodOneUnitPotential w q.val,
      hillPeriodOneUnitPotential_even w q.val,hillPeriodOneUnitPotential_real w q.val q.property⟩
    have hr : ‖r.val‖<δ := (norm_hillPeriodOneUnitPotential_le w q.val).trans_lt hq
    change L (hillPeriodOneCoefficientMap w q.val)+O (hillPeriodOneCoefficientMap w q.val)+H q.val=_
    rw [hillPeriodOneCoefficientMap_eq_unit,hLr r (hr.trans_le hdl),hOr r (hr.trans_le hdo),hHr q (hq.trans_le hdh)]
    exact (hillSummedRegularAbelianCorrection_eq_low_own_high h0q h0r r.val r.property.1 r.property.2 Nh hNh n hnH).symm
  · intro q hq
    exact (analyticAt_const.mul (hFa q hq)).cexp'
  · intro q hq
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    apply (Complex.re_le_norm (I*F q)).trans
    simpa only [norm_mul,norm_I,one_mul] using hFb q hq
  · intro q hq
    exact (analyticAt_const.mul (hFa q hq)).cexp'
  · intro q hq
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    apply (Complex.re_le_norm (-I*F q)).trans
    simpa only [norm_mul,norm_neg,norm_I,one_mul] using hFb q hq

end NLS.KdV
