import NLS.KdV.HillGeneralOffDiagonalPhase
import NLS.KdV.HillGeneralOwnCorrections
import NLS.KdV.HillUniformFiniteGapCorrections
import NLS.KdV.HillUniformFullRegularPhase

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

include h0q h0r in
/-- The actual full summed regular phases have uniformly bounded
analytic native charts around every real source. All constants, the
real neighborhood and high index cutoff precede n and the spectral weight. -/
theorem exists_hillSummedRegularAbelianCorrection_uniform_general_native_charts (L : ℝ) (hL : 0≤L) :
    ∃ δ M : ℝ, ∃ N : ℕ, ∃ V : Set RealPeriodOneHillPotential,
      0<δ ∧ 0<M ∧ ∃ hN : 1≤N, IsOpen V ∧ (⟨q,hq,hr⟩ : RealPeriodOneHillPotential)∈V ∧
      (∀ p∈V, SpectralWeight.one.toCoeff p.val∈ball (SpectralWeight.one.toCoeff q) δ) ∧
      ∀ n : ℕ, ∀ hn : N≤n, ∀ w : SpectralWeight,
      ∃ F : WeightedCoeff w.doubleIndex.toWeight 2 → ℂ,
        AnalyticOnNhd ℂ F (hillNativeSourceDomain w (SpectralWeight.one.toCoeff q) δ L) ∧
        (∀ r : WeightedCoeff w.doubleIndex.toWeight 2,
          hillPeriodOneCoefficientMap w r∈ball (SpectralWeight.one.toCoeff q) δ → ‖r‖<L → ‖F r‖≤M) ∧
        (∀ r : RealHillWeightedPotential w, hillRealWeightedEmbedding w r∈V → ‖r.val‖<L →
          F r.val=hillSummedRegularAbelianCorrection (hillPeriodOneUnitPotential w r.val)
            (hillPeriodOneUnitPotential_even w r.val) (hillPeriodOneUnitPotential_real w r.val r.property) n (hN.trans hn)) ∧
        AnalyticOnNhd ℂ (fun r => Complex.exp (I*F r))
          (hillNativeSourceDomain w (SpectralWeight.one.toCoeff q) δ L) ∧
        AnalyticOnNhd ℂ (fun r => Complex.exp (-I*F r))
          (hillNativeSourceDomain w (SpectralWeight.one.toCoeff q) δ L) ∧
        ∀ r : WeightedCoeff w.doubleIndex.toWeight 2,
          hillPeriodOneCoefficientMap w r∈ball (SpectralWeight.one.toCoeff q) δ → ‖r‖<L →
            ‖Complex.exp (I*F r)‖≤Real.exp M ∧ ‖Complex.exp (-I*F r)‖≤Real.exp M := by
  obtain ⟨δh,Mh,Nh,Vh,hδh,hMh,hNh,hVh,hqVh,_,hhigh⟩ :=
    exists_hillHighOffDiagonalRegularCorrection_general_native_charts q hq hr h0q h0r L hL
  obtain ⟨δo,Mo,No,Vo,hδo,hMo,hNo,hVo,hqVo,_,hown⟩ :=
    exists_hillOwnRegularAbelianCorrection_general_native_charts q hq hr h0q h0r L hL
  let S := (Finset.range Nh).filter (fun k => 1≤k)
  obtain ⟨δl,Cl,Vl,hδl,hCl,hVl,hqVl,_,hlow⟩ :=
    exists_hillFiniteRegularCorrections_uniform_general_source_charts q hq hr h0q h0r S
      (fun k hk => (Finset.mem_filter.mp hk).2)
  let δ := min δh (min δo δl)
  let M := Cl+Mo+Mh
  let N := max Nh No
  have hδ : 0<δ := lt_min hδh (lt_min hδo hδl)
  have hM : 0<M := by dsimp only [M];positivity
  have hN : 1≤N := hNh.trans (le_max_left _ _)
  have hdh : δ≤δh := min_le_left _ _
  have hdo : δ≤δo := (min_le_right _ _).trans (min_le_left _ _)
  have hdl : δ≤δl := (min_le_right _ _).trans (min_le_right _ _)
  let P : RealPeriodOneHillPotential → Coeff 2 := fun p => SpectralWeight.one.toCoeff p.val
  have hP : Continuous P := SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val
  let V := ((Vh∩Vo)∩Vl)∩P ⁻¹' ball (SpectralWeight.one.toCoeff q) δ
  have hV : IsOpen V := ((hVh.inter hVo).inter hVl).inter (isOpen_ball.preimage hP)
  have hqV : (⟨q,hq,hr⟩ : RealPeriodOneHillPotential)∈V := by
    refine ⟨⟨⟨hqVh,hqVo⟩,hqVl⟩,?_⟩
    change SpectralWeight.one.toCoeff q∈ball (SpectralWeight.one.toCoeff q) δ
    exact mem_ball_self hδ
  refine ⟨δ,M,N,V,hδ,hM,hN,hV,hqV,(fun p hp => hp.2),?_⟩
  intro n hn w
  have hn1 : 1≤n := hN.trans hn
  have hnH : Nh≤n := (le_max_left _ _).trans hn
  have hnO : No≤n := (le_max_right _ _).trans hn
  obtain ⟨H,hHa,hHb,hHr⟩ := hhigh n hn1 w
  obtain ⟨O,hOa,hOb,hOr⟩ := hown n hnO
  obtain ⟨A,hAa,hAb,hAr⟩ := hlow n hn1
  let D := hillNativeSourceDomain w (SpectralWeight.one.toCoeff q) δ L
  have hnorm (r : WeightedCoeff w.doubleIndex.toWeight 2) (hr : r∈D) : ‖r‖<L := by
    exact hr.2
  let F : WeightedCoeff w.doubleIndex.toWeight 2 → ℂ := fun r =>
    A (hillPeriodOneCoefficientMap w r)+O (hillPeriodOneCoefficientMap w r)+H r
  have hFa : AnalyticOnNhd ℂ F D := by
    exact ((analyticOnNhd_hillNativeSource_pullback w (SpectralWeight.one.toCoeff q) δ L A
      (hAa.mono (ball_subset_ball hdl))).add
      (analyticOnNhd_hillNativeSource_pullback w (SpectralWeight.one.toCoeff q) δ L O
        (hOa.mono (ball_subset_ball hdo)))).add
      (hHa.mono (fun r hr => ⟨ball_subset_ball hdh hr.1,hr.2⟩))
  have hFb (r : WeightedCoeff w.doubleIndex.toWeight 2) (hr : r∈D) : ‖F r‖≤M := by
    have hnreal : (1 : ℝ)≤n := by exact_mod_cast hn1
    have hA := (hAb _ (ball_subset_ball hdl hr.1)).trans (div_le_self hCl.le hnreal)
    have hO := (hOb w r (hnorm r hr).le (ball_subset_ball hdo hr.1)).trans (div_le_self hMo.le hnreal)
    exact (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans (add_le_add (add_le_add hA hO) (hHb r (ball_subset_ball hdh hr.1) (hnorm r hr))))
  refine ⟨F,hFa,(fun r hr hnormr => hFb r ⟨hr,hnormr⟩),?_,?_,?_,?_⟩
  · intro r hrV hrnorm
    let p := hillRealWeightedEmbedding w r
    have hcoef : hillPeriodOneCoefficientMap w r.val=SpectralWeight.one.toCoeff p.val := hillPeriodOneCoefficientMap_eq_unit w r.val
    change A (hillPeriodOneCoefficientMap w r.val)+O (hillPeriodOneCoefficientMap w r.val)+H r.val=_
    rw [hcoef,hAr p hrV.1.2,hOr p hrV.1.1.2,hHr r hrV.1.1.1 hrnorm]
    exact (hillSummedRegularAbelianCorrection_eq_low_own_high h0q h0r p.val p.property.1 p.property.2 Nh hNh n hnH).symm
  · intro r hr
    exact (analyticAt_const.mul (hFa r hr)).cexp'
  · intro r hr
    exact (analyticAt_const.mul (hFa r hr)).cexp'
  · intro r hr hrnorm
    have hbound := hFb r ⟨hr,hrnorm⟩
    constructor
    · rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      apply (Complex.re_le_norm (I*F r)).trans
      simpa only [norm_mul,norm_I,one_mul] using hbound
    · rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      apply (Complex.re_le_norm (-I*F r)).trans
      simpa only [norm_mul,norm_neg,norm_I,one_mul] using hbound

end NLS.KdV
