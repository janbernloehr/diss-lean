import NLS.KdV.HillUniformOpenGapCorrections
import NLS.KdV.HillUniformClosedGapCorrections

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

include h0q h0r in
/-- Uniform fixed-gap regular phase charts at any real source, including
both original open and original collapsed gaps. -/
theorem exists_hillRegularAbelianCorrection_uniform_fixed_gap_charts
    (k : ℕ) (hk : 1≤k) :
    ∃ δ C : ℝ, ∃ V : Set RealPeriodOneHillPotential,
      0<δ ∧ 0<C ∧ IsOpen V ∧ (⟨q,hq,hr⟩ : RealPeriodOneHillPotential)∈V ∧
      (∀ p∈V, SpectralWeight.one.toCoeff p.val∈ball (SpectralWeight.one.toCoeff q) δ) ∧
      ∀ n : ℕ, ∀ hn : 1≤n, ∃ β : Coeff 2 → ℂ,
        AnalyticOnNhd ℂ β (ball (SpectralWeight.one.toCoeff q) δ) ∧
        (∀ p∈ball (SpectralWeight.one.toCoeff q) δ, ‖β p‖≤C/(n : ℝ)) ∧
        ∀ p∈V, β (SpectralWeight.one.toCoeff p.val)=
          hillRegularAbelianCorrection p.val p.property.1 p.property.2 n hn k hk := by
  by_cases hgap : hillRealGapHalfLength q hq hr k=0
  · exact exists_hillRegularAbelianCorrection_uniform_closed_gap_charts q hq hr h0q h0r k hk hgap
  · exact exists_hillRegularAbelianCorrection_uniform_open_gap_charts q hq hr h0q h0r k hk hgap

include h0q h0r in
/-- Every finite low-gap sum of the actual regular corrections admits
one bounded analytic source chart before the differential index, around
any real source, with a quantitative inverse-index bound. -/
theorem exists_hillFiniteRegularCorrections_uniform_general_source_charts
    (S : Finset ℕ) (hS : ∀ k∈S, 1≤k) :
    ∃ δ C : ℝ, ∃ V : Set RealPeriodOneHillPotential,
      0<δ ∧ 0<C ∧ IsOpen V ∧ (⟨q,hq,hr⟩ : RealPeriodOneHillPotential)∈V ∧
      (∀ p∈V, SpectralWeight.one.toCoeff p.val∈ball (SpectralWeight.one.toCoeff q) δ) ∧
      ∀ n : ℕ, ∀ hn : 1≤n, ∃ β : Coeff 2 → ℂ,
        AnalyticOnNhd ℂ β (ball (SpectralWeight.one.toCoeff q) δ) ∧
        (∀ p∈ball (SpectralWeight.one.toCoeff q) δ, ‖β p‖≤C/(n : ℝ)) ∧
        ∀ p∈V, β (SpectralWeight.one.toCoeff p.val)=
          ∑ k∈S, if hk : 1≤k then hillRegularAbelianCorrection p.val p.property.1 p.property.2 n hn k hk else 0 := by
  induction S using Finset.induction_on with
  | empty =>
    let P : RealPeriodOneHillPotential → Coeff 2 := fun p => SpectralWeight.one.toCoeff p.val
    have hP : Continuous P := SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val
    let V := P ⁻¹' ball (SpectralWeight.one.toCoeff q) 1
    refine ⟨1,1,V,by norm_num,by norm_num,isOpen_ball.preimage hP,?_,(fun p hp => hp),?_⟩
    · change SpectralWeight.one.toCoeff q∈ball (SpectralWeight.one.toCoeff q) 1
      exact mem_ball_self (by norm_num)
    · intro n hn
      refine ⟨fun _ => 0,analyticOnNhd_const,?_,?_⟩
      · intro p hp
        simp only [norm_zero]
        positivity
      · intro p hp
        simp only [Finset.sum_empty]
  | @insert k S hkS ih =>
    have hk : 1≤k := hS k (Finset.mem_insert_self k S)
    have hS' : ∀ j∈S, 1≤j := fun j hj => hS j (Finset.mem_insert_of_mem hj)
    obtain ⟨δk,Ck,Vk,hδk,hCk,hVk,hqVk,_,hkcharts⟩ :=
      exists_hillRegularAbelianCorrection_uniform_fixed_gap_charts q hq hr h0q h0r k hk
    obtain ⟨δs,Cs,Vs,hδs,hCs,hVs,hqVs,_,hscharts⟩ := ih hS'
    let δ := min δk δs
    have hδ : 0<δ := lt_min hδk hδs
    have hdk : δ≤δk := min_le_left _ _
    have hds : δ≤δs := min_le_right _ _
    let P : RealPeriodOneHillPotential → Coeff 2 := fun p => SpectralWeight.one.toCoeff p.val
    have hP : Continuous P := SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val
    let V := (Vk∩Vs)∩P ⁻¹' ball (SpectralWeight.one.toCoeff q) δ
    have hV : IsOpen V := (hVk.inter hVs).inter (isOpen_ball.preimage hP)
    have hqV : (⟨q,hq,hr⟩ : RealPeriodOneHillPotential)∈V := by
      refine ⟨⟨hqVk,hqVs⟩,?_⟩
      change SpectralWeight.one.toCoeff q∈ball (SpectralWeight.one.toCoeff q) δ
      exact mem_ball_self hδ
    refine ⟨δ,Ck+Cs,V,hδ,add_pos hCk hCs,hV,hqV,(fun p hp => hp.2),?_⟩
    intro n hn
    obtain ⟨βk,hka,hkb,hkr⟩ := hkcharts n hn
    obtain ⟨βs,hsa,hsb,hsr⟩ := hscharts n hn
    refine ⟨fun p => βk p+βs p,(hka.mono (ball_subset_ball hdk)).add (hsa.mono (ball_subset_ball hds)),?_,?_⟩
    · intro p hp
      apply (norm_add_le _ _).trans
      apply (add_le_add (hkb p (ball_subset_ball hdk hp)) (hsb p (ball_subset_ball hds hp))).trans_eq
      ring
    · intro p hp
      dsimp only
      rw [hkr p hp.1.1,hsr p hp.1.2,Finset.sum_insert hkS,dif_pos hk]

end NLS.KdV
