import NLS.KdV.HillFixedGapUniformRegularCorrection

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

include h0q h0r in
/-- A finite set of original regular gap corrections has a common
bounded analytic source chart before every differential index. -/
theorem exists_hillFinite_regularAbelianCorrection_uniform_charts
    (S : Finset ℕ) (hS : ∀ k∈S, 1≤k) :
    ∃ δ C : ℝ, 0<δ ∧ 0<C ∧ ∀ n : ℕ, ∀ hn : 1≤n,
      ∃ β : Coeff 2 → ℂ, AnalyticOnNhd ℂ β (ball 0 δ) ∧
        (∀ p∈ball 0 δ, ‖β p‖≤C) ∧
        ∀ q : RealPeriodOneHillPotential, ‖q.val‖<δ →
          β (SpectralWeight.one.toCoeff q.val)=
            ∑ k∈S, if hk : 1≤k then
              hillRegularAbelianCorrection q.val q.property.1 q.property.2 n hn k hk else 0 := by
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨1,1,by norm_num,by norm_num,?_⟩
    intro n hn
    refine ⟨fun _ => 0,analyticOnNhd_const,?_,?_⟩
    · intro p hp
      simp
    · intro q hq
      simp
  | @insert k S hkS ih =>
    have hk : 1≤k := hS k (Finset.mem_insert_self k S)
    have hS' : ∀ j∈S, 1≤j := fun j hj => hS j (Finset.mem_insert_of_mem hj)
    obtain ⟨δk,Ck,hδk,hCk,hkcharts⟩ := exists_hillFixedGap_regularAbelianCorrection_uniform_charts h0q h0r k hk
    obtain ⟨δs,Cs,hδs,hCs,hscharts⟩ := ih hS'
    let δ := min δk δs
    have hδ : 0<δ := lt_min hδk hδs
    have hdk : δ≤δk := min_le_left _ _
    have hds : δ≤δs := min_le_right _ _
    refine ⟨δ,Ck+Cs,hδ,add_pos hCk hCs,?_⟩
    intro n hn
    obtain ⟨βk,hka,hkb,hkr⟩ := hkcharts n hn
    obtain ⟨βs,hsa,hsb,hsr⟩ := hscharts n hn
    refine ⟨fun p => βk p+βs p,(hka.mono (ball_subset_ball hdk)).add
      (hsa.mono (ball_subset_ball hds)),?_,?_⟩
    · intro p hp
      exact (norm_add_le _ _).trans (add_le_add (hkb p (ball_subset_ball hdk hp)) (hsb p (ball_subset_ball hds hp)))
    · intro q hq
      dsimp only
      rw [hkr q (hq.trans_le hdk),hsr q (hq.trans_le hds),Finset.sum_insert hkS,dif_pos hk]

end NLS.KdV
