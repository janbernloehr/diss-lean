import NLS.KdV.HillMixedPeriodPhysicalMatching
import NLS.KdV.HillNormalizedNumeratorBounds

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
/-- Every original real Hill source has common analytic extensions of
all selected normalized numerators, with genuine physical matching and
one entire growth bound of order inverse differential index. -/
theorem exists_hillSelectedGlobalPsi_common_bounded_analytic_extension :
    ∃ δ M : ℝ, ∃ V : Set RealPeriodOneHillPotential,
      0<δ ∧ 0<M ∧ IsOpen V ∧ (⟨q,hq,hr⟩ : RealPeriodOneHillPotential)∈V ∧
      (∀ p∈V, SpectralWeight.one.toCoeff p.val∈ball (SpectralWeight.one.toCoeff q) δ) ∧
      ∀ n : ℕ, ∀ hn : 1≤n, ∃ F : ℂ × Coeff 2 → ℂ,
        AnalyticOnNhd ℂ F (univ ×ˢ ball (SpectralWeight.one.toCoeff q) δ) ∧
        (∀ p∈V, ∀ E : ℂ, F (E,SpectralWeight.one.toCoeff p.val)=
          hillAbelianSelectedGlobalPsi p.val p.property.1 p.property.2 n hn E) ∧
        ∀ p∈ball (SpectralWeight.one.toCoeff q) δ, ∀ E : ℂ,
          ‖F (E,p)‖≤M*Real.exp (2*‖E‖*‖hillAbelianHilbertWeight 0‖)/(n : ℝ) := by
  obtain ⟨N,B,D,δ,A,C,c,hN,hB,hD,hc,hδ,hA,hC,hcpos,hsub,hcharts⟩ :=
    exists_hillMixedNormalizedComplexPsi_common_charts q hq hr h0q h0r
  obtain ⟨W,hW,hqW,hmatch⟩ := exists_hillMixedComplexPeriods_physical_neighborhood q hq hr h0q h0r N hN B D hc
  let P : RealPeriodOneHillPotential → Coeff 2 := fun p => SpectralWeight.one.toCoeff p.val
  let V : Set RealPeriodOneHillPotential := W ∩ P ⁻¹' ball (SpectralWeight.one.toCoeff q) δ
  have hP : Continuous P := SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val
  have hV : IsOpen V := hW.inter (isOpen_ball.preimage hP)
  have hqV : (⟨q,hq,hr⟩ : RealPeriodOneHillPotential)∈V := by
    refine ⟨hqW,?_⟩
    change SpectralWeight.one.toCoeff q∈ball (SpectralWeight.one.toCoeff q) δ
    exact mem_ball_self hδ
  let M := (2/Real.pi)*Real.exp (A*‖hillAbelianHilbertWeight 0‖)/c
  have hM : 0<M := by dsimp only [M];positivity
  refine ⟨δ,M,V,hδ,hM,hV,hqV,fun p hp => hp.2,?_⟩
  intro n hn
  obtain ⟨a,_,_,hAnal,_,hinfo⟩ := hcharts n hn
  let F : ℂ × Coeff 2 → ℂ := fun t => hillMixedNormalizedComplexPsi q hq hr h0q h0r N n (a t.2,t.2) t.1
  refine ⟨F,hAnal,?_,?_⟩
  · intro p hp E
    have hpball : P p∈ball (SpectralWeight.one.toCoeff q) δ := hp.2
    have hpB : ‖P p‖≤B :=
      (show ‖P p‖<B by simpa only [mem_ball,dist_zero_right] using hsub hpball).le
    obtain ⟨_,_,hLower,_,hperiods⟩ := hinfo (P p) hpball
    have he := hillMixedNormalizedComplexPsi_eq_selected_of_physical_periods q hq hr h0q h0r N n hn p (a (P p))
      (fun k hk => hmatch p hp.1 hpB n k hk (a (P p)))
      (norm_pos_iff.mp (hcpos.trans_le hLower)) hperiods
    exact congrFun he E
  · intro p hp E
    obtain ⟨_,ha,hLower,_,_⟩ := hinfo p hp
    have hb := norm_hillMixedNormalizedComplexPsi_le_of_bounds q hq hr h0q h0r N n hn (a p) p E A ‖E‖ c
      hcpos ha le_rfl hLower
    apply hb.trans_eq
    dsimp only [M]
    rw [add_mul,Real.exp_add]
    ring

end NLS.KdV
