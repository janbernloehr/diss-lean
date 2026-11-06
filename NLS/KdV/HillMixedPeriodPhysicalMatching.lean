import NLS.KdV.HillCommonMixedNormalizedPsi
import NLS.KdV.HillLocalPhysicalPeriodMatching
import NLS.KdV.HillComplexHilbertNormalizedUniqueness

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

/-- One real-source neighborhood identifies every actual mixed period,
including own periods, for every complex Hilbert numerator. -/
theorem exists_hillMixedComplexPeriods_physical_neighborhood
    (N : ℕ) (hN : 1≤N) (B D : ℝ) (hc : HillComplexTailPeriodControl h0q h0r N B D) :
    ∃ V : Set RealPeriodOneHillPotential, IsOpen V ∧ (⟨q,hq,hr⟩ : RealPeriodOneHillPotential)∈V ∧
      ∀ p∈V, ‖SpectralWeight.one.toCoeff p.val‖≤B → ∀ n k : ℕ, 1≤k → ∀ a : Coeff 2,
        (if k<N then hillAbelianComplexPeriod q hq hr n k (a,SpectralWeight.one.toCoeff p.val)
          else hillAbelianComplexPeriod 0 h0q h0r n k (a,SpectralWeight.one.toCoeff p.val))=
          hillAbelianHilbertPeriod p.val p.property.1 p.property.2 n k a := by
  obtain ⟨V,hV,hqV,hLow⟩ := exists_hillAbelianComplexPeriods_finite_physical_neighborhood q hq hr N
  refine ⟨V,hV,hqV,?_⟩
  intro p hp hpB n k hk a
  by_cases hkN : k<N
  · rw [if_pos hkN]
    exact hLow p hp k hk hkN n a
  · rw [if_neg hkN]
    exact hillHighAbelianComplexPeriod_eq_intrinsic_physical h0q h0r N hN B D hc
      p.val p.property.1 p.property.2 hpB n k (by omega) a

/-- Normalized mixed Kronecker periods determine the actual selected
physical differential, even when the Hilbert roots are complex. -/
theorem hillMixedNormalizedComplexPsi_eq_selected_of_physical_periods
    (N n : ℕ) (hn : 1≤n) (p : RealPeriodOneHillPotential) (a : Coeff 2)
    (hmatch : ∀ k : ℕ, 1≤k →
      (if k<N then hillAbelianComplexPeriod q hq hr n k (a,SpectralWeight.one.toCoeff p.val)
        else hillAbelianComplexPeriod 0 h0q h0r n k (a,SpectralWeight.one.toCoeff p.val))=
        hillAbelianHilbertPeriod p.val p.property.1 p.property.2 n k a)
    (hown : hillMixedOwnComplexPeriod q hq hr h0q h0r N n (a,SpectralWeight.one.toCoeff p.val)≠0)
    (hperiods : ∀ k : ℕ, 1≤k → hillMixedContourPeriod q hq hr h0q h0r N k (SpectralWeight.one.toCoeff p.val)
      (hillMixedNormalizedComplexPsi q hq hr h0q h0r N n (a,SpectralWeight.one.toCoeff p.val))=if k=n then 1 else 0) :
    hillMixedNormalizedComplexPsi q hq hr h0q h0r N n (a,SpectralWeight.one.toCoeff p.val)=
      hillAbelianSelectedGlobalPsi p.val p.property.1 p.property.2 n hn := by
  have he : hillMixedOwnComplexPeriod q hq hr h0q h0r N n (a,SpectralWeight.one.toCoeff p.val)=
      hillAbelianHilbertPeriod p.val p.property.1 p.property.2 n n a := hmatch n hn
  have hphys : hillAbelianHilbertPeriod p.val p.property.1 p.property.2 n n a≠0 := by
    rw [←he]
    exact hown
  have hzero (k : ℕ) (hk : 1≤k) (hkn : k≠n) :
      hillAbelianHilbertPeriod p.val p.property.1 p.property.2 n k a=0 := by
    have hp := hperiods k hk
    rw [hillMixedNormalizedComplexPsi_period_eq_ratio q hq hr h0q h0r N n k
      (a,SpectralWeight.one.toCoeff p.val),if_neg hkn,hmatch k hk,div_eq_zero_iff] at hp
    exact hp.resolve_right hown
  have huniq := hillAbelian_complex_normalized_hilbertPsi_eq_selected p.val p.property.1 p.property.2
    h0q h0r n hn a hphys hzero
  funext E
  change hillAbelianHilbertPsi n (E,a)/hillMixedOwnComplexPeriod q hq hr h0q h0r N n
    (a,SpectralWeight.one.toCoeff p.val)=_
  rw [he]
  exact congrFun huniq E

/-- One complex source ball and one real-source neighborhood support
analytic extensions of all actual selected physical numerators. -/
theorem exists_hillMixedNormalizedComplexPsi_common_physical_charts :
    ∃ N : ℕ, ∃ δ : ℝ, ∃ V : Set RealPeriodOneHillPotential,
      0<δ ∧ IsOpen V ∧ (⟨q,hq,hr⟩ : RealPeriodOneHillPotential)∈V ∧
      (∀ p∈V, SpectralWeight.one.toCoeff p.val∈ball (SpectralWeight.one.toCoeff q) δ) ∧
      ∀ n : ℕ, ∀ hn : 1≤n, ∃ a : Coeff 2 → Coeff 2,
        AnalyticOnNhd ℂ a (ball (SpectralWeight.one.toCoeff q) δ) ∧
        AnalyticOnNhd ℂ (fun t : ℂ × Coeff 2 => hillMixedNormalizedComplexPsi q hq hr h0q h0r N n (a t.2,t.2) t.1)
          (univ ×ˢ ball (SpectralWeight.one.toCoeff q) δ) ∧
        ∀ p∈V, hillMixedNormalizedComplexPsi q hq hr h0q h0r N n
          (a (SpectralWeight.one.toCoeff p.val),SpectralWeight.one.toCoeff p.val)=
          hillAbelianSelectedGlobalPsi p.val p.property.1 p.property.2 n hn := by
  obtain ⟨N,B,D,δ,A,C,c,hN,hB,hD,hc,hδ,hA,hC,hcpos,hsub,hcharts⟩ :=
    exists_hillMixedNormalizedComplexPsi_common_charts q hq hr h0q h0r
  obtain ⟨W,hW,hqW,hmatch⟩ := exists_hillMixedComplexPeriods_physical_neighborhood q hq hr h0q h0r N hN B D hc
  let P : RealPeriodOneHillPotential → Coeff 2 := fun p => SpectralWeight.one.toCoeff p.val
  have hP : Continuous P := SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val
  let V : Set RealPeriodOneHillPotential := W ∩ P ⁻¹' ball (SpectralWeight.one.toCoeff q) δ
  have hV : IsOpen V := hW.inter (isOpen_ball.preimage hP)
  have hqV : (⟨q,hq,hr⟩ : RealPeriodOneHillPotential)∈V := by
    refine ⟨hqW,?_⟩
    change SpectralWeight.one.toCoeff q∈ball (SpectralWeight.one.toCoeff q) δ
    exact mem_ball_self hδ
  refine ⟨N,δ,V,hδ,hV,hqV,fun p hp => hp.2,?_⟩
  intro n hn
  obtain ⟨a,ha,_,hAnal,_,hinfo⟩ := hcharts n hn
  refine ⟨a,ha,hAnal,?_⟩
  intro p hp
  have hpball : P p∈ball (SpectralWeight.one.toCoeff q) δ := hp.2
  have hpB : ‖P p‖≤B :=
    (show ‖P p‖<B by simpa only [mem_ball,dist_zero_right] using hsub hpball).le
  obtain ⟨_,_,hLower,_,hperiods⟩ := hinfo (P p) hpball
  exact hillMixedNormalizedComplexPsi_eq_selected_of_physical_periods q hq hr h0q h0r N n hn p (a (P p))
    (fun k hk => hmatch p hp.1 hpB n k hk (a (P p)))
    (norm_pos_iff.mp (hcpos.trans_le hLower)) hperiods

end NLS.KdV
