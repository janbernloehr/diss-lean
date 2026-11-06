import NLS.KdV.HillBoundedNormalizedContourBounds
import NLS.KdV.HillMixedPeriodPhysicalMatching
import NLS.KdV.HillUniformAllContourBounds

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
/-- Common physical normalized differential charts at any original real
source, with high own-radius and full off-diagonal kernel bounds. -/
theorem exists_hillSelectedPsi_uniform_general_high_contour_charts :
    ∃ δ S B : ℝ, ∃ J : ℕ, ∃ V : Set RealPeriodOneHillPotential,
      0<δ ∧ 0<S ∧ 0<B ∧ 1≤J ∧ ball (SpectralWeight.one.toCoeff q) δ⊆ball 0 B ∧
      IsOpen V ∧ (⟨q,hq,hr⟩ : RealPeriodOneHillPotential)∈V ∧
      (∀ p∈V, SpectralWeight.one.toCoeff p.val∈ball (SpectralWeight.one.toCoeff q) δ) ∧
      ∀ n : ℕ, ∀ hn : 1≤n, ∃ G : ℂ × Coeff 2 → ℂ,
        AnalyticOnNhd ℂ G (univ ×ˢ ball (SpectralWeight.one.toCoeff q) δ) ∧
        (∀ p∈V, ∀ E : ℂ, G (E,SpectralWeight.one.toCoeff p.val)=
          hillAbelianSelectedGlobalPsi p.val p.property.1 p.property.2 n hn E) ∧
        ∀ p∈ball (SpectralWeight.one.toCoeff q) δ, ∀ k : ℕ, J≤k →
          (∀ E∈sphere (hillRealGapCenter 0 h0q h0r k : ℂ)
            (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k),
            (E,p)∈hillAbelianComplexRootDomain 0 h0q h0r ∧
            ‖G (E,p)/hillAbelianComplexRoot 0 h0q h0r (E,p)‖≤S/
              (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k) ∧
            (k≠n → ‖G (E,p)/hillAbelianComplexRoot 0 h0q h0r (E,p)‖≤S*hillOffDiagonalPeriodKernel n (k : ℤ))) ∧
          (2*(Real.pi : ℂ))⁻¹ * ∮ E in C((hillRealGapCenter 0 h0q h0r k : ℂ),
            hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k),
            G (E,p)/hillAbelianComplexRoot 0 h0q h0r (E,p)=if k=n then 1 else 0 := by
  obtain ⟨N,B,D,δ,A,C,c,hN,hB,hD,hc,hδ,hA,hC,hcpos,hsub,hcharts⟩ :=
    exists_hillMixedNormalizedComplexPsi_common_charts q hq hr h0q h0r
  obtain ⟨J0,hJ0,K,hK,hinv⟩ := exists_hillFreeGapContour_bounded_complex_tail_inverse_bound h0q h0r B
  obtain ⟨W,hW,hqW,hmatch⟩ := exists_hillMixedComplexPeriods_physical_neighborhood q hq hr h0q h0r N hN B D hc
  let J := max N J0
  have hJ : 1≤J := hN.trans (le_max_left _ _)
  let S := 4*Real.exp ((8/Real.pi^2)*A)*(1+K*B)/c
  have hS : 0<S := by dsimp only [S];positivity
  let P : RealPeriodOneHillPotential → Coeff 2 := fun p => SpectralWeight.one.toCoeff p.val
  have hP : Continuous P := SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val
  let V := W∩P ⁻¹' ball (SpectralWeight.one.toCoeff q) δ
  have hV : IsOpen V := hW.inter (isOpen_ball.preimage hP)
  have hqV : (⟨q,hq,hr⟩ : RealPeriodOneHillPotential)∈V := by
    refine ⟨hqW,?_⟩
    change SpectralWeight.one.toCoeff q∈ball (SpectralWeight.one.toCoeff q) δ
    exact mem_ball_self hδ
  have hpB (p : Coeff 2) (hp : p∈ball (SpectralWeight.one.toCoeff q) δ) : ‖p‖≤B :=
    (show ‖p‖<B by simpa only [mem_ball,dist_zero_right] using hsub hp).le
  refine ⟨δ,S,B,J,V,hδ,hS,hB,hJ,hsub,hV,hqV,(fun p hp => hp.2),?_⟩
  intro n hn
  obtain ⟨a,_,_,hGa,_,hinfo⟩ := hcharts n hn
  let G : ℂ × Coeff 2 → ℂ := fun t => hillMixedNormalizedComplexPsi q hq hr h0q h0r N n (a t.2,t.2) t.1
  refine ⟨G,hGa,?_,?_⟩
  · intro p hp E
    obtain ⟨_,_,hLower,_,hperiods⟩ := hinfo (P p) hp.2
    have he := hillMixedNormalizedComplexPsi_eq_selected_of_physical_periods q hq hr h0q h0r N n hn p (a (P p))
      (fun k hk => hmatch p hp.1 (hpB (P p) hp.2) n k hk (a (P p)))
      (norm_pos_iff.mp (hcpos.trans_le hLower)) hperiods
    exact congrFun he E
  · intro p hp k hk
    obtain ⟨_,ha,hLower,_,hperiods⟩ := hinfo p hp
    have hkN : N≤k := (le_max_left _ _).trans hk
    have hk0 : J0≤k := (le_max_right _ _).trans hk
    have hk1 : 1≤k := hJ.trans hk
    have hcoef : 4*Real.exp ((8/Real.pi^2)*‖a p‖)*(1+K*‖p‖)/c≤S := by
      dsimp only [S]
      gcongr
      exact hpB p hp
    refine ⟨?_,?_⟩
    · intro E hE
      obtain ⟨hdom,hb⟩ := hinv p (hpB p hp) k hk0 E hE
      have hR : 0<hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k :=
        add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k hk1).1 (hillRealGapContour_geometry 0 h0q h0r k hk1).2.1
      have hscaled (hkn : k≠n) : ‖(((freeHillValue k : ℂ)-(freeHillValue n : ℂ))/(n : ℂ))*
          (G (E,p)/hillAbelianComplexRoot 0 h0q h0r (E,p))‖≤S/(k : ℝ) :=
        (norm_scaled_hillAbelianHilbertPsi_normalized_root_le h0q h0r n k hn hk1 (Ne.symm hkn) (a p) p
          (hillMixedOwnComplexPeriod q hq hr h0q h0r N n (a p,p)) c K hcpos hK.le hLower E hE hdom hb).trans
            (div_le_div_of_nonneg_right hcoef (Nat.cast_nonneg k))
      refine ⟨hdom,?_,fun hkn => norm_le_hillOffDiagonalPeriodKernel_of_scaled_bound n k hn hk1 hkn S _ (hscaled hkn)⟩
      by_cases hkn : k=n
      · subst k
        apply (norm_hillAbelianHilbertPsi_normalized_own_root_le h0q h0r n hn (a p) p
          (hillMixedOwnComplexPeriod q hq hr h0q h0r N n (a p,p)) c K hcpos hK.le hLower E hE hdom hb).trans
        apply div_le_div_of_nonneg_right _ hR.le
        apply le_trans _ hcoef
        gcongr
        norm_num
      · apply (norm_le_hillOffDiagonalPeriodKernel_of_scaled_bound n k hn hk1 hkn S _ (hscaled hkn)).trans
        apply (le_div_iff₀ hR).mpr
        have hh := mul_le_mul_of_nonneg_left (hillFreeGapRadius_mul_periodKernel_le h0q h0r n k hk1 hkn) hS.le
        nlinarith
    · have he := hperiods k hk1
      simpa only [hillMixedContourPeriod,if_neg (not_lt.mpr hkN)] using he

end NLS.KdV
