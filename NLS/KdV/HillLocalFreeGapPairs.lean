import NLS.KdV.HillFreeGapQuotient

/-! # Arbitrarily small fixed-gap clusters near the free potential

The compact annulus outside a prescribed smaller collar contains no free
zeros. Joint continuity keeps it zero-free on one source neighborhood.
The existing actual pair in the original collar must therefore lie inside
the smaller collar. No individual analytic endpoint labels are chosen.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillFreeGap_localized_pairs_neighborhood
    (k : ℕ) (hk : 1 ≤ k) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ V : Set (Coeff 2), IsOpen V ∧ (0 : Coeff 2) ∈ V ∧ ∀ p ∈ V,
      (∀ E ∈ sphere (hillRealGapCenter 0 h0q h0r k : ℂ)
        (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k), hillL2Radicand p E ≠ 0) ∧
      ∃ a ∈ ball (hillRealGapCenter 0 h0q h0r k : ℂ)
        (ρ*(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)),
      ∃ b ∈ ball (hillRealGapCenter 0 h0q h0r k : ℂ)
        (ρ*(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)),
        hillL2Radicand p a = 0 ∧ hillL2Radicand p b = 0 ∧
        ∀ E ∈ closedBall (hillRealGapCenter 0 h0q h0r k : ℂ)
          (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k),
          analyticOrderNatAt (hillL2Radicand p) E = ({a,b} : Multiset ℂ).count E := by
  let c : ℂ := hillRealGapCenter 0 h0q h0r k
  let R := hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k
  let K := closedBall c R \ ball c (ρ*R)
  let D : Set (ℂ × Coeff 2) := {t | hillL2Radicand t.2 t.1 ≠ 0}
  have hR : 0 < R := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k hk).1
    (hillRealGapContour_geometry 0 h0q h0r k hk).2.1
  have hK : IsCompact K := (isCompact_closedBall c R).diff isOpen_ball
  have hcont : Continuous (fun t : ℂ × Coeff 2 => hillL2Radicand t.2 t.1) :=
    continuous_iff_continuousAt.mpr (fun t => (analyticOnNhd_hillL2Radicand_joint t (mem_univ _)).continuousAt)
  have hD : IsOpen D := isOpen_ne_fun hcont continuous_const
  have hbase : K ×ˢ {(0 : Coeff 2)} ⊆ D := by
    rintro ⟨E,p⟩ ⟨hE,hp⟩
    have hp0 : p = 0 := hp
    subst p
    intro hz
    have he := hillScaledFreeGapContour_zero_unique h0q h0r 1 le_rfl k hk E
      (by simpa only [one_mul] using hE.1) hz
    exact hE.2 (he ▸ mem_ball_self (mul_pos hρ hR))
  obtain ⟨U,W,_,hW,hKU,h0W,hUW⟩ := generalized_tube_lemma hK isCompact_singleton hD hbase
  obtain ⟨V,hV,h0V,hpair⟩ := exists_hillComplexGapPair_neighborhood 0 h0q h0r k hk
  refine ⟨V ∩ W,hV.inter hW,⟨by simpa only [map_zero] using h0V,h0W (mem_singleton _)⟩,?_⟩
  intro p hp
  obtain ⟨hb,a,ha,b,hb',haz,hbz,hm⟩ := hpair p hp.1
  have hsmall (E : ℂ) (hE : E ∈ closedBall c R) (hz : hillL2Radicand p E = 0) : E ∈ ball c (ρ*R) := by
    by_contra hn
    have hEp : (E,p) ∈ U ×ˢ W := ⟨hKU (show E ∈ K from ⟨hE,hn⟩),hp.2⟩
    have hDp : (E,p) ∈ D := hUW hEp
    exact hDp hz
  exact ⟨hb,a,hsmall a (ball_subset_closedBall ha) haz,b,hsmall b (ball_subset_closedBall hb') hbz,haz,hbz,hm⟩

end NLS.KdV
