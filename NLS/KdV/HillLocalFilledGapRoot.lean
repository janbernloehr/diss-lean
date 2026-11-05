import NLS.KdV.HillRadiusRootProduct

/-! # Filled roots on each fixed radius-k disc near zero

The complete smaller closed energy disc lies strictly inside the free
intrinsic collar. A compact tube in the existing local root domain gives
one complex source neighborhood, independent of every output index.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillFreeGap_energy_radius_strict (k : ℕ+) :
    (k : ℝ) < hillRealGapHalfLength 0 h0q h0r (k : ℕ)+hillRealGapCollar 0 h0q h0r (k : ℕ) := by
  rw [hillFreeGapHalfLength h0q h0r (k : ℕ) k.property,zero_add,
    hillFreeGapCollar h0q h0r (k : ℕ) k.property]
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast k.property
  have hprod := mul_nonneg (show 0 ≤ (k : ℝ)-1 by linarith) (sq_nonneg Real.pi)
  have hpos := mul_pos (show 0 < Real.pi^2-4 by nlinarith [Real.pi_gt_three])
    (show 0 < (k : ℝ) by positivity)
  nlinarith

theorem exists_hillFilledFreeGapRoot_local_radius_data (k : ℕ+) :
    ∃ V : Set (Coeff 2), IsOpen V ∧ (0 : Coeff 2) ∈ V ∧ ∀ p ∈ V,
      ∀ E ∈ closedBall (freeHillEnergy k) (k : ℝ),
        AnalyticAt ℂ (hillFilledFreeGapRoot h0q h0r (k : ℕ)) (E,p) ∧
        hillFilledFreeGapRoot h0q h0r (k : ℕ) (E,p) ≠ 0 ∧
        hillL2Radicand p E = hillLocalGapPolynomial 0 h0q h0r (k : ℕ) p E *
          hillFilledFreeGapRoot h0q h0r (k : ℕ) (E,p)^2 := by
  let c : ℂ := hillRealGapCenter 0 h0q h0r (k : ℕ)
  let R := hillRealGapHalfLength 0 h0q h0r (k : ℕ)+hillRealGapCollar 0 h0q h0r (k : ℕ)
  have hc := (hillFreeGap_energy_radius_geometry h0q h0r k).1
  have hR := hillFreeGap_energy_radius_strict h0q h0r k
  have hEold (E : ℂ) (hE : E ∈ closedBall (freeHillEnergy k) (k : ℝ)) : E ∈ ball c R := by
    dsimp only [c]
    rw [hc]
    exact (closedBall_subset_ball (show (k : ℝ) < R from hR)) hE
  have hbase : closedBall (freeHillEnergy k) (k : ℝ) ×ˢ {(0 : Coeff 2)} ⊆
      hillLocalDeflatedRootDomain 0 h0q h0r (k : ℕ) := by
    rintro ⟨E,p⟩ ⟨hE,hp⟩
    have hp0 : p = 0 := hp
    subst p
    simpa only [map_zero] using mem_hillLocalDeflatedRootDomain_base 0 h0q h0r (k : ℕ) k.property E (hEold E hE)
  obtain ⟨U,V,_,hV,hKU,h0V,hUV⟩ := generalized_tube_lemma
    (isCompact_closedBall (freeHillEnergy k) (k : ℝ)) isCompact_singleton
    (isOpen_hillLocalDeflatedRootDomain 0 h0q h0r (k : ℕ) k.property) hbase
  obtain ⟨W,hW,h0W,hfactor⟩ := exists_hillLocalGapUnit_factorization_neighborhood 0 h0q h0r (k : ℕ) k.property
  refine ⟨V ∩ W,hV.inter hW,⟨h0V (mem_singleton _),by simpa only [map_zero] using h0W⟩,?_⟩
  intro p hp E hE
  have hD : (E,p) ∈ hillLocalDeflatedRootDomain 0 h0q h0r (k : ℕ) :=
    hUV (show (E,p) ∈ U ×ˢ V from ⟨hKU hE,hp.1⟩)
  have heq : hillFilledFreeGapRoot h0q h0r (k : ℕ) =ᶠ[𝓝 (E,p)]
      hillLocalDeflatedComplexRoot 0 h0q h0r (k : ℕ) := by
    filter_upwards [(isOpen_ball.preimage (continuous_fst : Continuous (Prod.fst : ℂ × Coeff 2 → ℂ))).mem_nhds (hEold E hE)] with t ht
    exact hillFilledFreeGapRoot_eq_local h0q h0r (k : ℕ) t.2 t.1 ht
  have hpoint := hillFilledFreeGapRoot_eq_local h0q h0r (k : ℕ) p E (hEold E hE)
  refine ⟨(analyticOnNhd_hillLocalDeflatedComplexRoot 0 h0q h0r (k : ℕ) k.property _ hD).congr heq.symm,?_,?_⟩
  · rw [hpoint]
    exact hillLocalDeflatedComplexRoot_ne_zero 0 h0q h0r (k : ℕ) k.property _ hD
  · rw [hpoint,hillLocalDeflatedComplexRoot_sq 0 h0q h0r (k : ℕ) k.property _ hD]
    exact (hfactor p hp.2 E (hEold E hE)).1

end NLS.KdV
