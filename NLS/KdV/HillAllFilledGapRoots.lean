import NLS.KdV.HillLocalFilledGapRoot
import NLS.ComplexAnalysis.FiniteHeadUniformTail

/-! # One complex source ball for every filled Hill gap root

Compact fixed-gap tubes cover the finite head. The verified bounded-source
tail controls the remaining gaps. Their combination does not intersect
infinitely many independent source neighborhoods.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillFilledFreeGapRoot_all_radius_data :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∀ k : ℕ+,
      AnalyticOnNhd ℂ (hillFilledFreeGapRoot h0q h0r (k : ℕ))
        (closedBall (freeHillEnergy k) (k : ℝ) ×ˢ ball (0 : Coeff 2) η) ∧
      ∀ p ∈ ball (0 : Coeff 2) η, ∀ E ∈ closedBall (freeHillEnergy k) (k : ℝ),
        hillFilledFreeGapRoot h0q h0r (k : ℕ) (E,p) ≠ 0 ∧
        hillL2Radicand p E = hillLocalGapPolynomial 0 h0q h0r (k : ℕ) p E *
          hillFilledFreeGapRoot h0q h0r (k : ℕ) (E,p)^2 := by
  let P := fun (k : ℕ+) (p : Coeff 2) => ∀ E ∈ closedBall (freeHillEnergy k) (k : ℝ),
    AnalyticAt ℂ (hillFilledFreeGapRoot h0q h0r (k : ℕ)) (E,p) ∧
      hillFilledFreeGapRoot h0q h0r (k : ℕ) (E,p) ≠ 0 ∧
      hillL2Radicand p E = hillLocalGapPolynomial 0 h0q h0r (k : ℕ) p E *
        hillFilledFreeGapRoot h0q h0r (k : ℕ) (E,p)^2
  have hlocal (k : ℕ+) : ∀ᶠ p in 𝓝 (0 : Coeff 2), P k p := by
    obtain ⟨V,hV,h0V,hdata⟩ := exists_hillFilledFreeGapRoot_local_radius_data h0q h0r k
    filter_upwards [hV.mem_nhds h0V] with p hp
    exact hdata p hp
  obtain ⟨Nu,_,hU⟩ := exists_hillFilledFreeGapRoot_bounded_complex_analytic h0q h0r 1
  obtain ⟨Nf,_,hfactor⟩ := exists_hillFilledFreeGapUnit_bounded_complex_factorization h0q h0r 1
  have htail (k : ℕ+) (hk : max Nu Nf ≤ (k : ℕ)) (p : Coeff 2) (hp : p ∈ ball 0 1) : P k p := by
    intro E hE
    obtain ⟨hc,hRlo,_⟩ := hillFreeGap_energy_radius_geometry h0q h0r k
    have hEold : E ∈ closedBall (hillRealGapCenter 0 h0q h0r (k : ℕ) : ℂ)
        (hillRealGapHalfLength 0 h0q h0r (k : ℕ)+hillRealGapCollar 0 h0q h0r (k : ℕ)) := by
      rw [hc]
      exact closedBall_subset_closedBall hRlo hE
    have hku := (le_max_left Nu Nf).trans hk
    have hkf := (le_max_right Nu Nf).trans hk
    have hd := (hU (k : ℕ) hku).2 p hp E hEold
    refine ⟨(hU (k : ℕ) hku).1 (E,p) ⟨hEold,hp⟩,hd.2.1,?_⟩
    rw [hd.1]
    exact hfactor p (mem_ball_zero_iff.mp hp).le (k : ℕ) hkf E
  obtain ⟨η,hη,hη1,hdata⟩ := exists_ball_forall_pos_index_of_local_and_uniform_tail
    P (0 : Coeff 2) hlocal (max Nu Nf) 1 (by norm_num) htail
  refine ⟨η,hη,hη1,?_⟩
  intro k
  exact ⟨fun t ht => (hdata k t.2 ht.2 t.1 ht.1).1,
    fun p hp E hE => (hdata k p hp E hE).2⟩

end NLS.KdV
