import NLS.Articles.KdVKdV2Frequencies.NativeRegularGapNumerators
import NLS.KdV.HillNativeQuadraticSolution

/-! # Actual physical regular differentials have native filled-gap solutions

One common complex source ball supports a family in the complete output
Hilbert space. The quadratic equation includes the own unit subtraction.
The solutions are jointly analytic on filled high-gap discs and satisfy
one full Hilbert norm estimate, including collapsed gaps.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV

private theorem zero_parity : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0 := by
  rw [map_zero]
  exact Submodule.zero_mem _
private theorem zero_real : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)) := by
  rw [map_zero]
  intro k
  simp

/-- Actual regular physical differential numerators admit native Hilbert
solutions of the symmetric gap equation, with a common `18*pi*M/k` bound.
Physical terminal values and summation of the resulting phases are separate
obligations. -/
theorem exists_hillPhysical_native_regular_gap_solutions :
    ∃ η : ℝ, ∃ G : ℂ × Coeff 2 → Coeff 2,
      ∃ H : ℕ+ → ℂ × Coeff 2 → Coeff 2, ∃ N : ℕ, ∃ M : ℝ,
      0 < η ∧ 1 ≤ N ∧ 0 < M ∧ AnalyticOnNhd ℂ G (univ ×ˢ ball (0 : Coeff 2) η) ∧
      (∀ k : ℕ+, N ≤ (k : ℕ) →
        AnalyticOnNhd ℂ (H k)
          (ball (freeHillEnergy k) (3*(k : ℝ)/4) ×ˢ ball (0 : Coeff 2) η) ∧
        (∀ u ∈ ball (0 : Coeff 2) η, ∀ E ∈ ball (freeHillEnergy k) (3*(k : ℝ)/4),
          hillLocalGapPolynomial 0 zero_parity zero_real (k : ℕ) (Coeff.periodDouble u) E •
              deriv (fun z => H k (z,u)) E +
            (E-hillLocalGapMidpoint 0 zero_parity zero_real (k : ℕ) (Coeff.periodDouble u)) • H k (E,u) =
              hillNativeRegularGapNumerator zero_parity zero_real G k (E,u)) ∧
        ∀ u ∈ ball (0 : Coeff 2) η, ∀ E ∈ closedBall (freeHillEnergy k) ((k : ℝ)/4),
          ‖H k (E,u)‖ ≤ 18*Real.pi*M/(k : ℝ)) ∧
      ∀ p : RealHillWeightedPotential SpectralWeight.one,
        SpectralWeight.one.doubleIndex.toCoeff p.val ∈ ball (0 : Coeff 2) η →
        let q := hillRealWeightedEmbedding SpectralWeight.one p
        let u := SpectralWeight.one.doubleIndex.toCoeff p.val
        (∀ n : ℕ+, ∀ E : ℂ, G (E,u) (n : ℤ)=
          hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 (n : ℕ) n.property E) ∧
        ∀ k : ℕ+, N ≤ (k : ℕ) → ∀ n : ℕ+, ∀ E ∈ closedBall (freeHillEnergy k) (k : ℝ),
          hillNativeRegularGapNumerator zero_parity zero_real G k (E,u) (n : ℤ)=
            (-I)*hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 (n : ℕ) n.property E /
              hillDeflatedEnergyCanonicalRoot q.val q.property.1 q.property.2 (k : ℕ) E - (if k=n then 1 else 0) := by
  obtain ⟨ρ,G,Ng,M,hρ,hNg,hM,hGa,_,hreg,hphysical⟩ :=
    exists_hillPhysical_native_regular_gap_numerators
  let η := min ρ (1/2)
  have hη : 0 < η := lt_min hρ (by norm_num)
  have hsub : ball (0 : Coeff 2) η ⊆ ball (0 : Coeff 2) ρ := ball_subset_ball (min_le_left _ _)
  have hsource (u : Coeff 2) (hu : u ∈ ball 0 η) : Coeff.periodDouble u ∈ ball (0 : Coeff 2) 1 := by
    rw [mem_ball_zero_iff,Coeff.norm_periodDouble]
    exact (mem_ball_zero_iff.mp hu).trans_le ((min_le_right ρ (1/2)).trans (by norm_num))
  obtain ⟨Nq,_,hsol⟩ := exists_hillRadius_native_quadratic_solutions zero_parity zero_real η 1 hsource
  let N := max Ng Nq
  have hex (k : ℕ+) : ∃ Hk : ℂ × Coeff 2 → Coeff 2, N ≤ (k : ℕ) →
      AnalyticOnNhd ℂ Hk
        (ball (freeHillEnergy k) (3*(k : ℝ)/4) ×ˢ ball (0 : Coeff 2) η) ∧
      (∀ u ∈ ball (0 : Coeff 2) η, ∀ E ∈ ball (freeHillEnergy k) (3*(k : ℝ)/4),
        hillLocalGapPolynomial 0 zero_parity zero_real (k : ℕ) (Coeff.periodDouble u) E •
            deriv (fun z => Hk (z,u)) E +
          (E-hillLocalGapMidpoint 0 zero_parity zero_real (k : ℕ) (Coeff.periodDouble u)) • Hk (E,u) =
            hillNativeRegularGapNumerator zero_parity zero_real G k (E,u)) ∧
      ∀ u ∈ ball (0 : Coeff 2) η, ∀ E ∈ closedBall (freeHillEnergy k) ((k : ℝ)/4),
        ‖Hk (E,u)‖ ≤ 18*Real.pi*M/(k : ℝ) := by
    by_cases hk : N ≤ (k : ℕ)
    · have hg := hreg k ((le_max_left Ng Nq).trans hk)
      obtain ⟨Hk,hHk⟩ := hsol k ((le_max_right Ng Nq).trans hk)
        (hillNativeRegularGapNumerator zero_parity zero_real G k) M hM.le
        (hg.1.mono (prod_mono Subset.rfl hsub))
        (fun u hu => (hg.2 u (hsub hu)).1)
        (fun u hu => (hg.2 u (hsub hu)).2.2.2)
      exact ⟨Hk,fun _ => hHk⟩
    · exact ⟨0,fun h => (hk h).elim⟩
  choose H hH using hex
  refine ⟨η,G,H,N,M,hη,hNg.trans (le_max_left _ _),hM,
    hGa.mono (prod_mono Subset.rfl hsub),hH,?_⟩
  intro p hp
  have hphys := hphysical p (hsub hp)
  exact ⟨hphys.1,fun k hk => hphys.2 k ((le_max_left Ng Nq).trans hk)⟩

end NLS.Articles.KdVKdV2Frequencies
