import NLS.KdV.HillLocalDirichletChart
import NLS.KdV.HillLocalFreeGapPairs
import NLS.KdV.HillLocalizedComplexGapPairs
import NLS.ComplexAnalysis.FiniteHeadUniformTail

/-! # One source ball for all scaled Dirichlet charts and periodic clusters -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillScaledDirichletRoot_all_analytic_chart
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∀ k : ℕ+,
      AnalyticOnNhd ℂ (hillScaledDirichletRoot h0q h0r ρ (k : ℕ)) (ball (0 : Coeff 2) η) ∧
      ∀ p ∈ ball (0 : Coeff 2) η,
        hillScaledDirichletRoot h0q h0r ρ (k : ℕ) p ∈ ball (hillRealGapCenter 0 h0q h0r (k : ℕ) : ℂ)
          (ρ*(hillRealGapHalfLength 0 h0q h0r (k : ℕ)+hillRealGapCollar 0 h0q h0r (k : ℕ))) ∧
        hillL2DirichletCharacteristic p (hillScaledDirichletRoot h0q h0r ρ (k : ℕ) p) = 0 ∧
        analyticOrderAt (hillL2DirichletCharacteristic p) (hillScaledDirichletRoot h0q h0r ρ (k : ℕ) p) = 1 ∧
        ∀ E ∈ closedBall (hillRealGapCenter 0 h0q h0r (k : ℕ) : ℂ)
          (ρ*(hillRealGapHalfLength 0 h0q h0r (k : ℕ)+hillRealGapCollar 0 h0q h0r (k : ℕ))),
          hillL2DirichletCharacteristic p E = 0 ↔ E = hillScaledDirichletRoot h0q h0r ρ (k : ℕ) p := by
  let P := fun (k : ℕ+) (p : Coeff 2) =>
    AnalyticAt ℂ (hillScaledDirichletRoot h0q h0r ρ (k : ℕ)) p ∧
    hillScaledDirichletRoot h0q h0r ρ (k : ℕ) p ∈ ball (hillRealGapCenter 0 h0q h0r (k : ℕ) : ℂ)
      (ρ*(hillRealGapHalfLength 0 h0q h0r (k : ℕ)+hillRealGapCollar 0 h0q h0r (k : ℕ))) ∧
    hillL2DirichletCharacteristic p (hillScaledDirichletRoot h0q h0r ρ (k : ℕ) p) = 0 ∧
    analyticOrderAt (hillL2DirichletCharacteristic p) (hillScaledDirichletRoot h0q h0r ρ (k : ℕ) p) = 1 ∧
    ∀ E ∈ closedBall (hillRealGapCenter 0 h0q h0r (k : ℕ) : ℂ)
      (ρ*(hillRealGapHalfLength 0 h0q h0r (k : ℕ)+hillRealGapCollar 0 h0q h0r (k : ℕ))),
      hillL2DirichletCharacteristic p E = 0 ↔ E = hillScaledDirichletRoot h0q h0r ρ (k : ℕ) p
  have hlocal (k : ℕ+) : ∀ᶠ p in 𝓝 (0 : Coeff 2), P k p := by
    obtain ⟨V,hV,h0V,ha,hd⟩ := exists_hillScaledDirichletRoot_local_analytic_chart h0q h0r (k : ℕ) k.property ρ hρ hρ1
    filter_upwards [hV.mem_nhds h0V] with p hp
    exact ⟨ha p hp,hd p hp⟩
  obtain ⟨N,_,hchart⟩ := exists_hillScaledDirichletRoot_bounded_complex_analytic_chart h0q h0r ρ hρ hρ1 1
  have htail (k : ℕ+) (hk : N ≤ (k : ℕ)) (p : Coeff 2) (hp : p ∈ ball 0 1) : P k p :=
    ⟨(hchart (k : ℕ) hk).1 p hp,(hchart (k : ℕ) hk).2 p (mem_ball_zero_iff.mp hp).le⟩
  obtain ⟨η,hη,hη1,hd⟩ := exists_ball_forall_pos_index_of_local_and_uniform_tail P (0 : Coeff 2) hlocal N 1 (by norm_num) htail
  exact ⟨η,hη,hη1,fun k => ⟨fun p hp => (hd k p hp).1,fun p hp => (hd k p hp).2⟩⟩

theorem exists_hillFreeGap_all_localized_pairs
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∀ k : ℕ+, ∀ p ∈ ball (0 : Coeff 2) η,
      (∀ E ∈ sphere (hillRealGapCenter 0 h0q h0r (k : ℕ) : ℂ)
        (hillRealGapHalfLength 0 h0q h0r (k : ℕ)+hillRealGapCollar 0 h0q h0r (k : ℕ)), hillL2Radicand p E ≠ 0) ∧
      ∃ a ∈ ball (hillRealGapCenter 0 h0q h0r (k : ℕ) : ℂ)
        (ρ*(hillRealGapHalfLength 0 h0q h0r (k : ℕ)+hillRealGapCollar 0 h0q h0r (k : ℕ))),
      ∃ b ∈ ball (hillRealGapCenter 0 h0q h0r (k : ℕ) : ℂ)
        (ρ*(hillRealGapHalfLength 0 h0q h0r (k : ℕ)+hillRealGapCollar 0 h0q h0r (k : ℕ))),
        hillL2Radicand p a = 0 ∧ hillL2Radicand p b = 0 ∧
        ∀ E ∈ closedBall (hillRealGapCenter 0 h0q h0r (k : ℕ) : ℂ)
          (hillRealGapHalfLength 0 h0q h0r (k : ℕ)+hillRealGapCollar 0 h0q h0r (k : ℕ)),
          analyticOrderNatAt (hillL2Radicand p) E = ({a,b} : Multiset ℂ).count E := by
  let P := fun (k : ℕ+) (p : Coeff 2) =>
    (∀ E ∈ sphere (hillRealGapCenter 0 h0q h0r (k : ℕ) : ℂ)
      (hillRealGapHalfLength 0 h0q h0r (k : ℕ)+hillRealGapCollar 0 h0q h0r (k : ℕ)), hillL2Radicand p E ≠ 0) ∧
    ∃ a ∈ ball (hillRealGapCenter 0 h0q h0r (k : ℕ) : ℂ)
      (ρ*(hillRealGapHalfLength 0 h0q h0r (k : ℕ)+hillRealGapCollar 0 h0q h0r (k : ℕ))),
    ∃ b ∈ ball (hillRealGapCenter 0 h0q h0r (k : ℕ) : ℂ)
      (ρ*(hillRealGapHalfLength 0 h0q h0r (k : ℕ)+hillRealGapCollar 0 h0q h0r (k : ℕ))),
      hillL2Radicand p a = 0 ∧ hillL2Radicand p b = 0 ∧
      ∀ E ∈ closedBall (hillRealGapCenter 0 h0q h0r (k : ℕ) : ℂ)
        (hillRealGapHalfLength 0 h0q h0r (k : ℕ)+hillRealGapCollar 0 h0q h0r (k : ℕ)),
        analyticOrderNatAt (hillL2Radicand p) E = ({a,b} : Multiset ℂ).count E
  have hlocal (k : ℕ+) : ∀ᶠ p in 𝓝 (0 : Coeff 2), P k p := by
    obtain ⟨V,hV,h0V,hdata⟩ := exists_hillFreeGap_localized_pairs_neighborhood h0q h0r (k : ℕ) k.property ρ hρ
    filter_upwards [hV.mem_nhds h0V] with p hp
    exact hdata p hp
  obtain ⟨N,_,hdata⟩ := exists_hillFreeGap_bounded_complex_localized_pairs h0q h0r ρ hρ hρ1 1
  exact exists_ball_forall_pos_index_of_local_and_uniform_tail P (0 : Coeff 2) hlocal N 1 (by norm_num)
    (fun k hk p hp => hdata p (mem_ball_zero_iff.mp hp).le (k : ℕ) hk)

end NLS.KdV
