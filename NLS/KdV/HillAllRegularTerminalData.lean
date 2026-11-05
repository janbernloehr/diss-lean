import NLS.KdV.HillLocalRegularTerminalData
import NLS.KdV.HillNativeTerminalPhysical
import NLS.ComplexAnalysis.FiniteHeadUniformTail
import NLS.SequenceSpaces.UnitSpectralWeightNorm

/-! # One physical source neighborhood for all regular terminal sheets -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillRegularTerminalPhysicalData_all :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ k : ℕ+, ∀ q : RealPeriodOneHillPotential,
      ‖SpectralWeight.one.toCoeff q.val‖ < ε → HillRegularTerminalPhysicalData h0q h0r k q := by
  let q0 : RealPeriodOneHillPotential := ⟨0,h0q,h0r⟩
  let P := fun k q => HillRegularTerminalPhysicalData h0q h0r k q
  have hlocal (k : ℕ+) : ∀ᶠ q in 𝓝 q0, P k q := eventually_hillRegularTerminalPhysicalData h0q h0r k
  obtain ⟨Ns,_,hsymmetric⟩ := exists_hillFreeGap_bounded_real_symmetric_data_matching h0q h0r 1
  obtain ⟨Nl,_,hlocalize⟩ := exists_hillFreeGap_bounded_real_midpoint_halfgap_localization h0q h0r (1/128) (by norm_num) (by norm_num) 1
  obtain ⟨Nm,_,hmumatch⟩ := exists_hillScaledDirichletRoot_bounded_real_physical_matching h0q h0r (1/128) (by norm_num) (by norm_num) 1
  obtain ⟨Nc,_,hmuchart⟩ := exists_hillScaledDirichletRoot_bounded_complex_analytic_chart h0q h0r (1/128) (by norm_num) (by norm_num) 1
  obtain ⟨Nr,_,hroot⟩ := exists_hillFilledFreeGapRoot_bounded_real_physical_matching h0q h0r 1
  let N := Ns+Nl+Nm+Nc+Nr+1
  have htail (k : ℕ+) (hk : N ≤ (k : ℕ)) (q : RealPeriodOneHillPotential) (hq : q ∈ ball q0 1) : P k q := by
    have hqnorm : ‖q.val‖ < 1 := by
      change dist q.val 0 < 1 at hq
      simpa only [dist_eq_norm,sub_zero] using hq
    have hp : ‖SpectralWeight.one.toCoeff q.val‖ ≤ 1 :=
      (SpectralWeight.norm_toCoeff_le SpectralWeight.one q.val).trans hqnorm.le
    have hks : Ns ≤ (k : ℕ) := by dsimp only [N] at hk;omega
    have hkl : Nl ≤ (k : ℕ) := by dsimp only [N] at hk;omega
    have hkm : Nm ≤ (k : ℕ) := by dsimp only [N] at hk;omega
    have hkc : Nc ≤ (k : ℕ) := by dsimp only [N] at hk;omega
    have hkr : Nr ≤ (k : ℕ) := by dsimp only [N] at hk;omega
    obtain ⟨hM,hS⟩ := hsymmetric q.val q.property.1 q.property.2 hp (k : ℕ) hks
    obtain ⟨hτ,hδ⟩ := hlocalize q.val q.property.1 q.property.2 hp (k : ℕ) hkl
    obtain ⟨hc,hRlo,hRhi⟩ := hillFreeGap_energy_radius_geometry h0q h0r k
    rw [hc] at hτ
    have hm := hmumatch q.val q.property.1 q.property.2 hp (k : ℕ) hkm
    have hμsmall : ‖hillScaledDirichletRoot h0q h0r (1/128) (k : ℕ) (SpectralWeight.one.toCoeff q.val)-freeHillEnergy k‖ < (k : ℝ)/16 := by
      have hh := ((hmuchart (k : ℕ) hkc).2 _ hp).1
      rw [hc,mem_ball_iff_norm] at hh
      linarith
    have hμB : (hillDirichletEnergy q.val q.property.1 q.property.2 (k : ℕ) k.property : ℂ) ∈ ball (freeHillEnergy k) (k : ℝ) := by
      rw [hm] at hμsmall
      exact mem_ball_iff_norm.mpr (by linarith [show (0 : ℝ) < k by positivity])
    refine ⟨(k : ℝ),by positivity,le_rfl,hM,hS,by linarith,by linarith,hm,hμB,?_⟩
    intro E hE
    have hEold : E ∈ closedBall (hillRealGapCenter 0 h0q h0r (k : ℕ) : ℂ)
        (hillRealGapHalfLength 0 h0q h0r (k : ℕ)+hillRealGapCollar 0 h0q h0r (k : ℕ)) := by
      rw [hc]
      exact closedBall_subset_closedBall hRlo (ball_subset_closedBall hE)
    exact hroot q.val q.property.1 q.property.2 hp (k : ℕ) hkr E hEold
  obtain ⟨ε,hε,hε1,hdata⟩ := exists_ball_forall_pos_index_of_local_and_uniform_tail P q0 hlocal N 1 (by norm_num) htail
  refine ⟨ε,hε,hε1,?_⟩
  intro k q hq
  apply hdata k q
  change dist q.val 0 < ε
  rw [dist_eq_norm,sub_zero,← SpectralWeight.norm_toCoeff_one]
  exact hq

end NLS.KdV
