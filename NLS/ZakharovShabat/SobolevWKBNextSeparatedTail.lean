import NLS.ZakharovShabat.SobolevWKBNextSeparatedCorrection
import NLS.ZakharovShabat.SobolevWKBBothCorrectedDiagonalTails
import NLS.ZakharovShabat.SobolevWKBBothOffDiagonalTails
import NLS.SequenceSpaces.WeightedDomination

/-! # The actual separated next-phase remainder

The exact next-phase identity assembles an H^(s+1) tail from corrected diagonals, off-diagonals, and the scalar correction.
-/

noncomputable section
open Set Complex NLS.Fourier NLS.LinearVolterra
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat
open BoundaryCondition

/-- The separated characteristic at the next Hamiltonian phase has an
H^(s+1) remainder after subtracting its two exact leading integrals.
The estimate is uniform on original Hs balls, for bounded spectral shifts,
both boundary conditions, and every larger cutoff. -/
theorem exists_uniform_nlsWKB_next_separated_fourier_tail_bound_of_bounded_displacement
    (s : ℕ) (hs : 1 ≤ s) (R D : ℝ) (hR : 0 ≤ R) (hD : 0 ≤ D) :
    ∃ K : ℕ, 0 < K ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ K' : ℕ, K ≤ K' → ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ∀ ha : ContDiff ℝ ∞ a, ∀ hb : ContDiff ℝ ∞ b,
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ δ : NLS.Coeff ⊤, ‖δ‖ ≤ D → ∀ θ : BoundaryCondition,
      ∃ f : ScalarSobolev (s+1),
        (∀ n, f.val n = if K' ≤ n.natAbs then
          let z := (Real.pi:ℂ)*n+δ n
          let p := nlsWKBInitialLower a b s z
          let q := nlsWKBInitialUpper a b s z
          let η := extensionSign θ
          2*I*(1-p*q)*classicalSeparatedCharacteristic θ
            (classicalPotentialOfFunctions a b ha.continuous hb.continuous) z+
            2*(1+p*q-η*(p+q))*sinh (nlsHamiltonianPhase a b (s+1) z)-
            (q-η)*nlsWKBLeadingTerm a b s z 1-(η-p)*nlsWKBLeadingTerm (-b) (-a) s (-z) 1
          else 0) ∧ ‖f‖ ≤ C := by
  classical
  obtain ⟨K₁,hK₁,C₁,hC₁,hdiag⟩ := exists_uniform_nlsWKB_both_corrected_diagonal_tail_bound_of_bounded_displacement s s hs le_rfl R D hR hD
  obtain ⟨K₂,_,C₂,hC₂,hoff⟩ := exists_uniform_nlsWKB_both_offDiagonal_tail_bound_of_bounded_displacement s s hs le_rfl R D hR hD
  obtain ⟨K₃,_,C₃,hC₃,hcorr⟩ := exists_uniform_nlsWKB_next_separated_correction_fourier_tail_bound_of_bounded_displacement s s hs le_rfl R D hR hD
  obtain ⟨K₄,_,hgeom⟩ := exists_wkb_bounded_frequency_cutoff D hD
  obtain ⟨T,_,hbasis⟩ := exists_uniform_nlsWKB_initial_basis_bounds s s le_rfl R hR
  obtain ⟨L,hL⟩ := exists_nat_ge T
  let K := max K₁ (max K₂ (max K₃ (max K₄ L)))
  refine ⟨K,hK₁.trans_le (le_max_left _ _),4*C₁+4*C₂+C₃,by positivity,?_⟩
  intro K' hKK' ab hab a b ha hb hpa hpb hca hcb δ hδD θ
  have hKs : K₁ ≤ K' ∧ K₂ ≤ K' ∧ K₃ ≤ K' ∧ K₄ ≤ K' ∧ L ≤ K' := by
    dsimp only [K] at hKK'
    omega
  obtain ⟨d₁,d₂,hd₁,hd₂,hd₁n,hd₂n⟩ := hdiag K' hKs.1 ab hab a b ha hb hpa hpb hca hcb δ hδD 1
  obtain ⟨o₁,o₂,ho₁,ho₂,ho₁n,ho₂n⟩ := hoff ab hab a b ha hb hpa hpb hca hcb δ hδD 1
  obtain ⟨c,hc,hcn⟩ := hcorr K' hKs.2.2.1 ab hab a b ha hb hpa hpb hca hcb δ hδD θ
  let ν (n : ℤ) := (Real.pi:ℂ)*n+δ n
  let p (n : ℤ) := nlsWKBInitialLower a b s (ν n)
  let q (n : ℤ) := nlsWKBInitialUpper a b s (ν n)
  let η := extensionSign θ
  have hη : ‖η‖ = 1 := by cases θ <;> norm_num [η,extensionSign]
  have hbase (n : ℤ) (hn : K' ≤ n.natAbs) :
      ‖p n‖ ≤ 1 ∧ ‖q n‖ ≤ 1 ∧ 1-p n*q n ≠ 0 := by
    have hδ (j : ℤ) : ‖δ j‖ ≤ D := (lp.norm_apply_le_norm (by simp) δ j).trans hδD
    have hz := (hgeom δ hδ n (hKs.2.2.2.1.trans hn)).2
    have hnL : (L:ℝ) ≤ (n.natAbs:ℝ) := by exact_mod_cast hKs.2.2.2.2.trans hn
    have hT : T ≤ ‖ν n‖ := by
      change 1+|(n:ℝ)| ≤ ‖ν n‖ at hz
      have habs : |(n:ℝ)| = (n.natAbs:ℝ) := by simp
      rw [habs] at hz
      linarith
    have h := hbasis ab hab a b ha hb hpa hpb hca hcb (ν n) hT
    exact ⟨h.1.trans (by norm_num),h.2.1.trans (by norm_num),h.2.2.1⟩
  have hmult (m : ℤ → ℂ) (hm : ∀ n, K' ≤ n.natAbs → ‖m n‖ ≤ 2)
      (v : ScalarSobolev (s+1)) :
      ∃ u : ScalarSobolev (s+1),
        (∀ n, u.val n = if K' ≤ n.natAbs then m n*v.val n else 0) ∧ ‖u‖ ≤ 2*‖v‖ := by
    apply WeightedCoeff.exists_of_norm_le _ v _ 2 (by norm_num)
    intro n
    by_cases hn : K' ≤ n.natAbs
    · simpa only [if_pos hn,norm_mul] using mul_le_mul_of_nonneg_right (hm n hn) (norm_nonneg _)
    · simp only [if_neg hn,norm_zero]
      positivity
  obtain ⟨u₁,hu₁,hu₁n⟩ := hmult (fun n => 1-η*q n) (by
    intro n hn
    have h := norm_sub_le (1:ℂ) (η*q n)
    rw [norm_one,norm_mul,hη,one_mul] at h
    linarith [(hbase n hn).2.1]) d₁
  obtain ⟨u₂,hu₂,hu₂n⟩ := hmult (fun n => 1-η*p n) (by
    intro n hn
    have h := norm_sub_le (1:ℂ) (η*p n)
    rw [norm_one,norm_mul,hη,one_mul] at h
    linarith [(hbase n hn).1]) d₂
  obtain ⟨u₃,hu₃,hu₃n⟩ := hmult (fun n => q n-η) (by
    intro n hn
    have h := norm_sub_le (q n) η
    rw [hη] at h
    linarith [(hbase n hn).2.1]) o₁
  obtain ⟨u₄,hu₄,hu₄n⟩ := hmult (fun n => η-p n) (by
    intro n hn
    have h := norm_sub_le η (p n)
    rw [hη] at h
    linarith [(hbase n hn).1]) o₂
  refine ⟨u₁-u₂+u₃+u₄+c,?_,?_⟩
  · intro n
    simp only [WeightedCoeff.add_val,WeightedCoeff.sub_val,hu₁,hu₂,hu₃,hu₄,hc]
    by_cases hn : K' ≤ n.natAbs
    · simp only [if_pos hn,hd₁,hd₂,ho₁,ho₂,if_pos (hKs.2.1.trans hn)]
      exact (classicalSeparatedCharacteristic_next_wkb_phase_exact θ a b ha hb hpa hpb s
        (ν n) (hbase n hn).2.2).symm
    · simp only [if_neg hn,sub_self,add_zero]
  · have h₁ := norm_sub_le u₁ u₂
    have h₂ := norm_add_le (u₁-u₂) u₃
    have h₃ := norm_add_le (u₁-u₂+u₃) u₄
    have h₄ := norm_add_le (u₁-u₂+u₃+u₄) c
    linarith

end NLS.ZakharovShabat
