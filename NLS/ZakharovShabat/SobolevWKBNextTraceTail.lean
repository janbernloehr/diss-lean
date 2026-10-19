import NLS.ZakharovShabat.SobolevWKBTraceLeadingTails
import NLS.ZakharovShabat.SobolevWKBBothCorrectedDiagonalTails
import NLS.ZakharovShabat.SobolevWKBBothOffDiagonalTails
import NLS.ZakharovShabat.SobolevWKBNextTraceCorrectionTail
import NLS.SequenceSpaces.WeightedMultiplier

/-! # The actual next-phase discriminant tail

The actual discriminant minus the next Hamiltonian trace has a uniformly bounded H^(s+1) tail under bounded inverse-index displacements.
-/

noncomputable section
open Set Complex NLS.Fourier NLS.LinearVolterra
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- The actual discriminant differs from the next Hamiltonian trace by
an H^(s+1) tail uniformly on original Hs balls, at every larger cutoff.
The sampled displacement retains its inverse-index bound. -/
theorem exists_uniform_nlsWKB_next_trace_fourier_tail_bound
    (s : ℕ) (hs : 1 ≤ s) (R D M : ℝ) (hR : 0 ≤ R) (hD : 0 ≤ D) (hM : 0 ≤ M) :
    ∃ K : ℕ, 0 < K ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ K' : ℕ, K ≤ K' → ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ∀ ha : ContDiff ℝ ∞ a, ∀ hb : ContDiff ℝ ∞ b,
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ δ : NLS.Coeff ⊤, ‖δ‖ ≤ D →
      (∀ n : ℤ, (1+|(n:ℝ)|)*‖δ n‖ ≤ M) →
      ∃ f : ScalarSobolev (s+1),
        (∀ n, f.val n = if K' ≤ n.natAbs then
          let z := (Real.pi:ℂ)*n+δ n
          classicalDiscriminant (classicalPotentialOfFunctions a b ha.continuous hb.continuous) z-
            2*cos (I*nlsHamiltonianPhase a b (s+1) z)
          else 0) ∧ ‖f‖ ≤ C := by
  classical
  obtain ⟨K₀,hK₀,C₀,hC₀,hlead⟩ := exists_uniform_nlsWKB_trace_leading_fourier_tail_bound s R D M hR hD hM
  obtain ⟨K₁,_,C₁,hC₁,hdiag⟩ := exists_uniform_nlsWKB_both_corrected_diagonal_tail_bound s s hs le_rfl R D M hR hD
  obtain ⟨K₂,_,C₂,hC₂,hoff⟩ := exists_uniform_nlsWKB_both_offDiagonal_tail_bound s s hs le_rfl R D M hR hD
  obtain ⟨K₃,_,C₃,hC₃,hcorr⟩ := exists_uniform_nlsWKB_next_trace_correction_fourier_tail_bound s s hs le_rfl R D M hR hD
  obtain ⟨K₄,_,hgeom⟩ := exists_wkb_leading_frequency_cutoff D M hD
  obtain ⟨T,_,hbasis⟩ := exists_uniform_nlsWKB_initial_basis_bounds s s le_rfl R hR
  obtain ⟨L,hL⟩ := exists_nat_ge T
  let K := max K₀ (max K₁ (max K₂ (max K₃ (max K₄ L))))
  refine ⟨K,hK₀.trans_le (le_max_left _ _),2*(C₀+C₀+C₂+C₂+C₁+C₁+C₃),by positivity,?_⟩
  intro K' hKK' ab hab a b ha hb hpa hpb hca hcb δ hδD hδM
  have hKs : K₀ ≤ K' ∧ K₁ ≤ K' ∧ K₂ ≤ K' ∧ K₃ ≤ K' ∧ K₄ ≤ K' ∧ L ≤ K' := by
    dsimp only [K] at hKK'
    omega
  obtain ⟨l₁,l₂,hl₁,hl₂,hl₁n,hl₂n⟩ := hlead K' hKs.1 ab hab a b ha hb hpa hpb hca hcb δ hδD hδM
  obtain ⟨d₁,d₂,hd₁,hd₂,hd₁n,hd₂n⟩ := hdiag K' hKs.2.1 ab hab a b ha hb hpa hpb hca hcb δ hδD hδM 1
  obtain ⟨o₁,o₂,ho₁,ho₂,ho₁n,ho₂n⟩ := hoff ab hab a b ha hb hpa hpb hca hcb δ hδD hδM 1
  obtain ⟨c,hc,hcn⟩ := hcorr K' hKs.2.2.2.1 ab hab a b ha hb hpa hpb hca hcb δ hδD hδM
  let ν (n : ℤ) := (Real.pi:ℂ)*n+δ n
  let p (n : ℤ) := nlsWKBInitialLower a b s (ν n)
  let q (n : ℤ) := nlsWKBInitialUpper a b s (ν n)
  let d (n : ℤ) := 1-p n*q n
  have hbase (n : ℤ) (hn : K' ≤ n.natAbs) :
      ‖p n‖ ≤ 1 ∧ ‖q n‖ ≤ 1 ∧ d n ≠ 0 ∧ ‖(d n)⁻¹‖ ≤ 2 := by
    have hδ (j : ℤ) : ‖δ j‖ ≤ D := (lp.norm_apply_le_norm (by simp) δ j).trans hδD
    have hz := (hgeom δ hδ hδM n (hKs.2.2.2.2.1.trans hn)).2
    have hnL : (L:ℝ) ≤ (n.natAbs:ℝ) := by exact_mod_cast hKs.2.2.2.2.2.trans hn
    have hT : T ≤ ‖ν n‖ := by
      change 1+|(n:ℝ)| ≤ ‖ν n‖ at hz
      have habs : |(n:ℝ)| = (n.natAbs:ℝ) := by simp
      rw [habs] at hz
      linarith
    have h := hbasis ab hab a b ha hb hpa hpb hca hcb (ν n) hT
    exact ⟨h.1.trans (by norm_num),h.2.1.trans (by norm_num),h.2.2⟩
  let v := Weight.sobolev ((s+1:ℕ):ℝ)
  let mp (n : ℤ) : ℂ := if K' ≤ n.natAbs then p n else 0
  let mq (n : ℤ) : ℂ := if K' ≤ n.natAbs then q n else 0
  have hmp (n : ℤ) : v n*‖mp n‖ ≤ 1*v n := by
    by_cases hn : K' ≤ n.natAbs
    · simpa only [mp,if_pos hn,mul_comm] using
        mul_le_mul_of_nonneg_left (hbase n hn).1 (v.positive n).le
    · simp [mp,hn,(v.positive n).le]
  have hmq (n : ℤ) : v n*‖mq n‖ ≤ 1*v n := by
    by_cases hn : K' ≤ n.natAbs
    · simpa only [mq,if_pos hn,mul_comm] using
        mul_le_mul_of_nonneg_left (hbase n hn).2.1 (v.positive n).le
    · simp [mq,hn,(v.positive n).le]
  let fp := WeightedCoeff.weightedMultiplier v v mp 1 hmp o₂
  let fq := WeightedCoeff.weightedMultiplier v v mq 1 hmq o₁
  have hfp : ‖fp‖ ≤ C₂ := by
    exact (WeightedCoeff.norm_weightedMultiplier_le v v mp 1 zero_le_one hmp o₂).trans (by simpa using ho₂n)
  have hfq : ‖fq‖ ≤ C₂ := by
    exact (WeightedCoeff.norm_weightedMultiplier_le v v mq 1 zero_le_one hmq o₁).trans (by simpa using ho₁n)
  let u := l₂+l₁+fp+fq-d₁-d₂+c
  have hu : ‖u‖ ≤ C₀+C₀+C₂+C₂+C₁+C₁+C₃ := by
    have h1 := norm_add_le l₂ l₁
    have h2 := norm_add_le (l₂+l₁) fp
    have h3 := norm_add_le (l₂+l₁+fp) fq
    have h4 := norm_sub_le (l₂+l₁+fp+fq) d₁
    have h5 := norm_sub_le (l₂+l₁+fp+fq-d₁) d₂
    have h6 := norm_add_le (l₂+l₁+fp+fq-d₁-d₂) c
    dsimp only [u]
    linarith
  let m (n : ℤ) : ℂ := if K' ≤ n.natAbs then (d n)⁻¹ else 0
  have hm (n : ℤ) : v n*‖m n‖ ≤ 2*v n := by
    by_cases hn : K' ≤ n.natAbs
    · simpa only [m,if_pos hn,mul_comm] using
        mul_le_mul_of_nonneg_left (hbase n hn).2.2.2 (v.positive n).le
    · simp only [m,if_neg hn,norm_zero,mul_zero]
      exact mul_nonneg (by norm_num) (v.positive n).le
  refine ⟨WeightedCoeff.weightedMultiplier v v m 2 hm u,?_,
    (WeightedCoeff.norm_weightedMultiplier_le v v m 2 (by norm_num) hm u).trans
      (mul_le_mul_of_nonneg_left hu (by norm_num))⟩
  intro n
  change m n*u.val n = _
  dsimp only [u]
  simp only [WeightedCoeff.add_val,WeightedCoeff.sub_val]
  change m n*(l₂.val n+l₁.val n+mp n*o₂.val n+mq n*o₁.val n-d₁.val n-d₂.val n+c.val n) = _
  rw [hl₂ n,hl₁ n,ho₂ n,ho₁ n,hd₁ n,hd₂ n,hc n]
  by_cases hn : K' ≤ n.natAbs
  · simp only [m,mp,mq,if_pos hn,if_pos (hKs.2.2.1.trans hn)]
    have he := classicalDiscriminant_sub_next_wkb_phase_exact a b ha hb hpa hpb s (ν n) (hbase n hn).2.2.1
    dsimp only at he
    calc
      _ = (d n)⁻¹*(d n*(classicalDiscriminant
          (classicalPotentialOfFunctions a b ha.continuous hb.continuous) (ν n)-
          2*cos (I*nlsHamiltonianPhase a b (s+1) (ν n)))) :=
        (congrArg (fun x : ℂ => (d n)⁻¹*x) he).symm
      _ = _ := by rw [← mul_assoc,inv_mul_cancel₀ (hbase n hn).2.2.1,one_mul]
  · simp [m,hn]

end NLS.ZakharovShabat
