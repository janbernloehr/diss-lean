import NLS.ZakharovShabat.SourceAntiDiscriminantDiscLp
import NLS.ComplexAnalysis.CompactParameterBounds

/-!
# Uniform central source anti-discriminant bounds

Joint analyticity and compactness bound the anti-discriminant on a fixed
spectral ball over one source neighborhood. Cauchy's estimate gives the
same local bound for its spectral derivative on a smaller ball.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem exists_local_uniform_sourceAntiDiscriminant_on_ball
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (R : ℝ) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ ψ ∈ U, ∀ z : ℂ, ‖z‖ ≤ R →
        ‖sourceAntiDiscriminantCandidate hp hp1 ψ z‖ ≤ B ∧
          ‖deriv (sourceAntiDiscriminantCandidate hp hp1 ψ) z‖ ≤ B := by
  have hf : Continuous (fun t : ℂ × CoeffPair p =>
      sourceAntiDiscriminantCandidate hp hp1 t.2 t.1) :=
    continuousOn_univ.mp (analyticOnNhd_sourceAntiDiscriminantCandidate_joint hp hp1).continuousOn
  obtain ⟨U, hUo, hUφ, B, hB, hb⟩ :=
    NLS.ComplexAnalysis.exists_local_uniform_bound_on_compact _ hf
      (closedBall (0 : ℂ) (R+1)) (isCompact_closedBall _ _) φ
  refine ⟨U, hUo, hUφ, B, hB, fun ψ hψ z hz => ⟨?_, ?_⟩⟩
  · exact hb ψ hψ z (by simpa only [mem_closedBall, dist_zero_right] using
      (show ‖z‖ ≤ R+1 by linarith))
  · have han : Differentiable ℂ (sourceAntiDiscriminantCandidate hp hp1 ψ) := by
      intro w
      exact (analyticOnNhd_sourceAntiDiscriminantCandidate hp hp1 ψ w (mem_univ _)).differentiableAt
    have hd := NLS.ComplexAnalysis.norm_deriv_le_of_closedDisc_bound han z
      (by norm_num : (0 : ℝ) < 1) B (by
        intro w hw
        apply hb ψ hψ w
        have ht : ‖w‖ ≤ ‖w-z‖+‖z‖ := by
          simpa only [sub_zero] using norm_sub_le_norm_sub_add_norm_sub w z 0
        simpa only [mem_closedBall, dist_zero_right] using
          (ht.trans (by linarith))) (by simp : ‖z-z‖ ≤ (0 : ℝ))
    simpa using hd

/-- Lemma 9.2(iii): the anti-discriminant and its spectral derivative,
sampled at every canonical ordinary Dirichlet root, have locally uniformly
bounded ℓᵖ norms on the original source coefficient space. -/
theorem exists_local_uniform_sampled_sourceAntiDiscriminant_at_dirichletRoots
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∀ ψ ∈ U,
        ∃ a b : Coeff p, ‖a‖ ≤ K ∧ ‖b‖ ≤ K ∧
          (∀ n, a n = sourceAntiDiscriminantCandidate hp hp1 ψ
            (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n)) ∧
          (∀ n, b n = deriv (sourceAntiDiscriminantCandidate hp hp1 ψ)
            (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n)) := by
  let F := periodOneBoundaryPotential hp hp1
  obtain ⟨Nt, Ut, hUto, _, hUtφ, _, Kt, hKt, htail⟩ :=
    exists_uniform_sourceAntiDiscriminant_at_dirichlet_tail hp hp1 φ
  obtain ⟨Nr, _, Vr, hVro, _, hVrφ, _, _, _, hroots⟩ :=
    exists_uniform_canonicalBoundaryRoots_all_cutoffs hp hp1 (F φ)
  let N := max Nt Nr
  let s := Finset.Icc (-(N : ℤ)) N
  obtain ⟨C, hC, hbox⟩ := (isBounded_centralSpectralBox N).exists_pos_norm_le
  obtain ⟨Uc, hUco, hUcφ, B, hB, hcentral⟩ :=
    exists_local_uniform_sourceAntiDiscriminant_on_ball hp hp1 φ C
  let U := (Ut ∩ (F ⁻¹' Vr)) ∩ Uc
  let K := s.card*B+Kt+(4/Real.pi)*Kt
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨U, (hUto.inter (hVro.preimage F.continuous)).inter hUco,
    ⟨⟨hUtφ,hVrφ⟩,hUcφ⟩, K, hK, fun ψ hψ => ?_⟩
  obtain ⟨A, hA, htailψ⟩ := htail ψ hψ.1.1
  let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ
  let a : Coeff p := ⟨_, (memℓp_sourceAntiDiscriminant_at_dirichletRoots hp hp1 ψ).1⟩
  let b : Coeff p := ⟨_, (memℓp_sourceAntiDiscriminant_at_dirichletRoots hp hp1 ψ).2⟩
  have hcenter (n : ℤ) (hn : n ∈ s) : ‖a n‖ ≤ B ∧ ‖b n‖ ≤ B := by
    have hnN : n.natAbs ≤ N := by simp only [s, Finset.mem_Icc] at hn; omega
    have hlabel := (hroots (F ψ) hψ.1.2 .dirichlet).1 N (le_max_right Nt Nr)
    have hμ : ‖μ n‖ ≤ C := hbox _ (hlabel.central_mem n hnN)
    exact hcentral ψ hψ.2 (μ n) hμ
  have htaila : ‖a-Coeff.truncate s a‖ ≤ ‖A‖ := by
    apply lp.norm_mono (zero_lt_one.trans hp1).ne'
    intro n
    by_cases hn : n ∈ s
    · simp [Coeff.truncate_apply, hn]
    · have hnN : N < n.natAbs := by simp only [s, Finset.mem_Icc] at hn; omega
      have htn : Nt < n.natAbs := (le_max_left Nt Nr).trans_lt hnN
      simpa only [lp.coeFn_sub, Pi.sub_apply, Coeff.truncate_apply, if_neg hn, sub_zero]
        using (htailψ n htn).1
  let D : Coeff p := ((4/Real.pi : ℝ) : ℂ) • A
  have htailb : ‖b-Coeff.truncate s b‖ ≤ ‖D‖ := by
    apply lp.norm_mono (zero_lt_one.trans hp1).ne'
    intro n
    by_cases hn : n ∈ s
    · simp [Coeff.truncate_apply, hn]
    · have hnN : N < n.natAbs := by simp only [s, Finset.mem_Icc] at hn; omega
      have htn : Nt < n.natAbs := (le_max_left Nt Nr).trans_lt hnN
      have hd := (htailψ n htn).2
      simpa only [lp.coeFn_sub, Pi.sub_apply, Coeff.truncate_apply, if_neg hn,
        sub_zero, D, lp.coeFn_smul, Pi.smul_apply, norm_smul, Complex.norm_real,
        Real.norm_of_nonneg (by positivity : 0 ≤ 4/Real.pi)] using hd
  have ha : ‖a‖ ≤ K := by
    calc
      ‖a‖ ≤ s.card*B+‖a-Coeff.truncate s a‖ :=
        Coeff.norm_le_of_eq_outside_finset a (a-Coeff.truncate s a) s B
          (fun n hn => (hcenter n hn).1) (by
            intro n hn
            simp [Coeff.truncate_apply, hn])
      _ ≤ s.card*B+‖A‖ := add_le_add le_rfl htaila
      _ ≤ s.card*B+Kt := add_le_add le_rfl hA
      _ ≤ K := by
        dsimp [K]
        have hcoef : 0 ≤ 4/Real.pi := by positivity
        nlinarith [mul_nonneg hcoef hKt]
  have hb : ‖b‖ ≤ K := by
    calc
      ‖b‖ ≤ s.card*B+‖b-Coeff.truncate s b‖ :=
        Coeff.norm_le_of_eq_outside_finset b (b-Coeff.truncate s b) s B
          (fun n hn => (hcenter n hn).2) (by
            intro n hn
            simp [Coeff.truncate_apply, hn])
      _ ≤ s.card*B+‖D‖ := add_le_add le_rfl htailb
      _ ≤ s.card*B+(4/Real.pi)*Kt := by
        change s.card*B+‖((4/Real.pi : ℝ) : ℂ) • A‖ ≤ s.card*B+(4/Real.pi)*Kt
        rw [norm_smul, Complex.norm_real,
          Real.norm_of_nonneg (by positivity : 0 ≤ 4/Real.pi)]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hA (by positivity))
      _ ≤ K := by
        dsimp [K]
        have hcard : 0 ≤ (s.card : ℝ)*B := mul_nonneg (Nat.cast_nonneg _) hB
        linarith
  exact ⟨a, b, ha, hb, fun _ => rfl, fun _ => rfl⟩

end NLS.ZakharovShabat
