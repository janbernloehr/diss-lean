import NLS.KdV.HillPeriodJacobianUniformJointLipschitz
import NLS.KdV.HillPeriodJacobianUniformInverse
import NLS.KdV.HillCommonZeroSequenceStability
import NLS.SequenceSpaces.NearbyInverse

/-! ONE complex data/source radius and ONE FULL inverse norm bound
work BEFORE ALL Hill numerator indices. The actual real inverse is
perturbed in FULL operator norm; no complex invertibility is assumed. -/
noncomputable section
open Set Metric Complex
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem exists_uniform_complex_sequenceJacobian_inverse_balls (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ δ M : ℝ, 0 < δ ∧ 0 ≤ M ∧ ∀ n : ℕ+,
      ∀ t ∈ ball (hillHminusPsiZeroDisplacement n ⟨q,hr⟩,q) δ,
        t ∈ P.inputDomain ∧
        ∃ R : lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2,
          (P.sequenceJacobian n t).comp R = ContinuousLinearMap.id ℂ _ ∧
          R.comp (P.sequenceJacobian n t) = ContinuousLinearMap.id ℂ _ ∧ ‖R‖ ≤ M := by
  obtain ⟨r,C,hrpos,hC,hcharts⟩ := P.exists_uniform_joint_sequenceJacobian_Lipschitz q hq hr
  obtain ⟨M₀,hM₀,hinv⟩ := P.exists_actual_real_uniform_sequenceJacobian_inverse q hq hr
  let ε := 1/(2*(M₀+1)*(C+1))
  let δ := min r ε
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hδ : 0 < δ := lt_min hrpos hε
  have hδr : δ ≤ r := min_le_left _ _
  have hδε : δ ≤ ε := min_le_right _ _
  refine ⟨δ,2*M₀,hδ,by positivity,?_⟩
  intro n t ht
  let d := hillHminusPsiZeroDisplacement n ⟨q,hr⟩
  have hd := actual_hill_zero_sequence_mem_energyGapData ⟨q,hr⟩ n
  have htr : t ∈ ball (d,q) r := ball_subset_ball hδr ht
  have htdist : ‖t-(d,q)‖ ≤ δ := by simpa only [mem_ball,dist_eq_norm] using (mem_ball.mp ht).le
  obtain ⟨S,hJS,hSJ,hS⟩ := hinv n
  have hdiff : ‖P.sequenceJacobian n (d,q)-P.sequenceJacobian n t‖ ≤ C*δ := by
    have h := (hcharts d hd).2 n t htr (d,q) (mem_ball_self hrpos)
    rw [norm_sub_rev] at h
    exact h.trans (mul_le_mul_of_nonneg_left htdist hC)
  have hnear : ‖S‖*‖P.sequenceJacobian n (d,q)-P.sequenceJacobian n t‖ ≤ (1/2:ℝ) := by
    calc
      _ ≤ M₀*(C*δ) := mul_le_mul hS hdiff (norm_nonneg _) hM₀
      _ ≤ (M₀+1)*((C+1)*ε) := by gcongr <;> linarith
      _ = 1/2 := by dsimp only [ε]; field_simp
  obtain ⟨R,hJR,hRJ,hR⟩ := NLS.exists_inverse_norm_le_two_mul_of_near
    (P.sequenceJacobian n t) (P.sequenceJacobian n (d,q)) S hJS hSJ hnear
  exact ⟨(hcharts d hd).1 htr,R,hJR,hRJ,hR.trans (mul_le_mul_of_nonneg_left hS (by norm_num))⟩

theorem exists_common_complex_source_sequenceJacobian_inverse (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ r M : ℝ, 0 < r ∧ 0 ≤ M ∧ ball q r ⊆ hillHminusCanonicalZeroSequenceDomain ∧
      ∀ y ∈ ball q r, ∀ n : ℕ+,
        (hillHminusCanonicalZeroSequence n y,y) ∈ P.inputDomain ∧
        ∃ R : lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2,
          (P.sequenceJacobian n (hillHminusCanonicalZeroSequence n y,y)).comp R = ContinuousLinearMap.id ℂ _ ∧
          R.comp (P.sequenceJacobian n (hillHminusCanonicalZeroSequence n y,y)) = ContinuousLinearMap.id ℂ _ ∧
          ‖R‖ ≤ M := by
  obtain ⟨δ,M,hδ,hM,hinv⟩ := P.exists_uniform_complex_sequenceJacobian_inverse_balls q hq hr
  obtain ⟨r,hrpos,hU,hgraph⟩ := exists_common_canonical_zero_sequence_graph_radius q hr δ hδ
  exact ⟨r,M,hrpos,hM,hU,fun y hy n => hinv n _ (hgraph y hy n)⟩

end NLS.KdV.HillProductEquationPatch
