import NLS.KdV.HillHminusOneSourcePrimitive
import NLS.KdV.HillHminusOneDiscAsymptotics
import NLS.ComplexAnalysis.CompactSliceBounds
/-! # Uniform smallness of the actual rough Hill trace near zero

One open complex H^-1 source neighborhood controls every positive frequency
disc, including the finite head. The free trace identity uses evenness of cosine.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV

theorem hillHminusDiscriminant_zero_sq (z : ℂ) :
    hillHminusDiscriminant 0 (z^2) = 2*cos z := by
  rw [hillHminusDiscriminant_zero]
  rcases eq_or_eq_neg_of_sq_eq_sq (sqrt (z^2)) z (complex_sqrt_sq _) with h | h
  · rw [h]
  · rw [h,cos_neg]

theorem exists_hillHminus_uniform_small_disc_trace
    (r : ℝ) (hr : 0 < r) (hrpi : r ≤ Real.pi/4) (ε : ℝ) (hε : 0 < ε) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ 0 ∈ U ∧
      ∀ q ∈ U, ∀ k : ℕ+, ∀ z ∈ closedBall ((Real.pi : ℂ)*(k : ℕ)) r,
        ‖hillHminusDiscriminant q (z^2)-2*cos z‖ ≤ ε := by
  obtain ⟨N,V,hN,hV,h0V,hhigh⟩ := exists_hillHminus_disc_trace_approximation 0 r hr hrpi ε hε
  let F := fun t : ℂ × PeriodOneHminusOne => hillHminusDiscriminant t.2 (t.1^2)-2*cos t.1
  have hF : AnalyticOnNhd ℂ F univ := by
    intro t _
    exact ((analyticOnNhd_hillHminusDiscriminant_joint (t.1^2,t.2) (mem_univ _)).comp
      (f := fun s : ℂ × PeriodOneHminusOne => (s.1^2,s.2))
      ((analyticAt_fst.pow 2).prod analyticAt_snd)).sub
        (analyticAt_const.mul (Complex.analyticAt_cos.comp analyticAt_fst))
  have hfixed (k : ℕ+) : ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ 0 ∈ U ∧
      ∀ q ∈ U, ∀ z ∈ closedBall ((Real.pi : ℂ)*(k : ℕ)) r, ‖F (z,q)‖ ≤ ε := by
    apply exists_compact_slice_norm_bound F univ isOpen_univ hF.continuousOn
      (closedBall ((Real.pi : ℂ)*(k : ℕ)) r) (isCompact_closedBall _ _) 0 ε
      (fun _ _ => mem_univ _)
    intro z _
    simp only [F,hillHminusDiscriminant_zero_sq,sub_self,norm_zero]
    exact hε
  let W (k : ℕ+) := (hfixed k).choose
  have hW (k : ℕ+) := (hfixed k).choose_spec
  let B : Fin (N+1) → Set PeriodOneHminusOne := fun i =>
    if hi : 0 < i.val then W ⟨i.val,hi⟩ else univ
  have hB (i : Fin (N+1)) : IsOpen (B i) ∧ (0 : PeriodOneHminusOne) ∈ B i := by
    by_cases hi : 0 < i.val
    · simpa only [B,dif_pos hi] using ⟨(hW ⟨i.val,hi⟩).1,(hW ⟨i.val,hi⟩).2.1⟩
    · simp only [B,dif_neg hi]
      exact ⟨isOpen_univ,mem_univ _⟩
  refine ⟨V ∩ ⋂ i, B i,hV.inter (isOpen_iInter_of_finite fun i => (hB i).1),
    ⟨h0V,mem_iInter.mpr (fun i => (hB i).2)⟩,?_⟩
  intro q hq k z hz
  by_cases hk : (k : ℕ) ≤ N
  · have hi := mem_iInter.mp hq.2 (⟨(k : ℕ),Nat.lt_succ_of_le hk⟩ : Fin (N+1))
    exact (hW k).2.2 q (by simpa only [B,dif_pos k.pos] using! hi) z hz
  · exact hhigh q hq.1 (k : ℕ) (by omega) z hz
end NLS.KdV
