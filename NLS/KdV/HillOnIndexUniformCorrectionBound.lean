import NLS.KdV.HillOnIndexUniformCorrectionTail

/-! One local bound BEFORE ALL n for the ACTUAL diagonal correction,
at EVERY complex source of the retained patch's physical divisor domain.
The common tail and finitely many analytic low coordinates suffice. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem exists_local_uniform_physicalOnIndexAbelianCorrection_bound (P : HillProductEquationPatch)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots)
    (q : PeriodOneHminusOne) (hq : q ∈ P.physicalDirichletSource) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q ∈ U ∧ U ⊆ P.physicalDirichletSource ∧
      ∃ C : ℝ, 0 < C ∧ ∀ a ∈ U, ∀ n : ℕ+,
        ‖P.physicalOnIndexAbelianCorrection n a‖ ≤ C := by
  obtain ⟨Ut,hUt,hqt,hUtP,K,Ct,hCt,htail⟩ :=
    P.exists_local_uniform_physicalOnIndexAbelianCorrection_tail_bound H q hq
  have hfinite : {n : ℕ+ | (n:ℕ) ≤ K}.Finite :=
    (Set.finite_Iic K).preimage (fun _ _ _ _ h => PNat.coe_injective h)
  let F := hfinite.toFinset
  have hevent : ∀ᶠ a in 𝓝 q, ∀ n ∈ F,
      ‖P.physicalOnIndexAbelianCorrection n a‖ < ‖P.physicalOnIndexAbelianCorrection n q‖+1 := by
    rw [Finset.eventually_all]
    intro n _
    exact (P.analytic_physicalOnIndexAbelianCorrection n q hq).continuousAt.norm.eventually
      (Iio_mem_nhds (by linarith : ‖P.physicalOnIndexAbelianCorrection n q‖ < ‖P.physicalOnIndexAbelianCorrection n q‖+1))
  obtain ⟨O,hOsub,hO,hqO⟩ := _root_.mem_nhds_iff.mp hevent
  let B := ∑ n ∈ F, (‖P.physicalOnIndexAbelianCorrection n q‖+1)
  have hB : 0 ≤ B := Finset.sum_nonneg (fun n _ => by positivity)
  refine ⟨Ut ∩ O,hUt.inter hO,⟨hqt,hqO⟩,(fun _ h => hUtP h.1),Ct+B,by positivity,?_⟩
  intro a ha n
  by_cases hn : K < (n:ℕ)
  · exact (htail a ha.1 n hn).trans (le_add_of_nonneg_right hB)
  · have hnF : n ∈ F := by rw [Set.Finite.mem_toFinset]; exact le_of_not_gt hn
    have hnB : ‖P.physicalOnIndexAbelianCorrection n q‖+1 ≤ B := by
      dsimp only [B]
      exact Finset.single_le_sum (fun k _ => show (0:ℝ) ≤ ‖P.physicalOnIndexAbelianCorrection k q‖+1 from by positivity) hnF
    exact (hOsub ha.2 n hnF).le.trans (hnB.trans (by linarith))

theorem exists_local_uniform_physicalOnIndex_phase_exponential_bound (P : HillProductEquationPatch)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots)
    (q : PeriodOneHminusOne) (hq : q ∈ P.physicalDirichletSource) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q ∈ U ∧ U ⊆ P.physicalDirichletSource ∧
      ∃ C : ℝ, 0 < C ∧ ∀ a ∈ U, ∀ n : ℕ+,
        ‖Complex.exp (I*P.physicalOnIndexAbelianCorrection n a)‖ ≤ C ∧
          ‖Complex.exp (-I*P.physicalOnIndexAbelianCorrection n a)‖ ≤ C := by
  obtain ⟨U,hU,hqU,hUP,R,_,hbound⟩ := P.exists_local_uniform_physicalOnIndexAbelianCorrection_bound H q hq
  refine ⟨U,hU,hqU,hUP,Real.exp R,Real.exp_pos _,?_⟩
  intro a ha n
  have hb := hbound a ha n
  constructor
  · rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    apply (Complex.re_le_norm _).trans
    simpa only [norm_mul,norm_I,one_mul] using hb
  · rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    apply (Complex.re_le_norm _).trans
    simpa only [norm_mul,norm_neg,norm_I,one_mul] using hb

end NLS.KdV.HillProductEquationPatch
