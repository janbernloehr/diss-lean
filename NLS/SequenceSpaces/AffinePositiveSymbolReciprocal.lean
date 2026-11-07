import NLS.SequenceSpaces.PositiveAnalyticReciprocal
import NLS.SequenceSpaces.CompactLpMultiplier
import NLS.SequenceSpaces.ExponentEmbedding
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Analytic.Composition

/-! A nonzero constant plus a finite-exponent analytic packet has an
actual bounded analytic reciprocal on all positive slots near a base
where those slots are nonzero. One complex neighborhood serves all slots. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1≤p)]

theorem exists_local_affine_positive_reciprocal
    (hp : p≠⊤) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (U : Set E) (hU : IsOpen U) (g : E → Coeff p) (hg : AnalyticOnNhd ℂ g U)
    (c : ℂ) (hc : c≠0) (a : E) (ha : a∈U)
    (hne : ∀ n : ℤ, 0<n → c+g a n≠0) :
    ∃ V : Set E, IsOpen V ∧ a∈V ∧ V⊆U ∧ ∃ B : ℝ, 0≤B ∧ ∃ N : E → Coeff ⊤,
      AnalyticOnNhd ℂ N V ∧ ∀ x∈V, ‖N x‖≤B ∧
        (∀ j : ℤ, j≤0 → N x j=0) ∧ ∀ n : ℕ+,
          c+g x (n : ℤ)≠0 ∧ N x (n : ℤ)=(c+g x (n : ℤ))⁻¹ := by
  classical
  have hcpos : 0<‖c‖ := norm_pos_iff.mpr hc
  obtain ⟨S,hS⟩ := exists_finset_norm_tail_le hp (g a) (‖c‖/2) (half_pos hcpos)
  have hfinite : ∀ F : Finset ℤ, ∃ b : ℝ, 0<b ∧ ∀ n∈F, 0<n → b≤‖c+g a n‖ := by
    intro F
    induction F using Finset.induction_on with
    | empty => exact ⟨1,zero_lt_one,by simp⟩
    | @insert n F _ ih =>
      obtain ⟨b,hb,hbF⟩ := ih
      by_cases hn : 0<n
      · refine ⟨min b ‖c+g a n‖,lt_min hb (norm_pos_iff.mpr (hne n hn)),?_⟩
        intro j hj hjpos
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact min_le_right _ _
        · exact (min_le_left _ _).trans (hbF j hj hjpos)
      · refine ⟨b,hb,?_⟩
        intro j hj hjpos
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact (hn hjpos).elim
        · exact hbF j hj hjpos
  obtain ⟨b,hb,hbS⟩ := hfinite S
  let d := min b (‖c‖/2)
  have hd : 0<d := lt_min hb (half_pos hcpos)
  have hl (n : ℕ+) : d≤‖c+g a (n : ℤ)‖ := by
    by_cases hn : (n : ℤ)∈S
    · exact (min_le_left _ _).trans (hbS _ hn (by exact_mod_cast n.pos))
    · have ht := norm_sub_le (c+g a (n : ℤ)) (g a (n : ℤ))
      rw [add_sub_cancel_right] at ht
      exact (min_le_right b (‖c‖/2)).trans (by linarith [hS _ hn])
  let C : Coeff ⊤ := ⟨fun _ => c,memℓp_infty ⟨‖c‖,by rintro _ ⟨_,rfl⟩; exact le_rfl⟩⟩
  let J := exponentInclusion (show p≤⊤ from le_top)
  let M := fun x => C+J (g x)
  have hMa : AnalyticOnNhd ℂ M U := fun x hx => analyticAt_const.add
    ((J.analyticAt _).comp (hg x hx))
  obtain ⟨V,hV,haV,hVU,hVl⟩ := exists_local_positive_symbol_lower U hU M a ha
    (hMa a ha).continuousAt d hd hl
  obtain ⟨N,hNa,hNd⟩ := exists_positive_analytic_reciprocal V hV M (hMa.mono hVU)
    (d/2) (half_pos hd) hVl
  refine ⟨V,hV,haV,hVU,(d/2)⁻¹,by positivity,N,hNa,?_⟩
  intro x hx
  refine ⟨(hNd x hx).1,(hNd x hx).2.1,?_⟩
  intro n
  have hnx : M x (n : ℤ)≠0 := norm_pos_iff.mp ((half_pos hd).trans_le (hVl x hx n))
  exact ⟨hnx,(hNd x hx).2.2 n |>.1⟩

end NLS.Coeff
