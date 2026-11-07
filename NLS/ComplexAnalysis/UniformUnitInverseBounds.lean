import NLS.ComplexAnalysis.ReciprocalPerturbation
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.Deriv.Inv

/-! Nonzero analytic positive sequences with one locally uniform
half-unit tail have locally uniform bounds for both the sequence and
its reciprocal. The finitely many low indices are retained explicitly. -/
noncomputable section
open Set Filter Topology
namespace NLS.ComplexAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem exists_local_uniform_unit_inverse_bounds (u : ℕ+ → E → ℂ) {U : Set E}
    (hU : IsOpen U) (hu : ∀ n, AnalyticOnNhd ℂ (u n) U)
    (hne : ∀ n, ∀ a ∈ U, u n a ≠ 0) (q : E) (hq : q ∈ U)
    (ht : ∃ N : ℕ, ∃ V : Set E, IsOpen V ∧ q ∈ V ∧ V ⊆ U ∧
      ∀ n : ℕ+, N ≤ (n:ℕ) → ∀ a ∈ V, ‖u n a-1‖ ≤ (1:ℝ)/2) :
    ∃ W : Set E, IsOpen W ∧ q ∈ W ∧ W ⊆ U ∧
      ∃ C : ℝ, 1 ≤ C ∧ ∀ a ∈ W, ∀ n, ‖u n a‖ ≤ C ∧ ‖(u n a)⁻¹‖ ≤ C := by
  classical
  obtain ⟨N,V,hV,hqV,hVU,ht⟩ := ht
  have hfinite : {n : ℕ+ | (n:ℕ) < N}.Finite :=
    (Set.finite_Iio N).preimage (fun _ _ _ _ h => PNat.coe_injective h)
  let F := hfinite.toFinset
  have hlow : ∀ᶠ a in 𝓝 q, ∀ n ∈ F,
      ‖u n a‖ < ‖u n q‖+1 ∧ ‖(u n a)⁻¹‖ < ‖(u n q)⁻¹‖+1 := by
    rw [Finset.eventually_all]
    intro n _
    have hc := (hu n q hq).continuousAt
    have hi := ((hu n q hq).inv (hne n q hq)).continuousAt
    exact (hc.norm.eventually (Iio_mem_nhds (by linarith))).and
      (hi.norm.eventually (Iio_mem_nhds (by
        change ‖(u n q)⁻¹‖ < ‖(u n q)⁻¹‖+1
        linarith)))
  obtain ⟨W,hWsub,hW,hqW⟩ := _root_.mem_nhds_iff.mp
    (Filter.inter_mem (hV.mem_nhds hqV) (Filter.inter_mem hlow (hU.mem_nhds hq)))
  let L := ∑ n ∈ F, (‖u n q‖+‖(u n q)⁻¹‖+1)
  have hL : 0 ≤ L := Finset.sum_nonneg (fun _ _ => by positivity)
  refine ⟨W,hW,hqW,(fun _ ha => hVU (hWsub ha).1),L+2,by linarith,?_⟩
  intro a ha n
  by_cases hn : N ≤ (n:ℕ)
  · have hb := ht n hn a (hWsub ha).1
    have hs := norm_add_le (u n a-1) (1:ℂ)
    rw [sub_add_cancel,norm_one] at hs
    have hi : ‖(u n a)⁻¹‖ ≤ 2 := by
      have he := norm_inv_sub_le (a := (1:ℂ)) (t := 1-u n a) (by simp)
        (by simpa only [norm_sub_rev] using hb)
      simpa only [sub_sub_cancel,norm_one,div_one] using he
    exact ⟨by linarith,by linarith⟩
  · have hnF : n ∈ F := by rw [Set.Finite.mem_toFinset]; exact lt_of_not_ge hn
    have hb := (hWsub ha).2.1 n hnF
    have hs : ‖u n q‖+‖(u n q)⁻¹‖+1 ≤ L := by
      dsimp only [L]
      exact Finset.single_le_sum (fun k _ => show (0:ℝ) ≤ ‖u k q‖+‖(u k q)⁻¹‖+1 from by positivity) hnF
    constructor <;> linarith [norm_nonneg (u n q),norm_nonneg ((u n q)⁻¹)]

end NLS.ComplexAnalysis
