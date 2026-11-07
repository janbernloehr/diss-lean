import NLS.KdV.HillAbelianUniformSelectedValue
import NLS.KdV.HillAbelianUniformValueTail

/-! ONE local complex neighborhood and positive constant control ALL
ACTUAL off-index values at ALL selected and numerator indices. Finite
low selected gaps and the common infinite tail retain their actual divisors. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem exists_local_uniform_physicalOffIndexAbelianValue_bound (P : HillProductEquationPatch)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q ∈ U ∧ U ⊆ P.physicalDirichletSource ∧
      ∃ C : ℝ, 0 < C ∧ ∀ a ∈ U, ∀ n m : ℕ+, m ≠ n →
        ‖P.physicalOffIndexAbelianValue n m a‖ ≤ C*
          (‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (P.sourcePsi a) ((m:ℕ):ℤ)‖+
            ‖P.physicalDirichletFrequency ((m:ℕ):ℤ) a-sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi a) ((m:ℕ):ℤ)‖)*
          (1/|((n:ℕ):ℝ)-(m:ℕ)|+1/((n:ℕ)+(m:ℕ):ℝ)) := by
  obtain ⟨Ut,hUt,hqt,hUtP,K,Ct,hCt,htail⟩ := P.exists_local_uniform_physicalOffIndexAbelianValue_tail_bound H q
    (P.real_mem_physicalDirichletSource q hq hr)
  have hlocal (m : ℕ+) := P.exists_local_uniform_selected_physicalOffIndexAbelianValue_bound H q hq hr m
  choose Um hUm hqm _ Cm hCm hbound using hlocal
  have hfinite : {m : ℕ+ | (m:ℕ) ≤ K}.Finite :=
    (Set.finite_Iic K).preimage (fun _ _ _ _ h => PNat.coe_injective h)
  let F := hfinite.toFinset
  have hevent : ∀ᶠ a in 𝓝 q, ∀ m ∈ F, a ∈ Um m := by
    rw [Finset.eventually_all]
    intro m _
    exact (hUm m).mem_nhds (hqm m)
  obtain ⟨O,hOsub,hO,hqO⟩ := _root_.mem_nhds_iff.mp hevent
  let B := ∑ m ∈ F, Cm m
  have hB : 0 ≤ B := Finset.sum_nonneg (fun m _ => (hCm m).le)
  refine ⟨Ut ∩ O,hUt.inter hO,⟨hqt,hqO⟩,(fun a ha => hUtP ha.1),Ct+B,by positivity,?_⟩
  intro a ha n m hmn
  have hweight : 0 ≤ ‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (P.sourcePsi a) ((m:ℕ):ℤ)‖+
      ‖P.physicalDirichletFrequency ((m:ℕ):ℤ) a-sourceStandardRootMidpoint (by norm_num) (by norm_num) (P.sourcePsi a) ((m:ℕ):ℤ)‖ := by positivity
  have hkernel : 0 ≤ 1/|((n:ℕ):ℝ)-(m:ℕ)|+1/((n:ℕ)+(m:ℕ):ℝ) := by positivity
  by_cases hm : K < (m:ℕ)
  · exact (htail a ha.1 n m hm hmn).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hB) hweight) hkernel)
  · have hmF : m ∈ F := by
      change m ∈ hfinite.toFinset
      rw [Set.Finite.mem_toFinset]
      exact le_of_not_gt hm
    have hmB : Cm m ≤ B := Finset.single_le_sum (fun k _ => (hCm k).le) hmF
    have hmC : Cm m ≤ Ct+B := by linarith [hCt]
    exact (hbound m a (hOsub ha.2 m hmF) n hmn).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hmC hweight) hkernel)

end NLS.KdV.HillProductEquationPatch
