import NLS.SequenceSpaces.FiniteOutputReciprocalTail
import NLS.SequenceSpaces.FiniteBlockOperatorCompact

/-! A common l2 output majorant and fixed l2 row kernels give common
finite matrix approximations and operator-norm total boundedness of
EVERY bounded operator satisfying the same entries. -/
noncomputable section
open Set Filter Topology
open scoped ENNReal Classical BigOperators
namespace NLS.Coeff

theorem row_bound_of_l2_kernel_entries
    (T : Coeff 2 →L[ℂ] Coeff 2) (b : Coeff 2) (κ : ℤ → Coeff 2)
    (L : ℝ) (hκ : ∀ m, ‖κ m‖ ≤ L)
    (he : ∀ m k, ‖T (lp.single 2 k 1) m‖ ≤ ‖b m‖*‖κ m k‖)
    (m : ℤ) (x : Coeff 2) : ‖T x m‖ ≤ ‖b m‖*L*‖x‖ := by
  let g : Coeff 2 := (‖b m‖:ℂ) • κ m
  have hg (k : ℤ) : ‖g k‖ = ‖b m‖*‖κ m k‖ := by
    simp only [g,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,norm_mul,Complex.norm_real,
      Real.norm_of_nonneg (norm_nonneg _)]
  obtain ⟨row,hr,heq⟩ := exists_operator_rowKernel_of_entryMajorant (by norm_num) T m g
    (fun k => by rw [hg]; exact he m k)
  rw [heq]
  calc
    _ ≤ ‖x‖*‖row‖ := norm_dualPairing_le _ _
    _ ≤ ‖x‖*‖g‖ := mul_le_mul_of_nonneg_left hr (norm_nonneg _)
    _ = ‖x‖*(‖b m‖*‖κ m‖) := by
      change ‖x‖*‖((‖b m‖:ℂ) • κ m : Coeff 2)‖ = _
      rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg _)]
    _ ≤ ‖x‖*(‖b m‖*L) := by gcongr; exact hκ m
    _ = _ := by ring

theorem norm_operator_le_of_l2_kernel_entries
    (T : Coeff 2 →L[ℂ] Coeff 2) (b : Coeff 2) (κ : ℤ → Coeff 2)
    (L : ℝ) (hL : 0 ≤ L) (hκ : ∀ m, ‖κ m‖ ≤ L)
    (he : ∀ m k, ‖T (lp.single 2 k 1) m‖ ≤ ‖b m‖*‖κ m k‖) :
    ‖T‖ ≤ L*‖b‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  have hn : ‖T x‖ ≤ ‖((L*‖x‖:ℝ):ℂ) • b‖ := by
    apply lp.norm_mono (by norm_num : (2:ℝ≥0∞) ≠ 0)
    intro m
    have heq : ‖(((L*‖x‖:ℝ):ℂ) • b) m‖ = ‖b m‖*L*‖x‖ := by
      simp only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,norm_mul,Complex.norm_real,
        Real.norm_of_nonneg (mul_nonneg hL (norm_nonneg _))]
      ring
    rw [heq]
    exact row_bound_of_l2_kernel_entries T b κ L hκ he m x
  simpa only [norm_smul,Complex.norm_real,Real.norm_of_nonneg (mul_nonneg hL (norm_nonneg _)),
    mul_right_comm] using hn

theorem exists_uniform_finiteOutput_inputTail_of_l2_kernel_entries
    (s : Finset ℤ) (g : ℤ → Coeff 2) (ε : ℝ) (hε : 0 < ε) :
    ∃ t : Finset ℤ, ∀ T : Coeff 2 →L[ℂ] Coeff 2,
      (∀ m ∈ s, ∀ k, ‖T (lp.single 2 k 1) m‖ ≤ ‖g m k‖) →
      ‖(truncateCLM s).comp (T.comp (ContinuousLinearMap.id ℂ (Coeff 2)-truncateCLM t))‖ < ε := by
  have ht (m : ℤ) : Tendsto (fun t : Finset ℤ => ‖g m-truncate t (g m)‖) atTop (𝓝 (0:ℝ)) := by
    simpa only [sub_self,norm_zero] using ((tendsto_const_nhds (x := g m)).sub
      (tendsto_truncate (by norm_num) (g m))).norm
  have hsum : Tendsto (fun t : Finset ℤ => ∑ m ∈ s, ‖g m-truncate t (g m)‖) atTop (𝓝 (0:ℝ)) := by
    simpa using tendsto_finsetSum s (fun m _ => ht m)
  obtain ⟨t,ht⟩ := (hsum.eventually_lt_const hε).exists
  refine ⟨t,?_⟩
  intro T hentry
  let A := T.comp (ContinuousLinearMap.id ℂ (Coeff 2)-truncateCLM t)
  have hsingle (k : ℤ) :
      (ContinuousLinearMap.id ℂ (Coeff 2)-truncateCLM (p := 2) t) (lp.single 2 k 1) =
        if k ∈ t then 0 else lp.single 2 k 1 := by
    ext j
    by_cases hk : k ∈ t <;> by_cases hj : j = k <;> simp [hk,hj,lp.single_apply,truncate_apply]
  have hrow (m : ℤ) (hm : m ∈ s) (x : Coeff 2) :
      ‖A x m‖ ≤ ‖g m-truncate t (g m)‖*‖x‖ := by
    obtain ⟨row,hrnorm,hr⟩ := exists_operator_rowKernel_of_entryMajorant (by norm_num) A m
      (g m-truncate t (g m)) (by
        intro k
        change ‖T ((ContinuousLinearMap.id ℂ (Coeff 2)-truncateCLM (p := 2) t) (lp.single 2 k 1)) m‖ ≤ _
        rw [hsingle]
        by_cases hk : k ∈ t
        · simp [hk]
        · simpa only [if_neg hk,lp.coeFn_sub,Pi.sub_apply,truncate_apply,if_neg hk,sub_zero] using hentry m hm k)
    rw [hr]
    exact (norm_dualPairing_le _ _).trans (by nlinarith [norm_nonneg x])
  have hb : ‖(truncateCLM s).comp A‖ ≤ ∑ m ∈ s, ‖g m-truncate t (g m)‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
    intro x
    change ‖truncate s (A x)‖ ≤ _
    calc
      _ ≤ ∑ m ∈ s, ‖(lp.single 2 m (A x m) : Coeff 2)‖ := norm_sum_le _ _
      _ = ∑ m ∈ s, ‖A x m‖ := by simp only [lp.norm_single (by norm_num : (0:ℝ≥0∞) < 2)]
      _ ≤ ∑ m ∈ s, ‖g m-truncate t (g m)‖*‖x‖ := Finset.sum_le_sum (fun m hm => hrow m hm x)
      _ = _ := (Finset.sum_mul _ _ _).symm
  exact hb.trans_lt ht

theorem exists_uniform_finiteBlocks_of_l2_kernel_entries
    (b : Coeff 2) (κ : ℤ → Coeff 2) (L : ℝ) (hL : 0 ≤ L) (hκ : ∀ m, ‖κ m‖ ≤ L)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ s t : Finset ℤ, ∀ T : Coeff 2 →L[ℂ] Coeff 2,
      (∀ m k, ‖T (lp.single 2 k 1) m‖ ≤ ‖b m‖*‖κ m k‖) →
      ‖T-(truncateCLM s).comp (T.comp (truncateCLM t))‖ < ε := by
  let b' : Coeff 2 := (L:ℂ) • b
  obtain ⟨s,hs⟩ := Metric.tendsto_atTop.mp (tendsto_truncate (by norm_num) b') (ε/2) (half_pos hε)
  let g (m : ℤ) : Coeff 2 := (‖b m‖:ℂ) • κ m
  obtain ⟨t,ht⟩ := exists_uniform_finiteOutput_inputTail_of_l2_kernel_entries s g (ε/2) (half_pos hε)
  refine ⟨s,t,?_⟩
  intro T he
  have hout : ‖T-(truncateCLM s).comp T‖ < ε/2 := by
    rw [norm_sub_rev]
    have hb' (m : ℤ) : ‖b' m‖ = ‖b m‖*L := by
      simp only [b',lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,norm_mul,Complex.norm_real,
        Real.norm_of_nonneg hL,mul_comm]
    have hn : ‖(truncateCLM s).comp T-T‖ ≤ ‖truncate s b'-b'‖ := by
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      intro x
      exact norm_truncate_operator_sub_le_rowTail T b'
        (fun m a => by rw [hb']; exact row_bound_of_l2_kernel_entries T b κ L hκ he m a) s x
    exact hn.trans_lt (by simpa only [dist_eq_norm] using hs s le_rfl)
  have hin := ht T (fun m _ k => by
    simpa only [g,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,norm_mul,Complex.norm_real,
      Real.norm_of_nonneg (norm_nonneg _)] using he m k)
  have hsplit : T-(truncateCLM s).comp (T.comp (truncateCLM t)) =
      (T-(truncateCLM s).comp T)+(truncateCLM s).comp
        (T.comp (ContinuousLinearMap.id ℂ (Coeff 2)-truncateCLM t)) := by
    ext x
    simp
  rw [hsplit]
  exact (norm_add_le _ _).trans_lt (by linarith)

theorem totallyBounded_operators_of_l2_kernel_entries
    (B : Set (Coeff 2 →L[ℂ] Coeff 2))
    (b : Coeff 2) (κ : ℤ → Coeff 2) (L : ℝ) (hL : 0 ≤ L) (hκ : ∀ m, ‖κ m‖ ≤ L)
    (he : ∀ T ∈ B, ∀ m k, ‖T (lp.single 2 k 1) m‖ ≤ ‖b m‖*‖κ m k‖) :
    TotallyBounded B := by
  apply totallyBounded_operators_of_uniform_finiteBlocks B
    (isBounded_iff_forall_norm_le.mpr ⟨L*‖b‖,fun T hT => norm_operator_le_of_l2_kernel_entries T b κ L hL hκ (he T hT)⟩)
  intro ε hε
  obtain ⟨s,t,hst⟩ := exists_uniform_finiteBlocks_of_l2_kernel_entries b κ L hL hκ ε hε
  exact ⟨s,t,fun T hT => (hst T (he T hT)).le⟩

end NLS.Coeff
