import NLS.SequenceSpaces.DominatedConvergence
import NLS.SequenceSpaces.FiniteModification
import NLS.SequenceSpaces.BoundedMatrixLimitPointwise
import NLS.SequenceSpaces.Truncation
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Column limits and finite-input operator convergence

A fixed summable output majorant upgrades scalar entry limits to full
column convergence. A finite input projection then gives a finite sum
of rank-one operators, so its compressed operators converge in norm.
-/

noncomputable section
open Set Filter Topology
open scoped NNReal ENNReal BigOperators
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Eventual column domination on the output tail, together with a
common operator bound for the finitely many remaining rows, upgrades
the scalar entries of a fixed column to convergence in `ℓᵖ` norm. -/
theorem tendsto_operator_column_of_tailMajorant
    (hp : p ≠ ⊤) {ι : Type*} (l : Filter ι) [NeBot l]
    (T : ι → Coeff p →L[ℂ] Coeff p) (Q : Coeff p →L[ℂ] Coeff p)
    (M : ℝ) (hM : 0 ≤ M) (hnorm : ∀ᶠ i in l, ‖T i‖ ≤ M)
    (b : Coeff p) (K : ℕ) (k : ℤ)
    (htail : ∀ᶠ i in l, ∀ m : ℤ, K ≤ m.natAbs → m ≠ k →
      ‖(T i (lp.single p k 1)) m‖ ≤ ‖b m‖)
    (hentry : ∀ m : ℤ, Tendsto (fun i => (T i (lp.single p k 1)) m)
      l (𝓝 ((Q (lp.single p k 1)) m))) :
    Tendsto (fun i => T i (lp.single p k 1)) l (𝓝 (Q (lp.single p k 1))) := by
  classical
  let head : Finset ℤ := Finset.Icc (-(K : ℤ)) (K : ℤ) ∪ {k}
  let g : Coeff p := ⟨fun m => if m ∈ head then (M : ℂ) else b m,
    NLS.memℓp_of_eq_outside_finset (lp.memℓp b) head (by
      intro m hm
      simp [hm])⟩
  have hdom : ∀ᶠ i in l, ∀ m : ℤ,
      ‖(T i (lp.single p k 1)) m‖ ≤ ‖g m‖ := by
    filter_upwards [hnorm,htail] with i hi ht
    intro m
    by_cases hm : m ∈ head
    · have hg : ‖g m‖ = M := by
        simp [g,hm,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hM]
      rw [hg]
      calc
        ‖(T i (lp.single p k 1)) m‖ ≤ ‖T i (lp.single p k 1)‖ :=
          lp.norm_apply_le_norm (zero_lt_one.trans_le Fact.out).ne' _ _
        _ ≤ M*‖(lp.single p k 1 : Coeff p)‖ := (T i).le_of_opNorm_le hi _
        _ = M := by simp [lp.norm_single (zero_lt_one.trans_le Fact.out)]
    · have hmK : K ≤ m.natAbs := by
        simp only [head,Finset.mem_union,Finset.mem_Icc,Finset.mem_singleton] at hm
        omega
      have hmk : m ≠ k := by
        intro heq
        exact hm (Finset.mem_union_right _ (Finset.mem_singleton.mpr heq))
      simpa [g,hm] using ht m hmK hmk
  have hQdom (m : ℤ) : ‖(Q (lp.single p k 1)) m‖ ≤ ‖g m‖ :=
    le_of_tendsto (hentry m).norm (hdom.mono fun i hi => hi m)
  have hdiffdom : ∀ᶠ i in l, ∀ m : ℤ,
      ‖(T i (lp.single p k 1) - Q (lp.single p k 1)) m‖ ≤
        ‖((2 : ℂ) • g) m‖ := by
    filter_upwards [hdom] with i hi
    intro m
    have h := (norm_sub_le _ _).trans (add_le_add (hi m) (hQdom m))
    have hgTwo : ‖((2 : ℂ) • g) m‖ = ‖g m‖+‖g m‖ := by
      simp only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,norm_mul]
      norm_num
      ring
    rw [hgTwo]
    exact h
  have hzero := tendsto_zero_of_dominated hp
    (fun i => T i (lp.single p k 1) - Q (lp.single p k 1))
    ((2 : ℂ) • g) hdiffdom (fun m => by
      simpa only [lp.coeFn_sub,Pi.sub_apply,sub_self] using
        (hentry m).sub_const ((Q (lp.single p k 1)) m))
  simpa only [sub_add_cancel,zero_add] using hzero.add_const (Q (lp.single p k 1))

/-- A finite input compression is a finite sum of rank-one maps whose
output vectors are the complete columns of the operator. -/
theorem operator_comp_truncate_eq_columnSum
    (T : Coeff p →L[ℂ] Coeff p) (s : Finset ℤ) :
    T.comp (truncateCLM s) = ∑ k ∈ s,
      (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p k).smulRight (T (lp.single p k 1)) := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply,truncateCLM_apply,truncate,
    map_sum,sum_apply,ContinuousLinearMap.smulRight_apply]
  apply Finset.sum_congr rfl
  intro k hk
  have hsingle : (lp.single p k (x k) : Coeff p) = x k • lp.single p k 1 := by
    ext m
    by_cases hmk : m = k <;> simp [lp.single_apply,hmk]
  rw [hsingle,map_smul]
  rfl

/-- Norm convergence of each complete column implies operator-norm
convergence after any fixed finite input projection. -/
theorem tendsto_operator_finiteInputs_of_columns
    {ι : Type*} (l : Filter ι)
    (T : ι → Coeff p →L[ℂ] Coeff p) (Q : Coeff p →L[ℂ] Coeff p)
    (hcol : ∀ k : ℤ, Tendsto (fun i => T i (lp.single p k 1))
      l (𝓝 (Q (lp.single p k 1)))) (s : Finset ℤ) :
    Tendsto (fun i => (T i).comp (truncateCLM s))
      l (𝓝 (Q.comp (truncateCLM s))) := by
  have hsum := tendsto_finsetSum s (fun k _ =>
    ((ContinuousLinearMap.smulRightL ℂ (Coeff p) (Coeff p)
      (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p k)).continuous.tendsto
        (Q (lp.single p k 1))).comp (hcol k))
  change Tendsto (fun i => ∑ k ∈ s,
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p k).smulRight (T i (lp.single p k 1)))
    l (𝓝 (∑ k ∈ s,
      (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p k).smulRight (Q (lp.single p k 1)))) at hsum
  simpa only [operator_comp_truncate_eq_columnSum] using hsum

/-- Strong convergence extends from the coordinate vectors to every
input when the family has an eventual common operator-norm bound. -/
theorem tendsto_operator_strong_of_columns
    (hp : p ≠ ⊤) {ι : Type*} (l : Filter ι)
    (T : ι → Coeff p →L[ℂ] Coeff p) (Q : Coeff p →L[ℂ] Coeff p)
    (M : ℝ) (hM : 0 ≤ M) (hQ : ‖Q‖ ≤ M)
    (hnorm : ∀ᶠ i in l, ‖T i‖ ≤ M)
    (hcol : ∀ k : ℤ, Tendsto (fun i => T i (lp.single p k 1))
      l (𝓝 (Q (lp.single p k 1)))) (x : Coeff p) :
    Tendsto (fun i => T i x) l (𝓝 (Q x)) := by
  classical
  let T' (i : ι) : Coeff p →L[ℂ] Coeff p := if ‖T i‖ ≤ M then T i else Q
  have hT'norm (i : ι) : ‖T' i‖ ≤ M := by
    dsimp [T']
    split_ifs with hi
    · exact hi
    · exact hQ
  have hTeq : T' =ᶠ[l] T := by
    filter_upwards [hnorm] with i hi
    simp [T',hi]
  let F : ι → Coeff p → Coeff p := fun i y => T' i y
  let B : ℝ≥0 := ⟨M,hM⟩
  have hFlipschitz (i : ι) : LipschitzWith B (F i) :=
    ContinuousLinearMap.lipschitzWith_of_opNorm_le (hT'norm i)
  have hFequi : Equicontinuous F :=
    (LipschitzWith.uniformEquicontinuous F B hFlipschitz).equicontinuous
  have hclosed : IsClosed {y : Coeff p | Tendsto (fun i => F i y) l (𝓝 (Q y))} :=
    hFequi.isClosed_setOfPred_tendsto Q.continuous
  have hfinite : {y : Coeff p | HasFiniteSupport y} ⊆
      {y : Coeff p | Tendsto (fun i => F i y) l (𝓝 (Q y))} := by
    intro y hy
    obtain ⟨s,hs⟩ := hy
    have htruncate : truncate s y = y := by
      ext m
      by_cases hm : m ∈ s
      · simp [hm]
      · simp [hm,hs m hm]
    have hlimit := ((ContinuousLinearMap.apply ℂ (Coeff p) y).continuous.tendsto
      (Q.comp (truncateCLM s))).comp
        (tendsto_operator_finiteInputs_of_columns l T Q hcol s)
    change Tendsto (fun i => ((T i).comp (truncateCLM s)) y)
      l (𝓝 ((Q.comp (truncateCLM s)) y)) at hlimit
    have hyLimit : Tendsto (fun i => T i y) l (𝓝 (Q y)) := by
      simpa only [ContinuousLinearMap.comp_apply,truncateCLM_apply,htruncate] using hlimit
    apply hyLimit.congr'
    filter_upwards [hTeq] with i hi
    simp [F,hi]
  have hlimit : Tendsto (fun i => F i x) l (𝓝 (Q x)) :=
    hclosed.closure_subset (closure_mono hfinite ((dense_finiteSupport hp) x))
  apply hlimit.congr'
  filter_upwards [hTeq] with i hi
  simp [F,hi]

/-- For fixed finite inputs, one output cutoff makes the mixed
high-output block small eventually throughout a column-convergent
family. This controls the entire output tail, not just finite rows. -/
theorem exists_eventual_uniform_outputTail_of_finiteInputs
    (hp : p ≠ ⊤) {ι : Type*} (l : Filter ι)
    (T : ι → Coeff p →L[ℂ] Coeff p) (Q : Coeff p →L[ℂ] Coeff p)
    (hcol : ∀ k : ℤ, Tendsto (fun i => T i (lp.single p k 1))
      l (𝓝 (Q (lp.single p k 1))))
    (s : Finset ℤ) (ε : ℝ) (hε : 0 < ε) :
    ∃ t : Finset ℤ, ∀ᶠ i in l,
      ‖(ContinuousLinearMap.id ℂ (Coeff p) - truncateCLM t).comp
        ((T i).comp (truncateCLM s))‖ < ε := by
  let A (t : Finset ℤ) : Coeff p →L[ℂ] Coeff p := (truncateCLM t).comp Q
  have hAcol (k : ℤ) : Tendsto (fun t => A t (lp.single p k 1))
      atTop (𝓝 (Q (lp.single p k 1))) := tendsto_truncate hp _
  have hA := tendsto_operator_finiteInputs_of_columns atTop A Q hAcol s
  obtain ⟨t,ht⟩ := Metric.tendsto_atTop.mp hA (ε/2) (by positivity)
  let H : Coeff p →L[ℂ] Coeff p := ContinuousLinearMap.id ℂ (Coeff p) - truncateCLM t
  let B : Coeff p →L[ℂ] Coeff p := Q.comp (truncateCLM s)
  have hH : ‖H‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro x
    change ‖x-truncate t x‖ ≤ 1*‖x‖
    simpa only [one_mul] using norm_sub_truncate_le
      (zero_lt_one.trans_le Fact.out).ne' t x
  have hQB : ‖H.comp B‖ < ε/2 := by
    have heq : H.comp B = B-(A t).comp (truncateCLM s) := by
      ext x
      simp [H,B,A]
    rw [heq,norm_sub_rev]
    simpa only [dist_eq_norm,B] using ht t le_rfl
  have hnear := Metric.tendsto_nhds.mp
    (tendsto_operator_finiteInputs_of_columns l T Q hcol s) (ε/2) (by positivity)
  refine ⟨t,?_⟩
  filter_upwards [hnear] with i hi
  rw [dist_eq_norm] at hi
  have hsplit : H.comp ((T i).comp (truncateCLM s)) =
      H.comp ((T i).comp (truncateCLM s)-B) + H.comp B := by
    ext x
    simp
  have hnorm : ‖H.comp ((T i).comp (truncateCLM s)-B)‖ ≤
      ‖(T i).comp (truncateCLM s)-B‖ := by
    calc
      _ ≤ ‖H‖*‖(T i).comp (truncateCLM s)-B‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1*‖(T i).comp (truncateCLM s)-B‖ := by gcongr
      _ = _ := one_mul _
  change ‖H.comp ((T i).comp (truncateCLM s))‖ < ε
  rw [hsplit]
  have htri : ‖H.comp ((T i).comp (truncateCLM s)-B) + H.comp B‖ ≤
      ‖(T i).comp (truncateCLM s)-B‖+‖H.comp B‖ :=
    (norm_add_le _ _).trans (add_le_add hnorm le_rfl)
  change ‖(T i).comp (truncateCLM s)-B‖ < ε/2 at hi
  linarith

end NLS.Coeff
