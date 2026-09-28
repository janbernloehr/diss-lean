import NLS.SequenceSpaces.Truncation
import NLS.SequenceSpaces.BoundedMatrixLimitPointwise
import NLS.SequenceSpaces.CompactRowMajorant
import NLS.SequenceSpaces.FiniteModification
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.Algebra.Monoid

/-!
# Finite blocks of operators on sequence spaces

The proof of Lemma 12.10 compares extended Jacobians in operator norm.
On fixed finite input and output cutoffs, their matrix entries
determine the compressed operator. This file makes that reduction
explicit, so scalar contour limits can later be assembled into the
finite-block part of the operator-norm convergence argument.
-/

noncomputable section
open Filter Topology
open scoped ENNReal BigOperators
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The rank-one operator taking input coordinate `k` to output
coordinate `m`. -/
def matrixUnit (m k : ℤ) : Coeff p →L[ℂ] Coeff p :=
  (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) p m).comp
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p k)

@[simp] theorem matrixUnit_apply (m k : ℤ) (a : Coeff p) :
    matrixUnit m k a = lp.single p m (a k) := rfl

/-- A finite Fourier projection is the sum of its diagonal matrix
units. -/
theorem truncateCLM_eq_matrixUnit_sum (s : Finset ℤ) :
    truncateCLM (p := p) s = ∑ m ∈ s, matrixUnit (p := p) m m := by
  apply ContinuousLinearMap.ext
  intro a
  change truncate s a = (∑ m ∈ s, matrixUnit (p := p) m m) a
  rw [truncate]
  simp only [sum_apply,matrixUnit_apply]

/-- Multiplying an operator by matrix units extracts one matrix
entry and places it at the selected input and output coordinates. -/
theorem matrixUnit_mul_operator_mul_matrixUnit
    (T : Coeff p →L[ℂ] Coeff p) (m k : ℤ) :
    matrixUnit (p := p) m m * T * matrixUnit k k =
      ((T (lp.single p k 1)) m) • matrixUnit m k := by
  apply ContinuousLinearMap.ext
  intro a
  change lp.single p m
      ((T (lp.single p k (a k))) m) =
        ((T (lp.single p k 1)) m) •
          (lp.single p m (a k : ℂ) : Coeff p)
  have hsingle : lp.single p k (a k) =
      (a k) • (lp.single p k (1 : ℂ) : Coeff p) := by
    ext j
    by_cases hjk : j = k <;> simp [hjk,lp.single_apply]
  rw [hsingle,map_smul]
  ext j
  simp only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul]
  by_cases hjm : j = m <;> simp [hjm,lp.single_apply,mul_comm]

/-- Compressing a bounded operator to two finite coordinate sets is
the finite sum of its scalar matrix entries times matrix units. -/
theorem finiteBlock_eq_matrixSum
    (T : Coeff p →L[ℂ] Coeff p) (s t : Finset ℤ) :
    (truncateCLM s).comp (T.comp (truncateCLM t)) =
      ∑ m ∈ s, ∑ k ∈ t,
        ((T (lp.single p k 1)) m) • matrixUnit (p := p) m k := by
  change (truncateCLM (p := p) s) * T * (truncateCLM t) = _
  rw [truncateCLM_eq_matrixUnit_sum s,
    truncateCLM_eq_matrixUnit_sum t]
  simp only [Finset.sum_mul, Finset.mul_sum,
    matrixUnit_mul_operator_mul_matrixUnit]
  rw [Finset.sum_comm]

/-- Entrywise convergence on a fixed finite rectangle gives
operator-norm convergence of the corresponding compressed blocks. -/
theorem tendsto_finiteBlock_of_entries
    (T : ℤ → Coeff p →L[ℂ] Coeff p)
    (S : Coeff p →L[ℂ] Coeff p) (s t : Finset ℤ)
    (hentry : ∀ m ∈ s, ∀ k ∈ t,
      Tendsto (fun n : ℤ => (T n (lp.single p k 1)) m)
        (Filter.comap Int.natAbs Filter.atTop)
        (𝓝 ((S (lp.single p k 1)) m))) :
    Tendsto (fun n : ℤ =>
      (truncateCLM s).comp ((T n).comp (truncateCLM t)))
      (Filter.comap Int.natAbs Filter.atTop)
      (𝓝 ((truncateCLM s).comp (S.comp (truncateCLM t)))) := by
  have hsum : Tendsto (fun n : ℤ =>
      ∑ m ∈ s, ∑ k ∈ t,
        ((T n (lp.single p k 1)) m) • matrixUnit (p := p) m k)
      (Filter.comap Int.natAbs Filter.atTop)
      (𝓝 (∑ m ∈ s, ∑ k ∈ t,
        ((S (lp.single p k 1)) m) • matrixUnit (p := p) m k)) := by
    apply tendsto_finsetSum
    intro m hm
    apply tendsto_finsetSum
    intro k hk
    exact (hentry m hm k hk).smul_const _
  simpa only [finiteBlock_eq_matrixSum] using hsum

/-- A common norm bound controls the finitely many head rows, while a
fixed `ℓᵖ` majorant controls all tail rows. Consequently one output
projection approximates every operator sufficiently far along the
family. -/
theorem exists_eventual_uniform_outputBlock_of_tailRowMajorant
    (hp : p ≠ ⊤)
    {α : Type*} (l : Filter α)
    (T : α → Coeff p →L[ℂ] Coeff p)
    (b : Coeff p) (K : ℕ) (M : ℝ) (hM : 0 ≤ M)
    (hnorm : ∀ᶠ i in l, ‖T i‖ ≤ M)
    (hrow : ∀ᶠ i in l, ∀ m : ℤ, K ≤ m.natAbs →
      ∀ x : Coeff p, ‖T i x m‖ ≤ ‖b m‖ * ‖x‖)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ s : Finset ℤ, ∀ᶠ i in l,
      ‖(truncateCLM s).comp (T i) - T i‖ < ε := by
  classical
  let head : Finset ℤ := Finset.Icc (-(K : ℤ)) (K : ℤ)
  let b' : Coeff p :=
    ⟨fun m => if m ∈ head then (M : ℂ) else b m,
      NLS.memℓp_of_eq_outside_finset (lp.memℓp b) head (by
        intro m hm
        simp [hm])⟩
  obtain ⟨s,hs⟩ := Metric.tendsto_atTop.mp (tendsto_truncate hp b') ε hε
  refine ⟨s,?_⟩
  filter_upwards [hnorm,hrow] with i hi hr
  have hrow' (m : ℤ) (x : Coeff p) :
      ‖T i x m‖ ≤ ‖b' m‖ * ‖x‖ := by
    by_cases hm : m ∈ head
    · have heval : ‖T i x m‖ ≤ ‖T i x‖ :=
        lp.norm_apply_le_norm
          (ne_of_gt (zero_lt_one.trans_le Fact.out)) _ m
      have hop : ‖T i x‖ ≤ M * ‖x‖ :=
        (T i).le_of_opNorm_le hi x
      have hb' : ‖b' m‖ = M := by
        simp [b',hm,Complex.norm_real,Real.norm_eq_abs,
          abs_of_nonneg hM]
      rw [hb']
      exact heval.trans hop
    · have hmK : K ≤ m.natAbs := by
        simp only [head,Finset.mem_Icc] at hm
        omega
      have hb' : b' m = b m := by simp [b',hm]
      rw [hb']
      exact hr m hmK x
  have hnorm' : ‖(truncateCLM s).comp (T i) - T i‖ ≤
      ‖truncate s b' - b'‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    change ‖truncate s (T i x) - T i x‖ ≤
      ‖truncate s b' - b'‖ * ‖x‖
    exact norm_truncate_operator_sub_le_rowTail (T i) b' hrow' s x
  have hb : ‖truncate s b' - b'‖ < ε := by
    simpa only [dist_eq_norm] using hs s le_rfl
  exact hnorm'.trans_lt hb

/-- To prove operator-norm convergence, it suffices to control the
two-sided finite-block truncation uniformly and prove convergence of
each scalar matrix entry. The analytic estimates in Lemma 12.10 must
provide precisely the uniform approximation hypothesis here. -/
theorem tendsto_operator_of_entries_and_uniform_finiteBlocks
    (T : ℤ → Coeff p →L[ℂ] Coeff p)
    (S : Coeff p →L[ℂ] Coeff p)
    (hentry : ∀ m k : ℤ,
      Tendsto (fun n : ℤ => (T n (lp.single p k 1)) m)
        (Filter.comap Int.natAbs Filter.atTop)
        (𝓝 ((S (lp.single p k 1)) m)))
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ s t : Finset ℤ,
      (∀ n : ℤ,
        ‖T n - (truncateCLM s).comp ((T n).comp (truncateCLM t))‖ < ε) ∧
      ‖S - (truncateCLM s).comp (S.comp (truncateCLM t))‖ < ε) :
    Tendsto T (Filter.comap Int.natAbs Filter.atTop) (𝓝 S) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨s,t,hT,hS⟩ := happrox (ε / 3) (by positivity)
  have hblock := tendsto_finiteBlock_of_entries T S s t
    (fun m hm k hk => hentry m k)
  have hevent := (Metric.tendsto_nhds.mp hblock) (ε / 3) (by positivity)
  filter_upwards [hevent] with n hn
  rw [dist_eq_norm] at hn ⊢
  let Bn := (truncateCLM s).comp ((T n).comp (truncateCLM t))
  let BS := (truncateCLM s).comp (S.comp (truncateCLM t))
  have htri : ‖T n - S‖ ≤ ‖T n - Bn‖ + ‖Bn - BS‖ + ‖BS - S‖ := by
    calc
      ‖T n - S‖ = ‖(T n - Bn) + (Bn - BS) + (BS - S)‖ := by congr 1; abel
      _ ≤ ‖T n - Bn‖ + ‖Bn - BS‖ + ‖BS - S‖ := by
        exact (norm_add_le ((T n - Bn) + (Bn - BS)) (BS - S)).trans
          (add_le_add_left (norm_add_le (T n - Bn) (Bn - BS)) _)
  have hlast : ‖BS - S‖ < ε / 3 := by
    rw [norm_sub_rev]
    exact hS
  have hfirst : ‖T n - Bn‖ < ε / 3 := hT n
  have hmiddle : ‖Bn - BS‖ < ε / 3 := hn
  linarith

/-- Coordinatewise convergence and eventual finite-block approximation of
the remainders imply operator-norm convergence. Subtracting a fixed
operator allows this criterion to apply when the full operators contain
a noncompact common term, such as the identity. -/
theorem tendsto_operator_of_coordinatewise_and_eventual_remainder_finiteBlocks
    (T : ℤ → Coeff p →L[ℂ] Coeff p)
    (S D : Coeff p →L[ℂ] Coeff p)
    (hpoint : ∀ x : Coeff p, ∀ m : ℤ,
      Tendsto (fun n : ℤ => (T n x) m)
        (Filter.comap Int.natAbs Filter.atTop) (𝓝 ((S x) m)))
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ s t : Finset ℤ,
      ∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
        ‖(T n - D) - (truncateCLM s).comp
          ((T n - D).comp (truncateCLM t))‖ < ε) :
    Tendsto T (Filter.comap Int.natAbs Filter.atTop) (𝓝 S) := by
  let : NeBot (Filter.comap Int.natAbs Filter.atTop) :=
    (inferInstance : NeBot (Filter.atTop : Filter ℕ)).comap_of_surj
      Int.natAbs_surjective
  let R (n : ℤ) := T n - D
  let U := S - D
  have hRpoint (x : Coeff p) (m : ℤ) :
      Tendsto (fun n : ℤ => (R n x) m)
        (Filter.comap Int.natAbs Filter.atTop) (𝓝 ((U x) m)) := by
    simpa [R, U, sub_apply] using
      (hpoint x m).sub_const ((D x) m)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨s, t, htail⟩ := happrox (ε / 4) (by positivity)
  let P := truncateCLM (p := p) s
  let Q := truncateCLM (p := p) t
  let A (n : ℤ) := R n - P.comp ((R n).comp Q)
  let B := U - P.comp (U.comp Q)
  have hBpoint (x : Coeff p) (m : ℤ) :
      Tendsto (fun n : ℤ => (A n x) m)
        (Filter.comap Int.natAbs Filter.atTop) (𝓝 ((B x) m)) := by
    have hproj : Tendsto (fun n : ℤ => (P (R n (Q x))) m)
        (Filter.comap Int.natAbs Filter.atTop)
        (𝓝 ((P (U (Q x))) m)) := by
      by_cases hm : m ∈ s
      · simpa [P, truncateCLM_apply, truncate_apply, hm] using
          hRpoint (Q x) m
      · simp [P, truncateCLM_apply, truncate_apply, hm]
    simpa [A, B, sub_apply,
      ContinuousLinearMap.comp_apply] using
      (hRpoint x m).sub hproj
  have hB : ‖B‖ ≤ ε / 4 := by
    apply opNorm_le_of_coordinatewise_limit
      (Filter.comap Int.natAbs Filter.atTop) A B (ε / 4) (by positivity)
    · filter_upwards [htail] with n hn
      exact le_of_lt hn
    · exact hBpoint
  have hblock := tendsto_finiteBlock_of_entries R U s t
    (fun m _ k _ => hRpoint (lp.single p k 1) m)
  have hblockevent := (Metric.tendsto_nhds.mp hblock) (ε / 4) (by positivity)
  filter_upwards [htail, hblockevent] with n hn hbn
  rw [dist_eq_norm] at hbn ⊢
  have htri : ‖T n - S‖ ≤ ‖A n‖ +
      ‖P.comp ((R n).comp Q) - P.comp (U.comp Q)‖ + ‖B‖ := by
    have hrewrite : T n - S = R n - U := by
      simp [R, U]
    rw [hrewrite]
    calc
      ‖R n - U‖ = ‖A n +
          (P.comp ((R n).comp Q) - P.comp (U.comp Q)) - B‖ := by
        congr 1
        simp [A, B]
      _ ≤ ‖A n‖ +
          ‖P.comp ((R n).comp Q) - P.comp (U.comp Q)‖ + ‖B‖ := by
        calc
          _ ≤ ‖A n + (P.comp ((R n).comp Q) - P.comp (U.comp Q))‖ +
              ‖B‖ := norm_sub_le _ _
          _ ≤ (‖A n‖ +
              ‖P.comp ((R n).comp Q) - P.comp (U.comp Q)‖) + ‖B‖ := by
                gcongr
                exact norm_add_le _ _
  have hfirst : ‖A n‖ < ε / 4 := hn
  have hmiddle : ‖P.comp ((R n).comp Q) - P.comp (U.comp Q)‖ < ε / 4 := hbn
  linarith

/-- The two-sided finite-block condition can be proved one side at a
time: an eventual common output cutoff and an eventual common input
cutoff for the remainders suffice. -/
theorem tendsto_operator_of_coordinatewise_and_separate_remainder_tails
    (T : ℤ → Coeff p →L[ℂ] Coeff p)
    (S D : Coeff p →L[ℂ] Coeff p)
    (hpoint : ∀ x : Coeff p, ∀ m : ℤ,
      Tendsto (fun n : ℤ => (T n x) m)
        (Filter.comap Int.natAbs Filter.atTop) (𝓝 ((S x) m)))
    (houtput : ∀ ε : ℝ, 0 < ε → ∃ s : Finset ℤ,
      ∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
        ‖(truncateCLM s).comp (T n - D) - (T n - D)‖ < ε)
    (hinput : ∀ ε : ℝ, 0 < ε → ∃ t : Finset ℤ,
      ∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
        ‖(T n - D).comp (truncateCLM t) - (T n - D)‖ < ε) :
    Tendsto T (Filter.comap Int.natAbs Filter.atTop) (𝓝 S) := by
  apply tendsto_operator_of_coordinatewise_and_eventual_remainder_finiteBlocks
    T S D hpoint
  intro ε hε
  obtain ⟨s,hs⟩ := houtput (ε / 2) (by positivity)
  obtain ⟨t,ht⟩ := hinput (ε / 2) (by positivity)
  refine ⟨s,t,?_⟩
  filter_upwards [hs,ht] with n hsn htn
  let R := T n - D
  let P := truncateCLM (p := p) s
  let Q := truncateCLM (p := p) t
  have hsplit : R - P.comp (R.comp Q) =
      (R - P.comp R) + P.comp (R - R.comp Q) := by
    ext x
    simp [ContinuousLinearMap.comp_apply]
  have hcomp : ‖P.comp (R - R.comp Q)‖ ≤ ‖R - R.comp Q‖ := by
    calc
      ‖P.comp (R - R.comp Q)‖ ≤ ‖P‖ * ‖R - R.comp Q‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖R - R.comp Q‖ := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right
            (norm_truncateCLM_le_one (p := p) s) (norm_nonneg _)
  have hfirst : ‖R - P.comp R‖ < ε / 2 := by
    rw [norm_sub_rev]
    exact hsn
  have hsecond : ‖R - R.comp Q‖ < ε / 2 := by
    rw [norm_sub_rev]
    exact htn
  change ‖R - P.comp (R.comp Q)‖ < ε
  rw [hsplit]
  calc
    ‖(R - P.comp R) + P.comp (R - R.comp Q)‖ ≤
        ‖R - P.comp R‖ + ‖P.comp (R - R.comp Q)‖ := norm_add_le _ _
    _ ≤ ‖R - P.comp R‖ + ‖R - R.comp Q‖ :=
      by gcongr
    _ < ε := by linarith

/-- The filter statement of two-sided operator convergence is exactly
the cutoff form used for deleted integer indices in Lemma 12.10. -/
theorem tendsto_operator_natAbs_iff
    (T : ℤ → Coeff p →L[ℂ] Coeff p)
    (S : Coeff p →L[ℂ] Coeff p) :
    Tendsto T (Filter.comap Int.natAbs Filter.atTop) (𝓝 S) ↔
      ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ n : ℤ,
        K ≤ n.natAbs → ‖T n - S‖ < ε := by
  constructor
  · intro h ε hε
    have hev := (Metric.tendsto_nhds.mp h) ε hε
    obtain ⟨K,hK⟩ := eventually_atTop.mp (eventually_comap.mp hev)
    refine ⟨K,?_⟩
    intro n hn
    simpa only [dist_eq_norm] using hK n.natAbs hn n rfl
  · intro h
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨K,hK⟩ := h ε hε
    apply eventually_comap.mpr
    apply eventually_atTop.mpr
    refine ⟨K,?_⟩
    intro j hj n heq
    simpa only [dist_eq_norm] using hK n (heq ▸ hj)

end NLS.Coeff
