import NLS.SequenceSpaces.Truncation
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
