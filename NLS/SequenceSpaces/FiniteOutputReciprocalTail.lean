import NLS.SequenceSpaces.FullReciprocalMatrixTail
import NLS.SequenceSpaces.FiniteBlockOperatorConvergence

/-!
# Uniform input tails on finitely many output rows

Reciprocal matrix decay gives summable conjugate-space kernels.
Truncating those kernels controls all high input frequencies at once,
uniformly over every operator satisfying the same finite-row bounds.
-/

noncomputable section
open Filter Topology
open scoped ENNReal BigOperators
namespace NLS.Coeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
  [p.HolderConjugate q]

/-- A summable majorant for one matrix row gives its conjugate-space
representation, with a quantitative kernel norm bound. -/
theorem exists_operator_rowKernel_of_entryMajorant
    (hp : p ≠ ⊤) (T : Coeff p →L[ℂ] Coeff p) (m : ℤ)
    (g : Coeff q)
    (hentry : ∀ k : ℤ, ‖(T (lp.single p k 1)) m‖ ≤ ‖g k‖) :
    ∃ row : Coeff q, ‖row‖ ≤ ‖g‖ ∧
      ∀ x : Coeff p, (T x) m = dualPairing x row := by
  let row : Coeff q := ⟨fun k => (T (lp.single p k 1)) m,
    (lp.memℓp g).mono' hentry⟩
  refine ⟨row,lp.norm_mono (zero_lt_one.trans_le Fact.out).ne' hentry,?_⟩
  intro x
  have hmatrix := tendsto_operator_matrixSum hp T x m
  have hsum : Summable (fun k : ℤ => x k*row k) :=
    (summable_norm_dualPairing x row).of_norm
  have hpair : Tendsto (fun s : Finset ℤ => ∑ k ∈ s, x k*row k)
      atTop (𝓝 (dualPairing x row)) := by
    rw [dualPairing_apply]
    exact hsum.hasSum
  exact tendsto_nhds_unique hmatrix hpair

/-- Finitely many reciprocally bounded output rows share one input
cutoff for every operator with those bounds. The estimate is uniform
over the operator family, including all high input frequencies. -/
theorem exists_uniform_finiteOutput_inputTail_cutoff_of_reciprocalEntries
    (q : ℝ≥0∞) [Fact (1 ≤ q)] [p.HolderConjugate q]
    (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (s : Finset ℤ) (K : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ t : Finset ℤ, ∀ T : Coeff p →L[ℂ] Coeff p,
      (∀ m ∈ s, ∀ k : ℤ, K ≤ k.natAbs → k ≠ m →
        ‖(T (lp.single p k 1)) m‖ ≤ C/|((k-m : ℤ) : ℝ)|) →
      ‖(truncateCLM s).comp
        (T.comp (ContinuousLinearMap.id ℂ (Coeff p) - truncateCLM t))‖ < ε := by
  classical
  let hq1 : 1 < q := (ENNReal.HolderConjugate.lt_top_iff_one_lt p q).mp hp.lt_top
  let c : Coeff q := puncturedLattice q hq1
  let g (m : ℤ) : Coeff q := (C : ℂ) • shift m c
  have htail (m : ℤ) : Tendsto (fun t : Finset ℤ => ‖g m-truncate t (g m)‖)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [sub_self,norm_zero] using
      (tendsto_const_nhds (x := g m)).sub (tendsto_truncate hq (g m)) |>.norm
  have hsum := tendsto_finsetSum s (fun m _ => htail m)
  have hsumZero : Tendsto (fun t : Finset ℤ => ∑ m ∈ s, ‖g m-truncate t (g m)‖)
      atTop (𝓝 (0 : ℝ)) := by simpa using hsum
  have hsmall : ∀ᶠ t : Finset ℤ in atTop,
      ∑ m ∈ s, ‖g m-truncate t (g m)‖ < ε :=
    hsumZero.eventually_lt_const hε
  obtain ⟨u,hu⟩ := eventually_atTop.mp hsmall
  let t : Finset ℤ := u ∪ s ∪ Finset.Icc (-(K : ℤ)) (K : ℤ)
  have hut : u ⊆ t := Finset.subset_union_left.trans Finset.subset_union_left
  have hst : s ⊆ t := Finset.subset_union_right.trans Finset.subset_union_left
  have hKt : Finset.Icc (-(K : ℤ)) (K : ℤ) ⊆ t := Finset.subset_union_right
  have htSmall := hu t hut
  refine ⟨t,?_⟩
  intro T hentry
  let A : Coeff p →L[ℂ] Coeff p :=
    T.comp (ContinuousLinearMap.id ℂ (Coeff p) - truncateCLM t)
  have hsingle (k : ℤ) :
      (ContinuousLinearMap.id ℂ (Coeff p) - truncateCLM (p := p) t) (lp.single p k 1) =
        if k ∈ t then 0 else lp.single p k 1 := by
    ext j
    by_cases hk : k ∈ t <;> by_cases hj : j = k <;>
      simp [hk,hj,lp.single_apply,truncate_apply]
  have hrow (m : ℤ) (hm : m ∈ s) : ∀ k : ℤ,
      ‖(A (lp.single p k 1)) m‖ ≤ ‖(g m-truncate t (g m)) k‖ := by
    intro k
    simp only [A,ContinuousLinearMap.comp_apply,hsingle]
    by_cases hk : k ∈ t
    · simp [hk]
    · have hkK : K ≤ k.natAbs := by
        have hnot : k ∉ Finset.Icc (-(K : ℤ)) (K : ℤ) := fun h => hk (hKt h)
        simp only [Finset.mem_Icc] at hnot
        omega
      have hkm : k ≠ m := by
        intro heq
        subst k
        exact hk (hst hm)
      have hg : ‖g m k‖ = C/|((k-m : ℤ) : ℝ)| := by
        simp only [g,c,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,norm_mul,
          Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hC,
          norm_shift_puncturedLattice_apply hq1 m k,if_neg hkm,div_eq_mul_inv]
      simpa only [if_neg hk,lp.coeFn_sub,Pi.sub_apply,truncate_apply,
        if_neg hk,sub_zero,hg] using hentry m hm k hkK hkm
  have hvalue (m : ℤ) (hm : m ∈ s) (x : Coeff p) :
      ‖A x m‖ ≤ ‖g m-truncate t (g m)‖*‖x‖ := by
    obtain ⟨row,hrnorm,hr⟩ :=
      exists_operator_rowKernel_of_entryMajorant hp A m _ (hrow m hm)
    rw [hr x]
    calc
      ‖dualPairing x row‖ ≤ ‖x‖*‖row‖ := norm_dualPairing_le x row
      _ ≤ ‖x‖*‖g m-truncate t (g m)‖ :=
        mul_le_mul_of_nonneg_left hrnorm (norm_nonneg _)
      _ = _ := mul_comm _ _
  have hbound : ‖(truncateCLM s).comp A‖ ≤ ∑ m ∈ s, ‖g m-truncate t (g m)‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
    intro x
    change ‖truncate s (A x)‖ ≤ _
    calc
      ‖truncate s (A x)‖ ≤ ∑ m ∈ s, ‖(lp.single p m (A x m) : Coeff p)‖ :=
        norm_sum_le _ _
      _ = ∑ m ∈ s, ‖A x m‖ := by simp only [lp.norm_single (zero_lt_one.trans_le Fact.out)]
      _ ≤ ∑ m ∈ s, ‖g m-truncate t (g m)‖*‖x‖ :=
        Finset.sum_le_sum (fun m hm => hvalue m hm x)
      _ = _ := (Finset.sum_mul _ _ _).symm
  exact hbound.trans_lt htSmall

/-- Coordinatewise limits and uniform input cutoffs give operator-norm
convergence after any fixed finite output projection. -/
theorem tendsto_finiteOutputs_of_coordinatewise_and_uniformInputTails
    (T : ℤ → Coeff p →L[ℂ] Coeff p) (Q : Coeff p →L[ℂ] Coeff p)
    (s : Finset ℤ)
    (hpoint : ∀ x : Coeff p, ∀ m : ℤ,
      Tendsto (fun n : ℤ => (T n x) m)
        (Filter.comap Int.natAbs Filter.atTop) (𝓝 ((Q x) m)))
    (htail : ∀ ε : ℝ, 0 < ε → ∃ t : Finset ℤ,
      ∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
        ‖(truncateCLM s).comp
          ((T n).comp (ContinuousLinearMap.id ℂ (Coeff p) - truncateCLM t))‖ < ε) :
    Tendsto (fun n : ℤ => (truncateCLM s).comp (T n))
      (Filter.comap Int.natAbs Filter.atTop) (𝓝 ((truncateCLM s).comp Q)) := by
  let A (n : ℤ) : Coeff p →L[ℂ] Coeff p := (truncateCLM s).comp (T n)
  let B : Coeff p →L[ℂ] Coeff p := (truncateCLM s).comp Q
  have hpoint' (x : Coeff p) (m : ℤ) :
      Tendsto (fun n : ℤ => (A n x) m)
        (Filter.comap Int.natAbs Filter.atTop) (𝓝 ((B x) m)) := by
    by_cases hm : m ∈ s
    · simpa [A,B,truncate_apply,hm] using hpoint x m
    · simpa [A,B,truncate_apply,hm] using
        (tendsto_const_nhds (x := (0 : ℂ)) :
          Tendsto (fun _n : ℤ => (0 : ℂ))
            (Filter.comap Int.natAbs Filter.atTop) (𝓝 0))
  apply tendsto_operator_of_coordinatewise_and_eventual_remainder_finiteBlocks A B 0 hpoint'
  intro ε hε
  obtain ⟨t,ht⟩ := htail ε hε
  refine ⟨s,t,?_⟩
  filter_upwards [ht] with n hn
  have heq : A n-(truncateCLM s).comp ((A n).comp (truncateCLM t)) =
      (truncateCLM s).comp
        ((T n).comp (ContinuousLinearMap.id ℂ (Coeff p) - truncateCLM t)) := by
    ext x
    simp [A]
  simpa only [sub_zero,heq] using hn

end NLS.Coeff
