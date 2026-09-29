import NLS.SequenceSpaces.CompactPuncturedKernel
import NLS.SequenceSpaces.CompactRowMajorant
import NLS.SequenceSpaces.OperatorDiagonal

/-!
# Reciprocal matrix estimates on full coefficient spaces

A bounded operator on `ℓᵖ` has a finite matrix expansion. Reciprocal
bounds on one matrix row produce a conjugate-`ℓᵖ` row kernel, which
then gives a quantitative norm bound for operators whose output rows
are controlled by a common coefficient sequence.
-/

noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
  [p.HolderConjugate q]

/-- The finite matrix expansion of a bounded operator on `ℓᵖ`. -/
theorem operator_truncate_matrixExpansion
    (T : Coeff p →L[ℂ] Coeff p) (a : Coeff p)
    (m : ℤ) (s : Finset ℤ) :
    (T (truncate s a)) m =
      ∑ k ∈ s, a k * (T (lp.single p k 1)) m := by
  have hsingle (k : ℤ) :
      (lp.single p k (a k) : Coeff p) =
        a k • (lp.single p k (1 : ℂ) : Coeff p) := by
    ext r
    by_cases hrk : r = k
    · subst r
      simp
    · simp [hrk]
  have htrunc : truncate s a =
      ∑ k ∈ s, a k • (lp.single p k (1 : ℂ) : Coeff p) := by
    rw [truncate]
    simp_rw [hsingle]
  let L : Coeff p →L[ℂ] ℂ :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p m).comp T
  change L (truncate s a) = ∑ k ∈ s, a k * L (lp.single p k 1)
  rw [htrunc, map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [map_smul]
  rfl

/-- Finite matrix sums converge to each output coordinate. -/
theorem tendsto_operator_matrixSum (hp : p ≠ ⊤)
    (T : Coeff p →L[ℂ] Coeff p) (a : Coeff p) (m : ℤ) :
    Tendsto (fun s : Finset ℤ =>
      ∑ k ∈ s, a k * (T (lp.single p k 1)) m)
      atTop (𝓝 ((T a) m)) := by
  let L : Coeff p →L[ℂ] ℂ :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p m).comp T
  have ht := (L.continuous.tendsto a).comp (tendsto_truncate hp a)
  change Tendsto (fun s : Finset ℤ =>
    ∑ k ∈ s, a k * (T (lp.single p k 1)) m)
      atTop (𝓝 (L a))
  have hsum (s : Finset ℤ) :
      L (truncate s a) =
        ∑ k ∈ s, a k * (T (lp.single p k 1)) m :=
    operator_truncate_matrixExpansion T a m s
  simpa only [Function.comp_def, hsum] using ht

/-- A reciprocal matrix row has a conjugate-space kernel, with an
explicit norm bound independent of its output coordinate. -/
theorem exists_operator_rowKernel_of_reciprocalEntries
    (hp : p ≠ ⊤) (m : ℤ)
    (T : Coeff p →L[ℂ] Coeff p) (b : Coeff p)
    (hdiag : (T (lp.single p m 1)) m = 0)
    (hoff : ∀ k : ℤ, k ≠ m →
      ‖(T (lp.single p k 1)) m‖ ≤
        ‖b m‖ / |((k-m : ℤ) : ℝ)|) :
    ∃ row : Coeff q,
      ‖row‖ ≤ ‖b m‖ *
        ‖puncturedLattice q
          ((ENNReal.HolderConjugate.lt_top_iff_one_lt p q).mp hp.lt_top)‖ ∧
      ∀ a : Coeff p, (T a) m = dualPairing a row := by
  let hq : 1 < q :=
    (ENNReal.HolderConjugate.lt_top_iff_one_lt p q).mp hp.lt_top
  let c : Coeff q := puncturedLattice q hq
  let w : Coeff q := (‖b m‖ : ℂ) • shift m c
  have hw (k : ℤ) : ‖w k‖ =
      ‖b m‖ * (if k = m then 0 else |((k-m : ℤ) : ℝ)|⁻¹) := by
    simp only [w,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,norm_mul,
      Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg (b m))]
    exact congrArg (‖b m‖ * ·)
      (norm_shift_puncturedLattice_apply hq m k)
  have hpoint (k : ℤ) :
      ‖(T (lp.single p k 1)) m‖ ≤ ‖w k‖ := by
    rw [hw]
    by_cases hkm : k = m
    · subst k
      simp [hdiag]
    · rw [if_neg hkm]
      simpa only [div_eq_mul_inv] using hoff k hkm
  have hmem : Memℓp (fun k : ℤ => (T (lp.single p k 1)) m) q :=
    (lp.memℓp w).mono' hpoint
  let row : Coeff q := ⟨fun k => (T (lp.single p k 1)) m,hmem⟩
  have hrowBound : ‖row‖ ≤ ‖b m‖ * ‖c‖ := by
    calc
      ‖row‖ ≤ ‖w‖ :=
        lp.norm_mono (zero_lt_one.trans_le Fact.out).ne' hpoint
      _ = ‖b m‖ * ‖c‖ := by
        rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,
          abs_of_nonneg (norm_nonneg (b m)),norm_shift]
  refine ⟨row,hrowBound,?_⟩
  intro a
  have hmatrix := tendsto_operator_matrixSum hp T a m
  have hsum : Summable (fun k : ℤ => a k * row k) :=
    (summable_norm_dualPairing a row).of_norm
  have hpair : Tendsto (fun s : Finset ℤ =>
      ∑ k ∈ s, a k * row k) atTop
        (𝓝 (dualPairing a row)) := by
    rw [dualPairing_apply]
    exact hsum.hasSum
  have hsame : (fun s : Finset ℤ =>
      ∑ k ∈ s, a k * row k) =
      (fun s : Finset ℤ =>
        ∑ k ∈ s, a k * (T (lp.single p k 1)) m) := rfl
  rw [hsame] at hpair
  exact tendsto_nhds_unique hmatrix hpair

/-- A full-space reciprocal matrix estimate gives a quantitative
operator norm bound. -/
theorem norm_operator_le_of_reciprocalEntries
    (hp : p ≠ ⊤)
    (T : Coeff p →L[ℂ] Coeff p) (b : Coeff p)
    (hdiag : ∀ m : ℤ, (T (lp.single p m 1)) m = 0)
    (hoff : ∀ m k : ℤ, k ≠ m →
      ‖(T (lp.single p k 1)) m‖ ≤
        ‖b m‖ / |((k-m : ℤ) : ℝ)|) :
    ‖T‖ ≤ ‖b‖ *
      ‖puncturedLattice q
        ((ENNReal.HolderConjugate.lt_top_iff_one_lt p q).mp hp.lt_top)‖ := by
  let c : Coeff q := puncturedLattice q
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p q).mp hp.lt_top)
  let B : Coeff p := (‖c‖ : ℂ) • b
  have hrow (m : ℤ) (a : Coeff p) :
      ‖T a m‖ ≤ ‖B m‖ * ‖a‖ := by
    obtain ⟨row,hbound,hrep⟩ :=
      exists_operator_rowKernel_of_reciprocalEntries (q := q)
        hp m T b (hdiag m) (hoff m)
    have hB : ‖B m‖ = ‖c‖ * ‖b m‖ := by
      simp only [B,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,norm_mul,
        Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg c)]
    rw [hrep a,hB]
    calc
      ‖dualPairing a row‖ ≤ ‖a‖ * ‖row‖ := norm_dualPairing_le _ _
      _ ≤ ‖a‖ * (‖b m‖ * ‖c‖) :=
        mul_le_mul_of_nonneg_left hbound (norm_nonneg a)
      _ = (‖c‖ * ‖b m‖) * ‖a‖ := by ring
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro a
  have hglobal := norm_truncate_operator_sub_le_rowTail T B hrow ∅ a
  have hBnorm : ‖B‖ = ‖c‖ * ‖b‖ := by
    rw [show B = (‖c‖ : ℂ) • b from rfl, norm_smul,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg c)]
  simpa only [truncate_empty, zero_sub, norm_neg, hBnorm, mul_comm]
    using hglobal

/-- The high-output, high-input block of a zero-diagonal operator is
small when its reciprocal off-diagonal entries share a fixed `ℓᵖ`
row majorant. The bound depends only on the output tail of that
majorant. -/
theorem norm_twoSidedTail_le_of_reciprocalEntries
    (hp : p ≠ ⊤)
    (T : Coeff p →L[ℂ] Coeff p) (b : Coeff p)
    (s t : Finset ℤ)
    (hdiag : ∀ m : ℤ, m ∉ s → m ∉ t →
      (T (lp.single p m 1)) m = 0)
    (hoff : ∀ m : ℤ, m ∉ s → ∀ k : ℤ, k ∉ t → k ≠ m →
      ‖(T (lp.single p k 1)) m‖ ≤
        ‖b m‖ / |((k-m : ℤ) : ℝ)|) :
    ‖(ContinuousLinearMap.id ℂ (Coeff p) - truncateCLM s).comp
        (T.comp (ContinuousLinearMap.id ℂ (Coeff p) - truncateCLM t))‖ ≤
      ‖b - truncate s b‖ *
        ‖puncturedLattice q
          ((ENNReal.HolderConjugate.lt_top_iff_one_lt p q).mp hp.lt_top)‖ := by
  let H : Coeff p →L[ℂ] Coeff p :=
    (ContinuousLinearMap.id ℂ (Coeff p) - truncateCLM s).comp
      (T.comp (ContinuousLinearMap.id ℂ (Coeff p) - truncateCLM t))
  let bTail : Coeff p := b - truncate s b
  have hsingle (k : ℤ) :
      ((ContinuousLinearMap.id ℂ (Coeff p) - truncateCLM (p := p) t)
        (lp.single p k 1)) =
          if k ∈ t then 0 else lp.single p k 1 := by
    ext j
    by_cases hkt : k ∈ t <;> by_cases hjk : j = k <;>
      simp [hkt,hjk,lp.single_apply,truncate_apply]
  have hentry (m k : ℤ) :
      (H (lp.single p k 1)) m =
        if m ∈ s then 0 else
          if k ∈ t then 0 else (T (lp.single p k 1)) m := by
    simp only [H,ContinuousLinearMap.comp_apply,hsingle]
    by_cases hkt : k ∈ t
    · simp [hkt]
    · simp [hkt]
      by_cases hms : m ∈ s <;> simp [hms]
  have hbTail (m : ℤ) :
      ‖bTail m‖ = if m ∈ s then 0 else ‖b m‖ := by
    by_cases hms : m ∈ s <;> simp [bTail,hms,truncate_apply]
  have hHdiag (m : ℤ) : (H (lp.single p m 1)) m = 0 := by
    rw [hentry]
    by_cases hms : m ∈ s
    · simp [hms]
    · by_cases hmt : m ∈ t
      · simp [hms,hmt]
      · simpa [hms,hmt] using hdiag m hms hmt
  have hHoff (m k : ℤ) (hkm : k ≠ m) :
      ‖(H (lp.single p k 1)) m‖ ≤
        ‖bTail m‖ / |((k-m : ℤ) : ℝ)| := by
    rw [hentry,hbTail]
    by_cases hms : m ∈ s
    · simp [hms]
    · by_cases hkt : k ∈ t
      · simp only [if_neg hms,if_pos hkt,norm_zero]
        exact div_nonneg (norm_nonneg (b m)) (abs_nonneg _)
      · simpa [hms,hkt] using hoff m hms k hkt hkm
  exact norm_operator_le_of_reciprocalEntries (q := q)
    hp H bTail hHdiag hHoff

/-- The tail estimate applies to the canonical off-diagonal piece of
any bounded operator, without imposing an assumption on its diagonal. -/
theorem norm_twoSidedTail_offDiagonal_le_of_reciprocalEntries
    (hp : p ≠ ⊤)
    (T : Coeff p →L[ℂ] Coeff p) (b : Coeff p)
    (s t : Finset ℤ)
    (hoff : ∀ m : ℤ, m ∉ s → ∀ k : ℤ, k ∉ t → k ≠ m →
      ‖(T (lp.single p k 1)) m‖ ≤
        ‖b m‖ / |((k-m : ℤ) : ℝ)|) :
    ‖(ContinuousLinearMap.id ℂ (Coeff p) - truncateCLM s).comp
        ((operatorOffDiagonal T).comp
          (ContinuousLinearMap.id ℂ (Coeff p) - truncateCLM t))‖ ≤
      ‖b - truncate s b‖ *
        ‖puncturedLattice q
          ((ENNReal.HolderConjugate.lt_top_iff_one_lt p q).mp hp.lt_top)‖ := by
  apply norm_twoSidedTail_le_of_reciprocalEntries (q := q)
    hp (operatorOffDiagonal T) b s t
  · intro m _ _
    exact operatorOffDiagonal_diagonal T m
  · intro m hm k hk hkm
    rw [operatorOffDiagonal_entry_other T m k hkm.symm]
    exact hoff m hm k hk hkm

/-- One pair of cutoffs makes the off-diagonal high/high block small
for every operator with the same tail-entry majorant. This uniformity
is needed when the deleted index of the psi Jacobian varies. -/
theorem exists_uniform_twoSidedTail_cutoffs_of_reciprocalEntries
    (q : ℝ≥0∞) [Fact (1 ≤ q)] [p.HolderConjugate q]
    (hp : p ≠ ⊤) (b : Coeff p) (Krow Kcol : ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ s t : Finset ℤ, ∀ T : Coeff p →L[ℂ] Coeff p,
      (∀ m k : ℤ, Krow ≤ m.natAbs → Kcol ≤ k.natAbs → k ≠ m →
        ‖(T (lp.single p k 1)) m‖ ≤
          ‖b m‖ / |((k-m : ℤ) : ℝ)|) →
      ‖(ContinuousLinearMap.id ℂ (Coeff p) - truncateCLM s).comp
        ((operatorOffDiagonal T).comp
          (ContinuousLinearMap.id ℂ (Coeff p) - truncateCLM t))‖ < ε := by
  classical
  let C : ℝ := ‖puncturedLattice q
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p q).mp hp.lt_top)‖
  have hC : 0 ≤ C := norm_nonneg _
  obtain ⟨u,hu⟩ := Metric.tendsto_atTop.mp (tendsto_truncate hp b)
    (ε / (C+1)) (by positivity)
  let s : Finset ℤ := u ∪ Finset.Icc (-(Krow : ℤ)) (Krow : ℤ)
  let t : Finset ℤ := Finset.Icc (-(Kcol : ℤ)) (Kcol : ℤ)
  have htail : ‖b - truncate s b‖ < ε / (C+1) := by
    have hs : u ⊆ s := Finset.subset_union_left
    have h := hu s hs
    rw [dist_eq_norm,norm_sub_rev] at h
    exact h
  refine ⟨s,t,?_⟩
  intro T hentry
  have hbound := norm_twoSidedTail_offDiagonal_le_of_reciprocalEntries
    (q := q) hp T b s t (by
      intro m hm k hk hkm
      have hmK : Krow ≤ m.natAbs := by
        have hmhead : m ∉ Finset.Icc (-(Krow : ℤ)) (Krow : ℤ) := by
          intro hmem
          exact hm (Finset.mem_union_right u hmem)
        simp only [Finset.mem_Icc] at hmhead
        omega
      have hkK : Kcol ≤ k.natAbs := by
        simp only [t,Finset.mem_Icc] at hk
        omega
      exact hentry m k hmK hkK hkm)
  have hprod : ‖b - truncate s b‖ * (C+1) < ε := by
    have h := mul_lt_mul_of_pos_right htail (by positivity : 0 < C+1)
    rwa [div_mul_cancel₀ ε (by positivity : C+1 ≠ 0)] at h
  exact hbound.trans_lt ((mul_le_mul_of_nonneg_left
    (by linarith : C ≤ C+1) (norm_nonneg _)).trans_lt hprod)

end NLS.Coeff
