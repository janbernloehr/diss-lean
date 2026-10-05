import NLS.ZakharovShabat.SourceFullAbelianGapComparison
import NLS.ZakharovShabat.SourceMomentRegularFactorization
import NLS.ZakharovShabat.SourcePsiFreeEquationFactorization

/-! # Free values of the regular factors in second moments -/
noncomputable section
open Set Metric Filter Topology Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The Cauchy quotient of the full primitive is exactly `i` at the free
source, including the filled center of the collapsed selected gap. -/
theorem SourceFullAbelianUniformCauchyFamily.quotient_zero_source
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (hzero : (0 : CoeffPair p) ∈ ball C.discs.source.val C.discs.sourceRadius)
    (k : ℤ) (z : ℂ) (hz : z ∈ ball (C.discs.center k) (C.discs.outer k)) :
    sourceFullAbelianCauchyQuotient hp hp1 W k (C.discs.center k) (C.discs.outer k) (z,0) =
      Complex.I := by
  obtain ⟨D⟩ := C.charts 0 hzero
  have hoff (w : ℂ) (hw : w ∈ ball (C.discs.center k) (C.discs.outer k))
      (hne : w ≠ (Real.pi : ℂ)*k) :
      sourceFullAbelianCauchyQuotient hp hp1 W k (C.discs.center k) (C.discs.outer k) (w,0) =
        Complex.I := by
    have hcut : w ∉ sourcePeriodicSegment hp hp1 (0 : CoeffPair p) k := by
      simpa only [sourcePeriodicSegment_zero_source, mem_singleton_iff] using hne
    have he := C.fullPrimitive_eq_cauchy k k 0 hzero w ⟨hw,hcut⟩
    rw [sourceFullAbelianPrimitive_zero_eq_I_mul_standardRoot D,
      sourceFullAbelianCauchyPrimitive] at he
    simp only [sub_self,mul_zero,add_zero] at he
    apply (mul_left_cancel₀ (sourceStandardRoot_ne_zero_off_segment hp hp1 0 k w hcut))
    exact he.symm.trans (mul_comm _ _)
  by_cases he : z = (Real.pi : ℂ)*k
  · have hlim := ((C.quotient_slice_analytic k 0 hzero z hz).continuousAt.tendsto).mono_left
      (show 𝓝[≠] z ≤ 𝓝 z from nhdsWithin_le_nhds)
    apply tendsto_nhds_unique hlim
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin,
      (show ball (C.discs.center k) (C.discs.outer k) ∈ 𝓝[≠] z from
        nhdsWithin_le_nhds (isOpen_ball.mem_nhds hz))] with w hw hwB
    exact (hoff w hwB (by simpa only [mem_compl_iff,mem_singleton_iff,he] using hw)).symm
  · exact hoff z hz he

/-- The free regular numerator at the selected center is diagonal in its
frequency index. This includes the filled numerator and denominator values. -/
theorem sourceMomentRegularNumerator_zero_freeCenter
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n k : ℤ) :
    sourceMomentRegularNumerator hp hp1 n k (0 : Coeff p) 0 ((Real.pi : ℂ)*k) =
      if k = n then Complex.I else 0 := by
  classical
  by_cases hkn : k = n
  · subst n
    rw [if_pos rfl,sourceMomentRegularNumerator_diagonal,
      sourceSingleRootQuotient_freeCenter_zero_eq_one,mul_one]
  · rw [if_neg hkn]
    unfold sourceMomentRegularNumerator
    rw [show sourcePsiCandidate n ((Real.pi : ℂ)*k,(0 : Coeff p)) = 0 from by
      simpa only [displacedRoots,lp.coeFn_zero,Pi.zero_apply,add_zero] using
        sourcePsiCandidate_other_root hp hp1 n k hkn (0 : Coeff p)]
    exact zero_div _

/-- Every actual isolating psi branch has zero deleted displacement at the
free source, independently of its choice of complex extension. -/
theorem SourcePsiIsolatingComplexExtension.branch_zero
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (hs : SourcePsiIsolatingComplexExtension hp hp1 V s) (n : ℤ) : s n 0 = 0 := by
  have he := hs.real_agreement n (⟨0,by simp [realTypeSourceLocus]⟩ : realTypeSourceLocus p)
  simpa only [sourcePsiGapRoot_zero] using he

end NLS.ZakharovShabat
