import NLS.ZakharovShabat.CriticalMidpointGapSquared
import NLS.ZakharovShabat.SourcePeriodicGapSummability
import NLS.ZakharovShabat.CanonicalCriticalFree
import NLS.ZakharovShabat.DeletedPeriodicFree

/-!
# Lemma 8.6: critical-point midpoint offsets are quadratic in the gap

For every finite p > 1, one original open convex source neighborhood and
one positive cutoff give a uniformly bounded actual ℓp coefficient sequence.
Outside that cutoff, the canonical critical-point midpoint offset equals
the squared gap times this coefficient. The denominator is bounded away
from zero, and collapsed complex gaps require no division by the gap.

The deleted product has the literal normalization of printed p. 51.
Consequently its midpoint factorization has prefactor -4. The printed +4
is refuted at the free source; this correction leaves Lemma 8.6 intact.
-/

noncomputable section
open Set Filter
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual deleted-derivative quotient on the tail, extended by zero centrally. -/
def sourceCriticalGapTailCoefficient (hp : p ≠ ⊤) (hp1 : 1 < p)
    (N : ℕ) (φ : CoeffPair p) : Coeff p :=
  ⟨fun n => if N < n.natAbs then canonicalCriticalGapQuotient hp hp1
      (periodOnePotential φ) (periodOnePotential_mem φ) n else 0,
    (memℓp_canonicalCriticalGapQuotient hp hp1 _ (periodOnePotential_mem φ)).mono' (by
      intro n
      split_ifs <;> simp)⟩

/-- The literal coefficient, with its full denominator exposed. -/
@[simp] theorem sourceCriticalGapTailCoefficient_apply (hp : p ≠ ⊤) (hp1 : 1 < p)
    (N : ℕ) (φ : CoeffPair p) (n : ℤ) :
    sourceCriticalGapTailCoefficient hp hp1 N φ n = if N < n.natAbs then
      canonicalDeletedCriticalDerivative hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n /
        (4*canonicalCriticalOffsetCoefficient hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n) else 0 := rfl

/-- The finite central extension is exactly zero. -/
@[simp] theorem sourceCriticalGapTailCoefficient_central (hp : p ≠ ⊤) (hp1 : 1 < p)
    (N : ℕ) (φ : CoeffPair p) (n : ℤ) (hn : n.natAbs ≤ N) :
    sourceCriticalGapTailCoefficient hp hp1 N φ n = 0 := by
  rw [sourceCriticalGapTailCoefficient_apply,if_neg (not_lt.mpr hn)]

/-- Uniform original-source data for the squared-gap estimate. -/
structure SourceLemma8_6Data (hp : p ≠ ⊤) (hp1 : 1 < p)
    (U : Set (CoeffPair p)) (N : ℕ) (K : ℝ) : Prop where
  coefficient_norm : ∀ ψ ∈ U, ‖sourceCriticalGapTailCoefficient hp hp1 N ψ‖ ≤ K
  denominator_lower_bound : ∀ ψ ∈ U, ∀ n : ℤ, N < n.natAbs →
    1 ≤ ‖canonicalCriticalOffsetCoefficient hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n‖
  offset : ∀ ψ ∈ U, ∀ n : ℤ, N < n.natAbs →
    canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-
      canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n =
        (sourcePeriodicGapDisplacement hp hp1 ψ n)^2*sourceCriticalGapTailCoefficient hp hp1 N ψ n

/-- Lemma 8.6 on one original neighborhood of each arbitrary complex source. -/
theorem sourceLemma8_6 (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ N : ℕ, 0 < N ∧ ∃ U : Set (CoeffPair p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∃ K : ℝ, 0 ≤ K ∧ SourceLemma8_6Data hp hp1 U N K := by
  obtain ⟨Na,hNa,A,hAo,hAc,hAφ,hA0,K,hK,ha⟩ :=
    exists_uniform_critical_midpoint_gap_sq_lp hp hp1 (periodOnePotential φ)
  obtain ⟨Nb,_,B,hBo,hBc,hBφ,hB0,hb⟩ :=
    exists_uniform_criticalOffsetCoefficient_lower_bound hp hp1 (periodOnePotential φ)
  let N := max Na Nb
  let U : Set (CoeffPair p) := periodOnePotential ⁻¹' (A ∩ B)
  refine ⟨N,hNa.trans_le (le_max_left _ _),U,
    (hAo.inter hBo).preimage (periodOnePotential (p := p)).continuous,
    (hAc.inter hBc).linear_preimage ((periodOnePotential (p := p)).restrictScalars ℝ).toLinearMap,
    ⟨hAφ,hBφ⟩,?_,K,hK,?_⟩
  · simpa only [U,mem_preimage,map_zero,mem_inter_iff] using (show (0 : PairSpace p) ∈ A ∧ 0 ∈ B from ⟨hA0,hB0⟩)
  · refine ⟨?_,?_,?_⟩
    · intro ψ hψ
      obtain ⟨a,haK,hea⟩ := ha _ hψ.1 (periodOnePotential_mem ψ)
      have hd (n : ℤ) : ‖sourceCriticalGapTailCoefficient hp hp1 N ψ n‖ ≤ ‖a n‖ := by
        by_cases hn : N < n.natAbs
        · have hn' : Na < n.natAbs := (le_max_left _ _).trans_lt hn
          have he : sourceCriticalGapTailCoefficient hp hp1 N ψ n = a n := by
            rw [(hea n hn').1,sourceCriticalGapTailCoefficient_apply,if_pos hn]
            rfl
          rw [he]
        · simp only [sourceCriticalGapTailCoefficient_apply,if_neg hn,norm_zero]
          exact norm_nonneg _
      exact (lp.norm_mono ((zero_lt_one.trans hp1).ne') hd).trans haK
    · intro ψ hψ n hn
      exact hb _ hψ.2 (periodOnePotential_mem ψ) n ((le_max_right _ _).trans_lt hn)
    · intro ψ hψ n hn
      obtain ⟨a,_,hea⟩ := ha _ hψ.1 (periodOnePotential_mem ψ)
      have he := hea n ((le_max_left _ _).trans_lt hn)
      have ht : sourceCriticalGapTailCoefficient hp hp1 N ψ n = a n := by
        rw [he.1,sourceCriticalGapTailCoefficient_apply,if_pos hn]
        rfl
      simpa only [ht,canonicalCriticalMidpointOffset_apply,sourcePeriodicGapDisplacement_apply] using he.2

/-- The tail coefficient uses an ordinary nonzero denominator. -/
theorem SourceLemma8_6Data.denominator_ne_zero {hp : p ≠ ⊤} {hp1 : 1 < p}
    {U : Set (CoeffPair p)} {N : ℕ} {K : ℝ} (D : SourceLemma8_6Data hp hp1 U N K)
    (ψ : CoeffPair p) (hψ : ψ ∈ U) (n : ℤ) (hn : N < n.natAbs) :
    4*canonicalCriticalOffsetCoefficient hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0 :=
  mul_ne_zero (by norm_num) (norm_pos_iff.mp (zero_lt_one.trans_le (D.denominator_lower_bound ψ hψ n hn)))

/-- A collapsed distant complex gap has its critical point at its midpoint. -/
theorem SourceLemma8_6Data.collapsed_gap {hp : p ≠ ⊤} {hp1 : 1 < p}
    {U : Set (CoeffPair p)} {N : ℕ} {K : ℝ} (D : SourceLemma8_6Data hp hp1 U N K)
    (ψ : CoeffPair p) (hψ : ψ ∈ U) (n : ℤ) (hn : N < n.natAbs)
    (hgap : sourcePeriodicGapDisplacement hp hp1 ψ n = 0) :
    canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n =
      canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n := by
  have h := D.offset ψ hψ n hn
  rw [hgap,zero_pow (by norm_num),zero_mul] at h
  exact sub_eq_zero.mp h

/-- A uniform quadratic bound for the actual midpoint offset. -/
theorem SourceLemma8_6Data.norm_offset_le {hp : p ≠ ⊤} {hp1 : 1 < p}
    {U : Set (CoeffPair p)} {N : ℕ} {K : ℝ} (D : SourceLemma8_6Data hp hp1 U N K)
    (ψ : CoeffPair p) (hψ : ψ ∈ U) (n : ℤ) (hn : N < n.natAbs) :
    ‖canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-
      canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n‖ ≤
        ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖^2*K := by
  rw [D.offset ψ hψ n hn,norm_mul,norm_pow]
  exact mul_le_mul_of_nonneg_left
    ((lp.norm_apply_le_norm ((zero_lt_one.trans hp1).ne') _ n).trans (D.coefficient_norm ψ hψ)) (sq_nonneg _)

/-- The literal deleted product converges on the entire spectral plane, including removed roots. -/
theorem sourceDeletedPeriodicProduct_formula (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (n : ℤ) :
    TendstoLocallyUniformlyOn
      (fun (M : ℕ) (z : ℂ) =>
        (∏ m ∈ (Finset.Icc (-(M : ℤ)) M).erase n,
          (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) m-z)*
          (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) m-z)/
          (if m = 0 then 1 else ((Real.pi : ℂ)*m)^2))/
          (if n = 0 then 1 else ((Real.pi : ℂ)*n)^2))
      (canonicalDeletedPeriodicProduct hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n)
      atTop univ := by
  have h := tendstoLocallyUniformlyOn_deletedSpectralPairProduct hp
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ))
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ))
      (canonicalPeriodicEndpoints_spec hp hp1 _ (periodOnePotential_mem φ)).1.left_displacement
      (canonicalPeriodicEndpoints_spec hp hp1 _ (periodOnePotential_mem φ)).1.right_displacement n
  unfold deletedSpectralPairPartialProduct at h
  simpa only [canonicalDeletedPeriodicProduct,spectralPairFactor_eq_div,spectralPairDenominator] using h

/-- The midpoint factorization with the corrected prefactor -4. -/
theorem sourceDiscriminant_midpoint_factorization (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (n : ℤ) (z : ℂ) :
    (canonicalDiscriminant hp (periodOnePotential φ) z)^2-4 =
      -4*((canonicalPeriodicMidpoint hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n-z)^2-
        (sourcePeriodicGapDisplacement hp hp1 φ n)^2/4)*
        canonicalDeletedPeriodicProduct hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n z := by
  simpa only [sourcePeriodicGapDisplacement_apply,sub_sq_comm] using
    canonicalDiscriminant_sq_sub_four_eq_midpoint_mul hp hp1 _ (periodOnePotential_mem φ) n z

/-- The printed +4 factorization fails at zero potential and spectral value π/2. -/
theorem sourceLemma8_6_printed_factorization_false (hp : p ≠ ⊤) (hp1 : 1 < p) :
    (canonicalDiscriminant hp (periodOnePotential (0 : CoeffPair p)) ((Real.pi : ℂ)/2))^2-4 ≠
      4*((canonicalPeriodicMidpoint hp hp1 (periodOnePotential (0 : CoeffPair p)) (periodOnePotential_mem 0) 0-
        (Real.pi : ℂ)/2)^2-(sourcePeriodicGapDisplacement hp hp1 (0 : CoeffPair p) 0)^2/4)*
        canonicalDeletedPeriodicProduct hp hp1 (periodOnePotential (0 : CoeffPair p)) (periodOnePotential_mem 0) 0 ((Real.pi : ℂ)/2) := by
  intro hbad
  have hgood := sourceDiscriminant_midpoint_factorization hp hp1 (0 : CoeffPair p) 0 ((Real.pi : ℂ)/2)
  have hzero : canonicalDiscriminant hp (periodOnePotential (0 : CoeffPair p)) ((Real.pi : ℂ)/2) = 0 := by
    simp only [map_zero,canonicalDiscriminant_zero_finite,freeDiscriminant,Complex.cos_pi_div_two,mul_zero]
  rw [hzero] at hbad hgood
  have h : (-8 : ℂ) = 0 := by linear_combination hbad+hgood
  norm_num at h

/-- The actual coefficient sequence vanishes at zero potential for every cutoff. -/
@[simp] theorem sourceCriticalGapTailCoefficient_zero (hp : p ≠ ⊤) (hp1 : 1 < p) (N : ℕ) :
    sourceCriticalGapTailCoefficient hp hp1 N (0 : CoeffPair p) = 0 := by
  ext n
  rw [sourceCriticalGapTailCoefficient_apply]
  split_ifs
  · have he : canonicalDeletedPeriodicProduct hp hp1 (periodOnePotential (0 : CoeffPair p))
          (periodOnePotential_mem 0) n = (fun z => (freeSineQuotient n z)^2) := by
      funext z
      simpa only [map_zero] using congrFun (canonicalDeletedPeriodicProduct_zero (p := p) hp hp1 n) z
    simp only [canonicalDeletedCriticalDerivative,he,map_zero,canonicalCriticalPoints_zero,
      deriv_freeSineQuotient_sq_center,zero_div,lp.coeFn_zero,Pi.zero_apply]
  · rfl

end NLS.ZakharovShabat
