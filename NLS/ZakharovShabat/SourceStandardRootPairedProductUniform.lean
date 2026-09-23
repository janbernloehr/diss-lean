import NLS.ZakharovShabat.SourceStandardRootPairedProductAnalytic
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Topology.MetricSpace.Algebra

/-!
# Uniform estimates for paired standard-root products

The normalized single-factor error is uniformly `O(1/|k|)` on bounded
spectral regions and source neighborhoods. Its quadratic contribution to
the paired product therefore has a summable `O(1/k²)` bound.
-/

noncomputable section
open Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The single-factor error is `O(1/|k|)` whenever the square-root
remainder has its quadratic tail bound. -/
theorem norm_sourceStandardRootRelativeError_le_reciprocal
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (z : ℂ) (k : ℤ)
    (M R C : ℝ) (hk : k ≠ 0)
    (hM : ‖sourcePeriodicMidpointDisplacement hp hp1 ψ‖ ≤ M)
    (hR : ‖z‖ ≤ R) (hC : 0 ≤ C)
    (hr : ‖sourceStandardRootSqrtCorrection hp hp1 ψ z k‖ ≤
      C * |(k : ℝ)| ^ (-(2 : ℝ))) :
    ‖sourceStandardRootRelativeError hp hp1 ψ k z‖ ≤
      ((M+R)/Real.pi+C) / |(k : ℝ)| := by
  let q : ℝ := |(k : ℝ)|
  have hq : 1 ≤ q := by
    dsimp [q]
    exact_mod_cast Int.one_le_abs hk
  have hqpos : 0 < q := by linarith
  have hπ : 0 < Real.pi := Real.pi_pos
  have hden : ‖(Real.pi : ℂ)*k‖ = Real.pi*q := by
    simp [q, Complex.norm_intCast, abs_of_pos Real.pi_pos]
  have hmidk : ‖sourcePeriodicMidpointDisplacement hp hp1 ψ k‖ ≤ M :=
    (lp.norm_apply_le_norm (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
      (sourcePeriodicMidpointDisplacement hp hp1 ψ) k).trans hM
  have hb : ‖sourcePeriodicMidpointDisplacement hp hp1 ψ k /
      ((Real.pi : ℂ)*k)‖ ≤ M/(Real.pi*q) := by
    rw [norm_div, hden]
    exact div_le_div_of_nonneg_right hmidk (by positivity)
  have hz : ‖z / ((Real.pi : ℂ)*k)‖ ≤ R/(Real.pi*q) := by
    rw [norm_div, hden]
    exact div_le_div_of_nonneg_right hR (by positivity)
  have hr' : ‖sourceStandardRootSqrtCorrection hp hp1 ψ z k‖ ≤ C/q^2 := by
    simpa only [q, Real.rpow_neg (abs_nonneg (k : ℝ)), Real.rpow_ofNat,
      div_eq_mul_inv] using hr
  have heq : sourceStandardRootRelativeError hp hp1 ψ k z =
      sourcePeriodicMidpointDisplacement hp hp1 ψ k / ((Real.pi : ℂ)*k) -
        z / ((Real.pi : ℂ)*k) +
        sourceStandardRootSqrtCorrection hp hp1 ψ z k := by
    rw [sourceStandardRootRelativeError_eq hp hp1 ψ k z hk]
    simp only [sourceStandardRootSqrtCorrection, if_neg hk]
    rfl
  rw [heq]
  have htriangle : ‖sourcePeriodicMidpointDisplacement hp hp1 ψ k /
      ((Real.pi : ℂ)*k) - z / ((Real.pi : ℂ)*k) +
        sourceStandardRootSqrtCorrection hp hp1 ψ z k‖ ≤
      ‖sourcePeriodicMidpointDisplacement hp hp1 ψ k / ((Real.pi : ℂ)*k)‖ +
      ‖z / ((Real.pi : ℂ)*k)‖ +
      ‖sourceStandardRootSqrtCorrection hp hp1 ψ z k‖ := by
    have ht := norm_sub_le
      (sourcePeriodicMidpointDisplacement hp hp1 ψ k / ((Real.pi : ℂ)*k))
      (z / ((Real.pi : ℂ)*k))
    exact (norm_add_le _ _).trans (by linarith)
  calc
    _ ≤ M/(Real.pi*q) + R/(Real.pi*q) + C/q^2 := by linarith
    _ ≤ ((M+R)/Real.pi+C)/q := by
      have hmain : C/q^2 ≤ C/q := by
        apply (div_le_div_iff₀ (by positivity) hqpos).mpr
        nlinarith [mul_nonneg hC (show 0 ≤ q^2-q by nlinarith)]
      have hid : M/(Real.pi*q) + R/(Real.pi*q) + C/q =
          ((M+R)/Real.pi+C)/q := by field_simp
      linarith

/-- On a source neighborhood and bounded spectral region, the quadratic
paired-error term has one summable reciprocal-square majorant. -/
theorem exists_uniform_sourceStandardRootPairedCross_majorant
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ N : ℕ, ∃ V : Set (CoeffPair p), ∃ A : ℝ,
      IsOpen V ∧ φ ∈ V ∧ 0 ≤ A ∧
      (∀ ψ ∈ V, ∀ z : ℂ, ‖z‖ ≤ R → ∀ k : ℤ, N < k.natAbs →
        ‖sourceStandardRootRelativeError hp hp1 ψ k z *
          sourceStandardRootRelativeError hp hp1 ψ (-k) z‖ ≤
          A * |(k : ℝ)| ^ (-(2 : ℝ))) ∧
      Summable (fun k : ℤ =>
        A * (if k = 0 then (0 : ℝ) else |(k : ℝ)| ^ (-(2 : ℝ)))) := by
  obtain ⟨N₁, _, V₁, hV₁open, hφV₁, M, hM, hdata₁⟩ :=
    exists_uniform_small_sourcePeriodicMidpointDisplacement hp hp1 φ
      (by norm_num : (0 : ℝ) < 1)
  obtain ⟨N₂, V₂, C, hV₂open, hφV₂, hC, hdata₂, _⟩ :=
    exists_uniform_sourceStandardRootSqrtCorrection_majorant hp hp1 φ R
  let B : ℝ := (M+R)/Real.pi+C
  let A : ℝ := B^2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨max N₁ N₂, V₁ ∩ V₂, A,
    hV₁open.inter hV₂open, ⟨hφV₁, hφV₂⟩,
    by dsimp [A]; positivity, ?_, ?_⟩
  · intro ψ hψ z hz k hk
    have hk₁ : N₁ < k.natAbs := by omega
    have hk₂ : N₂ < k.natAbs := by omega
    have hk0 : k ≠ 0 := by omega
    have hrpos := hdata₂ ψ hψ.2 z hz k hk₂
    have hrneg := hdata₂ ψ hψ.2 z hz (-k) (by simpa using hk₂)
    have ha := norm_sourceStandardRootRelativeError_le_reciprocal
      hp hp1 ψ z k M R C hk0 (hdata₁ ψ hψ.1).1 hz hC hrpos
    have hb := norm_sourceStandardRootRelativeError_le_reciprocal
      hp hp1 ψ z (-k) M R C (neg_ne_zero.mpr hk0)
        (hdata₁ ψ hψ.1).1 hz hC hrneg
    have hq : 0 < |(k : ℝ)| := abs_pos.mpr (by exact_mod_cast hk0)
    have hb' : ‖sourceStandardRootRelativeError hp hp1 ψ (-k) z‖ ≤
        B / |(k : ℝ)| := by simpa only [Int.cast_neg, abs_neg, B] using hb
    have ha' : ‖sourceStandardRootRelativeError hp hp1 ψ k z‖ ≤
        B / |(k : ℝ)| := ha
    calc
      _ = ‖sourceStandardRootRelativeError hp hp1 ψ k z‖ *
          ‖sourceStandardRootRelativeError hp hp1 ψ (-k) z‖ := norm_mul _ _
      _ ≤ (B / |(k : ℝ)|) * (B / |(k : ℝ)|) :=
        mul_le_mul ha' hb' (norm_nonneg _) (div_nonneg hB hq.le)
      _ = A * |(k : ℝ)| ^ (-(2 : ℝ)) := by
        rw [Real.rpow_neg hq.le, Real.rpow_ofNat]
        dsimp [A]
        field_simp
  · have hbase : Summable (fun k : ℤ =>
        if k = 0 then (0 : ℝ) else |(k : ℝ)| ^ (-(2 : ℝ))) := by
      simpa only [zero_add] using
        (NLS.ReciprocalSeries.summable_int_shifted_rpow
          (α := 0) (q := 2) le_rfl (by norm_num))
    exact hbase.mul_left A

/-- The paired deviation is the sum of the two midpoint corrections,
the two square-root corrections, and the quadratic cross term. -/
theorem sourceStandardRootPairedFactor_sub_one_eq_corrections
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (z : ℂ) (j : ℕ) :
    let k : ℤ := (j+1 : ℕ)
    sourceStandardRootPairedFactor hp hp1 ψ z j - 1 =
      sourceStandardRootMidpointCorrection hp hp1 ψ k +
      sourceStandardRootMidpointCorrection hp hp1 ψ (-k) +
      sourceStandardRootSqrtCorrection hp hp1 ψ z k +
      sourceStandardRootSqrtCorrection hp hp1 ψ z (-k) +
      sourceStandardRootRelativeError hp hp1 ψ k z *
        sourceStandardRootRelativeError hp hp1 ψ (-k) z := by
  let k : ℤ := (j+1 : ℕ)
  have hk : k ≠ 0 := by dsimp [k]; omega
  simp only [sourceStandardRootPairedFactor_eq_one_add, add_sub_cancel_left,
    sourceStandardRootPairExcessCoeff, lp.coeFn_add, Pi.add_apply,
    Coeff.reflection_apply, Coeff.holderProduct_apply,
    sourceStandardRootSqrtCorrectionCoeff_apply]
  rw [sourceStandardRootRelativeErrorCoeff_apply_of_ne hp hp1 ψ z
    ((j+1 : ℕ) : ℤ) (by omega),
    sourceStandardRootRelativeErrorCoeff_apply_of_ne hp hp1 ψ z
    (-((j+1 : ℕ) : ℤ)) (by omega)]

/-- On every compact spectral set, the paired factors have a common
summable majorant after finitely many indices. -/
theorem exists_sourceStandardRootPairedFactor_compact_majorant
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (K : Set ℂ) (hK : IsCompact K) :
    ∃ N : ℕ, ∃ u : ℕ → ℝ, Summable u ∧
      ∀ j : ℕ, N ≤ j → ∀ z ∈ K,
        ‖sourceStandardRootPairedFactor hp hp1 ψ z j - 1‖ ≤ u j := by
  obtain ⟨R, hR, hbound⟩ := hK.isBounded.exists_pos_norm_le
  obtain ⟨N₁, V₁, C, _, hψ₁, hC, hsqrt, _⟩ :=
    exists_uniform_sourceStandardRootSqrtCorrection_majorant hp hp1 ψ R
  obtain ⟨N₂, V₂, A, _, hψ₂, hA, hcross, _⟩ :=
    exists_uniform_sourceStandardRootPairedCross_majorant hp hp1 ψ R hR.le
  let b := sourceStandardRootMidpointCorrection hp hp1 ψ
  let u : ℕ → ℝ := fun j =>
    ‖b (((j+1 : ℕ) : ℤ))‖ + ‖b (-((j+1 : ℕ) : ℤ))‖ +
      (2*C+A) / ((j : ℝ)+1)^2
  have hb := summable_norm_sourceStandardRootMidpointCorrection hp hp1 ψ
  have hpos : Summable (fun j : ℕ => ‖b (((j+1 : ℕ) : ℤ))‖) := by
    apply hb.comp_injective
    intro i j hij
    have := Int.ofNat_injective hij
    omega
  have hneg : Summable (fun j : ℕ => ‖b (-((j+1 : ℕ) : ℤ))‖) := by
    apply hb.comp_injective
    intro i j hij
    have := Int.ofNat_injective (neg_injective hij)
    omega
  have hq : Summable (fun j : ℕ => 1/((j : ℝ)+1)^2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr
        (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
  have hu : Summable u := by
    simpa only [u, one_div, div_eq_mul_inv, one_mul] using
      (hpos.add hneg).add (hq.mul_left (2*C+A))
  refine ⟨max N₁ N₂, u, hu, ?_⟩
  intro j hj z hz
  let k : ℤ := ((j+1 : ℕ) : ℤ)
  have hk₁ : N₁ < k.natAbs := by simpa only [k, Int.natAbs_natCast] using (by omega : N₁ < j+1)
  have hk₂ : N₂ < k.natAbs := by simpa only [k, Int.natAbs_natCast] using (by omega : N₂ < j+1)
  have hzk : ‖z‖ ≤ R := hbound z hz
  have hrootpos := hsqrt ψ hψ₁ z hzk k hk₁
  have hrootneg := hsqrt ψ hψ₁ z hzk (-k) (by simpa using hk₁)
  have hquadratic := hcross ψ hψ₂ z hzk k hk₂
  have hpow : |(k : ℝ)| ^ (-(2 : ℝ)) =
      1/((j : ℝ)+1)^2 := by
    have hkpos : 0 < |(k : ℝ)| := by dsimp [k]; positivity
    rw [Real.rpow_neg hkpos.le, Real.rpow_ofNat]
    simp [k, Nat.cast_add, Nat.cast_one]
  rw [hpow] at hrootpos hquadratic
  have hrootneg' : ‖sourceStandardRootSqrtCorrection hp hp1 ψ z (-k)‖ ≤
      C / ((j : ℝ)+1)^2 := by
    simpa [Int.cast_neg, abs_neg, hpow, div_eq_mul_inv] using hrootneg
  have hrootpos' : ‖sourceStandardRootSqrtCorrection hp hp1 ψ z k‖ ≤
      C / ((j : ℝ)+1)^2 := by
    simpa [div_eq_mul_inv] using hrootpos
  have hquadratic' : ‖sourceStandardRootRelativeError hp hp1 ψ k z *
      sourceStandardRootRelativeError hp hp1 ψ (-k) z‖ ≤
      A / ((j : ℝ)+1)^2 := by
    simpa [div_eq_mul_inv] using hquadratic
  rw [sourceStandardRootPairedFactor_sub_one_eq_corrections]
  have ht₁ := norm_add_le
    (b k + b (-k) + sourceStandardRootSqrtCorrection hp hp1 ψ z k +
      sourceStandardRootSqrtCorrection hp hp1 ψ z (-k))
    (sourceStandardRootRelativeError hp hp1 ψ k z *
      sourceStandardRootRelativeError hp hp1 ψ (-k) z)
  have ht₂ := norm_add_le
    (b k + b (-k) + sourceStandardRootSqrtCorrection hp hp1 ψ z k)
    (sourceStandardRootSqrtCorrection hp hp1 ψ z (-k))
  have ht₃ := norm_add_le (b k + b (-k))
    (sourceStandardRootSqrtCorrection hp hp1 ψ z k)
  have ht₄ := norm_add_le (b k) (b (-k))
  dsimp [u, b, k] at *
  have hid : (2*C+A) / ((j : ℝ)+1)^2 =
      C / ((j : ℝ)+1)^2 + C / ((j : ℝ)+1)^2 +
        A / ((j : ℝ)+1)^2 := by ring
  rw [hid]
  nlinarith

/-- The omitted-zero paired product converges uniformly on every compact
subset of its spectral gap complement. -/
theorem hasProdUniformlyOn_sourceStandardRootPairedFactor
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (K : Set ℂ) (hK : IsCompact K)
    (hdom : K ⊆ sourceStandardRootPairedDomain hp hp1 ψ) :
    HasProdUniformlyOn (fun j z => sourceStandardRootPairedFactor hp hp1 ψ z j)
      (fun z => sourceStandardRootPairedProduct hp hp1 ψ z) K := by
  obtain ⟨N, u, hu, hbound⟩ :=
    exists_sourceStandardRootPairedFactor_compact_majorant hp hp1 ψ K hK
  have hevent : ∀ᶠ j : ℕ in cofinite, ∀ z ∈ K,
      ‖sourceStandardRootPairedFactor hp hp1 ψ z j - 1‖ ≤ u j := by
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [eventually_ge_atTop N] with j hj
    exact hbound j hj
  have hprod := hu.hasProdUniformlyOn_one_add
    (f := fun j z => sourceStandardRootPairedFactor hp hp1 ψ z j - 1)
    hK hevent (fun j =>
      (sourceStandardRootPairedFactor_continuousOn hp hp1 ψ K hdom j).sub continuousOn_const)
  have hfac (j : ℕ) (z : ℂ) :
      1 + (sourceStandardRootPairedFactor hp hp1 ψ z j - 1) =
        sourceStandardRootPairedFactor hp hp1 ψ z j := by ring
  simpa only [hfac, sourceStandardRootPairedProduct] using hprod

/-- Natural finite paired cutoffs converge uniformly on compact subsets
of the omitted-zero spectral domain. -/
theorem tendstoUniformlyOn_sourceStandardRootPairedPartialProduct
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (K : Set ℂ) (hK : IsCompact K)
    (hdom : K ⊆ sourceStandardRootPairedDomain hp hp1 ψ) :
    TendstoUniformlyOn (fun N : ℕ => fun z =>
      sourceStandardRootPairedPartialProduct hp hp1 ψ z N)
      (fun z => sourceStandardRootPairedProduct hp hp1 ψ z) atTop K := by
  simpa only [sourceStandardRootPairedPartialProduct] using
    (hasProdUniformlyOn_sourceStandardRootPairedFactor hp hp1 ψ K hK hdom).tendstoUniformlyOn_finsetRange


end NLS.ZakharovShabat
