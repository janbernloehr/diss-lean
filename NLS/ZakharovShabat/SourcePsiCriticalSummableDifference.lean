import NLS.ZakharovShabat.SourceProposition4_1
import NLS.Fourier.AbsoluteReciprocalYoungRows

/-! # Summable actual root differences after Proposition 4.1

Pairing the gap with the conjugate-exponent normalized root difference
puts the full critical-filled difference in ℓ¹ uniformly in the deleted
index. Its absolute reciprocal rows consequently belong to every finite
exponent above one, on a source neighborhood chosen before that exponent.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual full root difference is summable uniformly in the deleted index. -/
theorem SourceLemma12_11Data.exists_local_critical_difference_one
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (H : SourceLemma12_11Data hp hp1 W₀ W s) (hp2 : 2 < p)
    (φ : realTypeSourceLocus p) (hφ : φ.val ∈ W) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ.val ∈ V ∧ V ⊆ W ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ ψ ∈ V, ∀ n : ℤ, ∃ u : Coeff 1, ‖u‖ ≤ M ∧
        ∀ k, u k = sourcePsiCriticalDifference hp hp1 s n ψ k := by
  obtain ⟨Va,hVa,hφa,hVaW,ha⟩ := H.exists_local_critical_gapNormalized_onePlus hp2 φ hφ
  obtain ⟨_,_,Vg,hVg,hφg,G,hG,hg⟩ :=
    exists_uniform_small_sourcePeriodicGapDisplacement hp hp1 φ.val (by norm_num : (0:ℝ)<1)
  have hpc1 : 1 < p.conjExponent :=
    (ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top
  have hpc : p.conjExponent ≠ ⊤ :=
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p.conjExponent p).mpr hp1).ne
  obtain ⟨A,hA,hrows⟩ := ha p.conjExponent hpc hpc1
  refine ⟨Va ∩ Vg,hVa.inter hVg,⟨hφa,hφg⟩,fun _ h => hVaW h.1,G*A,by positivity,?_⟩
  intro ψ hψ n
  obtain ⟨a,ha',han,_,hroots⟩ := hrows ψ hψ.1 n
  let u := Coeff.quasiHolderProduct (r := 1) (sourcePeriodicGapDisplacement hp hp1 ψ) a
  have hpr : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans hp1).ne' hp
  have hpcr : 0 < p.conjExponent.toReal := ENNReal.toReal_pos (zero_lt_one.trans hpc1).ne' hpc
  refine ⟨u,(Coeff.norm_quasiHolderProduct_le hpr hpcr _ _).trans
    (mul_le_mul (hg ψ hψ.2).1 ha' (lp.norm_nonneg' _) hG),?_⟩
  intro k
  change sourcePeriodicGapDisplacement hp hp1 ψ k*a k = _
  by_cases hkn : k=n
  · subst k
    rw [han,mul_zero,sourcePsiCriticalDifference_same]
  · rw [sourcePsiCriticalDifference_other hp hp1 s n k hkn,hroots k hkn,add_sub_cancel_left]

/-- The absolute reciprocal row of the actual root difference has every finite
exponent above one, uniformly in the source and deleted index. -/
theorem SourceLemma12_11Data.exists_local_critical_difference_reciprocal_rows
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (H : SourceLemma12_11Data hp hp1 W₀ W s) (hp2 : 2 < p)
    (φ : realTypeSourceLocus p) (hφ : φ.val ∈ W) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ.val ∈ V ∧ V ⊆ W ∧
      ∀ q : ℝ≥0∞, q ≠ ⊤ → 1 < q → ∃ M : ℝ, 0 ≤ M ∧
        ∀ ψ ∈ V, ∀ n : ℤ, ∃ B : Coeff q, ‖B‖ ≤ M ∧ ∀ k : ℤ,
          ‖B k‖ = ∑' m, ‖sourcePsiCriticalDifference hp hp1 s n ψ m‖*‖NLS.Fourier.hilbertKernel (k-m)‖ := by
  obtain ⟨V,hV,hφV,hVW,L,hL,hu⟩ := H.exists_local_critical_difference_one hp2 φ hφ
  refine ⟨V,hV,hφV,hVW,?_⟩
  intro q _ hq1
  let : Fact (1 ≤ q) := ⟨hq1.le⟩
  have hY : YoungRelation 1 q q := by simp only [YoungRelation,inv_one]
  refine ⟨L*‖NLS.Fourier.hilbertKernelCoeffs hq1‖,by positivity,?_⟩
  intro ψ hψ n
  obtain ⟨u,hn,he⟩ := hu ψ hψ n
  refine ⟨NLS.Fourier.absoluteReciprocalYoungMajorant hY hq1 u,
    (NLS.Fourier.norm_absoluteReciprocalYoungMajorant_le hY hq1 u).trans
      (mul_le_mul_of_nonneg_right hn (norm_nonneg _)),?_⟩
  intro k
  simpa only [he] using NLS.Fourier.norm_absoluteReciprocalYoungMajorant_apply hY hq1 u k

end NLS.ZakharovShabat
