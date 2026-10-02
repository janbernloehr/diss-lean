import NLS.ZakharovShabat.SourceFiniteGapTailRecurrence
import NLS.SequenceSpaces.GeometricTailRegularity

/-! # Positive weighted regularity of actual finite-gap sources

The spectral finite-gap condition implies weighted Fourier membership
for every nonnegative `s` with `s*p < min(1,p-1)`. No Fourier support
or initial positive regularity hypothesis is imposed.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every real finite-gap source has Sobolev-weighted Fourier
coefficients throughout the regularity range furnished by the first
tail bootstrap. This statement concerns the original source. -/
theorem sourceFiniteGap_mem_sobolev
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceLocus p)
    (hfinite : φ ∈ sourceFiniteGapLocus hp hp1)
    (s : ℝ) (hs : 0 ≤ s) (hsp : s*p.toReal < min 1 (p.toReal-1)) :
    Memℓp (fun n => (Weight.sobolev s n : ℂ)*φ.val.fst n) p ∧
    Memℓp (fun n => (Weight.sobolev s n : ℂ)*φ.val.snd n) p := by
  have hpR : 1 < p.toReal := (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
  have hp0 : 0 < p.toReal := zero_lt_one.trans hpR
  let α := min 1 (p.toReal-1)
  let β := (α+s*p.toReal)/2
  have hsp0 : 0 ≤ s*p.toReal := mul_nonneg hs hp0.le
  have hβ0 : 0 < β := by dsimp [β,α]; linarith
  have hβlo : s*p.toReal < β := by dsimp [β,α]; linarith
  have hβhi : β < α := by dsimp [β]; dsimp only [α] at *; linarith
  let q := (4 : ℝ)^(-β)
  have hq0 : 0 < q := Real.rpow_pos_of_pos (by norm_num) _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hqlo : (4 : ℝ)^(-α) < q :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  have hrq : (4 : ℝ)^(s*p.toReal)*q < 1 := by
    dsimp only [q]
    rw [← Real.rpow_add (by norm_num)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  obtain ⟨M,hM,C,_,hb⟩ := sourceFiniteGap_fourierTail_geometric hp hp1 φ hfinite q hqlo hq1
  constructor
  · apply Coeff.mem_sobolev_of_geometric_tail hp0 φ.val.fst M hM C q s hq0.le hs hrq
    intro k
    exact (Real.rpow_le_rpow (norm_nonneg _)
      (WithLp.norm_fst_le (Coeff p) (sourceFourierTail (4^k*M) φ.val)) hp0.le).trans (hb k)
  · apply Coeff.mem_sobolev_of_geometric_tail hp0 φ.val.snd M hM C q s hq0.le hs hrq
    intro k
    exact (Real.rpow_le_rpow (norm_nonneg _)
      (WithLp.norm_snd_le (Coeff p) (sourceFourierTail (4^k*M) φ.val)) hp0.le).trans (hb k)

/-- A positive regularity exponent is constructed at every finite
Banach exponent above one. Further bootstrapping is needed for `H¹`. -/
theorem exists_sourceFiniteGap_positive_regularity
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceLocus p)
    (hfinite : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ s : ℝ, 0 < s ∧
      Memℓp (fun n => (Weight.sobolev s n : ℂ)*φ.val.fst n) p ∧
      Memℓp (fun n => (Weight.sobolev s n : ℂ)*φ.val.snd n) p := by
  have hpR : 1 < p.toReal := (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
  have hp0 : 0 < p.toReal := zero_lt_one.trans hpR
  let α := min 1 (p.toReal-1)
  have hα : 0 < α := lt_min (by norm_num) (by linarith)
  let s := α/(2*p.toReal)
  have hs : 0 < s := div_pos hα (by positivity)
  refine ⟨s,hs,sourceFiniteGap_mem_sobolev hp hp1 φ hfinite s hs.le ?_⟩
  change α/(2*p.toReal)*p.toReal < α
  have he : α/(2*p.toReal)*p.toReal = α/2 := by field_simp
  rw [he]
  linarith

end NLS.ZakharovShabat
