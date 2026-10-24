import NLS.ZakharovShabat.SourceFiniteGapPhysicalTrace
import NLS.ZakharovShabat.AuxiliaryPeriodOneBoundaryInterlacing
import NLS.ZakharovShabat.SourceSpatialTranslation
import NLS.Fourier.PeriodOneSynthesisAlgebra
import NLS.Fourier.SpatialTranslation

/-! # Pointwise finite-gap bounds by the total gap length

The physical boundary trace, applied also to the fixed quarter-turn phase,
bounds both components at zero. Spatial translation gives the same bound
at every point. The constant here is sufficient for norm bounds; no claim
of a sharp trace inequality or properness is made.
-/
noncomputable section
open Set Complex NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The finite sum of the actual open gap lengths for a Hilbert source. -/
def sourceFiniteGapLengthSum (φ : realTypeSourceSubmodule 2)
    (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) : ℝ :=
  ∑ n ∈ hf.toFinset, ‖canonicalPeriodicGap (by simp) (by norm_num)
    (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n‖

theorem sourceFiniteGapLengthSum_eq_of_gaps_eq
    (φ ψ : realTypeSourceSubmodule 2)
    (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (hg : ψ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (he : ∀ n, canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n =
      canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential ψ.val) (periodOnePotential_mem ψ.val) n) :
    sourceFiniteGapLengthSum φ hf = sourceFiniteGapLengthSum ψ hg := by
  have hs : hf.toFinset = hg.toFinset := by
    ext n
    have hφ : n ∈ hf.toFinset ↔ canonicalPeriodicGap (by simp) (by norm_num)
        (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0 := Set.Finite.mem_toFinset hf
    have hψ : n ∈ hg.toFinset ↔ canonicalPeriodicGap (by simp) (by norm_num)
        (periodOnePotential ψ.val) (periodOnePotential_mem ψ.val) n ≠ 0 := Set.Finite.mem_toFinset hg
    have hn : canonicalPeriodicGap (by simp) (by norm_num)
        (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0 ↔
        canonicalPeriodicGap (by simp) (by norm_num)
        (periodOnePotential ψ.val) (periodOnePotential_mem ψ.val) n ≠ 0 := by rw [he]
    exact hφ.trans (hn.trans hψ.symm)
  unfold sourceFiniteGapLengthSum
  rw [hs]
  apply Finset.sum_congr rfl
  intro n _
  rw [he]

theorem norm_sourceFiniteGapPhysicalPair_sum_zero_le
    (φ : realTypeSourceSubmodule 2)
    (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    ‖(sourceFiniteGapPhysicalPair (by simp) (by norm_num) φ hf).1 0 +
      (sourceFiniteGapPhysicalPair (by simp) (by norm_num) φ hf).2 0‖ ≤
      sourceFiniteGapLengthSum φ hf := by
  obtain ⟨s,hs,_,hb⟩ := exists_sourceFiniteGap_physical_boundary_trace φ hf
  have he : s = hf.toFinset := by
    ext n
    exact (hs n).trans (Set.Finite.mem_toFinset hf).symm
  simpa only [he,sourceFiniteGapLengthSum] using hb

private theorem norm_components_le_of_sum_and_difference (u v : ℂ) (S : ℝ)
    (hp : ‖u+v‖ ≤ S) (hm : ‖u-v‖ ≤ S) : ‖u‖ ≤ S ∧ ‖v‖ ≤ S := by
  have hu := norm_add_le (u+v) (u-v)
  have hv := norm_sub_le (u+v) (u-v)
  rw [show u+v+(u-v) = (2:ℂ)*u by ring,norm_mul] at hu
  rw [show u+v-(u-v) = (2:ℂ)*v by ring,norm_mul] at hv
  norm_num only [norm_ofNat] at hu hv
  constructor <;> linarith

/-- The two physical components at zero are bounded by the finite gap sum. -/
theorem norm_sourceFiniteGapPhysicalPair_zero_le
    (φ : realTypeSourceSubmodule 2)
    (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    ‖(sourceFiniteGapPhysicalPair (by simp) (by norm_num) φ hf).1 0‖ ≤ sourceFiniteGapLengthSum φ hf ∧
    ‖(sourceFiniteGapPhysicalPair (by simp) (by norm_num) φ hf).2 0‖ ≤ sourceFiniteGapLengthSum φ hf := by
  let ψ : realTypeSourceSubmodule 2 := ⟨sourcePhase φ.val,isRealType_sourcePhase φ.val φ.property⟩
  have hgap (n : ℤ) : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential ψ.val) (periodOnePotential_mem ψ.val) n =
      canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n := by
    obtain ⟨hl,hr⟩ := canonicalPeriodicEndpoints_sourcePhase (by simp) (by norm_num) φ.val
    simp only [canonicalPeriodicGap,ψ,hl,hr]
  have hg : ψ ∈ sourceFiniteGapLocus (by simp) (by norm_num) := by
    change {n : ℤ | canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential ψ.val) (periodOnePotential_mem ψ.val) n ≠ 0}.Finite
    simp_rw [hgap]
    exact hf
  have hsum := norm_sourceFiniteGapPhysicalPair_sum_zero_le ψ hg
  rw [sourceFiniteGapLengthSum_eq_of_gaps_eq ψ φ hg hf hgap] at hsum
  let a : Coeff 1 := ⟨_,(sourceFiniteGap_memlp_one (by simp) (by norm_num) φ hf).1⟩
  let b : Coeff 1 := ⟨_,(sourceFiniteGap_memlp_one (by simp) (by norm_num) φ hf).2⟩
  have ha : (⟨_,(sourceFiniteGap_memlp_one (by simp) (by norm_num) ψ hg).1⟩ : Coeff 1) = I • a := by
    ext n
    rfl
  have hb : (⟨_,(sourceFiniteGap_memlp_one (by simp) (by norm_num) ψ hg).2⟩ : Coeff 1) = -I • b := by
    ext n
    rfl
  simp only [sourceFiniteGapPhysicalPair,ha,hb,periodOneSynthesis_smul] at hsum
  rw [show I*periodOneSynthesis a 0 + -I*periodOneSynthesis b 0 =
    I*(periodOneSynthesis a 0-periodOneSynthesis b 0) by ring,norm_mul,norm_I,one_mul] at hsum
  exact norm_components_le_of_sum_and_difference _ _ _
    (norm_sourceFiniteGapPhysicalPair_sum_zero_le φ hf) hsum

/-- Both original physical components are uniformly bounded by the sum of the open gap lengths. -/
theorem norm_sourceFiniteGapPhysicalPair_le
    (φ : realTypeSourceSubmodule 2)
    (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (x : ℝ) :
    ‖(sourceFiniteGapPhysicalPair (by simp) (by norm_num) φ hf).1 x‖ ≤ sourceFiniteGapLengthSum φ hf ∧
    ‖(sourceFiniteGapPhysicalPair (by simp) (by norm_num) φ hf).2 x‖ ≤ sourceFiniteGapLengthSum φ hf := by
  let ψ : realTypeSourceSubmodule 2 :=
    ⟨sourceSpatialTranslation x φ.val,sourceSpatialTranslation_realType x φ.val φ.property⟩
  have hg : ψ ∈ sourceFiniteGapLocus (by simp) (by norm_num) :=
    sourceSpatialTranslation_mem_sourceFiniteGapLocus (by simp) (by norm_num) x φ hf
  have hgap (n : ℤ) : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential ψ.val) (periodOnePotential_mem ψ.val) n =
      canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n :=
    sourceCanonicalPeriodicGap_spatialTranslation (by simp) (by norm_num) x φ.val n
  have h := norm_sourceFiniteGapPhysicalPair_zero_le ψ hg
  rw [sourceFiniteGapLengthSum_eq_of_gaps_eq ψ φ hg hf hgap] at h
  let a : Coeff 1 := ⟨_,(sourceFiniteGap_memlp_one (by simp) (by norm_num) φ hf).1⟩
  let b : Coeff 1 := ⟨_,(sourceFiniteGap_memlp_one (by simp) (by norm_num) φ hf).2⟩
  have ha : (⟨_,(sourceFiniteGap_memlp_one (by simp) (by norm_num) ψ hg).1⟩ : Coeff 1) =
      Coeff.spatialTranslation (2*Real.pi) x a := by ext n; rfl
  have hb : (⟨_,(sourceFiniteGap_memlp_one (by simp) (by norm_num) ψ hg).2⟩ : Coeff 1) =
      Coeff.spatialTranslation (2*Real.pi) x b := by ext n; rfl
  simpa only [sourceFiniteGapPhysicalPair,ha,hb,periodOneSynthesis_spatialTranslation,zero_add] using h

/-- The original Hilbert source norm is controlled by the finite sum of gap lengths. -/
theorem norm_sq_sourceFiniteGap_le_gap_sum
    (φ : realTypeSourceSubmodule 2)
    (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    ‖φ.val‖^2 ≤ 2 * (sourceFiniteGapLengthSum φ hf)^2 := by
  let a : Coeff 1 := ⟨_,(sourceFiniteGap_memlp_one (by simp) (by norm_num) φ hf).1⟩
  let b : Coeff 1 := ⟨_,(sourceFiniteGap_memlp_one (by simp) (by norm_num) φ hf).2⟩
  have hS : 0 ≤ sourceFiniteGapLengthSum φ hf := by
    unfold sourceFiniteGapLengthSum
    positivity
  have hm := classicalPhysicalMass_absoluteSourceCurve φ.val a b (fun _ => rfl) (fun _ => rfl)
  have hb : ‖classicalPhysicalMass (absoluteSourceCurve a b)‖ ≤ (sourceFiniteGapLengthSum φ hf)^2 := by
    unfold classicalPhysicalMass
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
      (f := fun x => (NLS.LinearVolterra.extend (absoluteSourceCurve a b) x).1 *
        (NLS.LinearVolterra.extend (absoluteSourceCurve a b) x).2)
      (C := (sourceFiniteGapLengthSum φ hf)^2) (fun x hx => ?_)
    · simpa only [sub_zero,abs_one,one_mul,mul_one] using hi
    · have hx' : x ∈ Icc (0 : ℝ) 1 := by
        exact Set.Ioc_subset_Icc_self (by simpa only [Set.uIoc_of_le zero_le_one] using hx)
      rw [extend_absoluteSourceCurve a b x hx',norm_mul]
      have hxbound := norm_sourceFiniteGapPhysicalPair_le φ hf x
      exact (mul_le_mul hxbound.1 hxbound.2 (norm_nonneg _) hS).trans_eq (by ring)
  rw [hm,sourceHilbertMass_eq_half_norm_sq_of_realType φ.val φ.property,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)] at hb
  nlinarith

end NLS.ZakharovShabat
