import NLS.ZakharovShabat.SourcePeriodicEndpointContinuity

/-!
# Lemma 8.2 and the real-gap characterization in the original source space

Continuity at real type allows arbitrary complex source perturbations.
The actual ordered endpoints are real and successive gaps are strictly
separated, including collapsed and central gaps. The discriminant levels
and closed/open-gap characterizations retain every signed integer index.
-/

noncomputable section
open Set Complex
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The original closed real gap, used at real-type source potentials. -/
def sourceRealPeriodicGap (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (n : ℤ) : Set ℝ :=
  Icc (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re
    (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re

/-- Equation (2.5), with integer powers at every positive and negative source index. -/
theorem sourcePeriodicEndpoints_signed_discriminant (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) :
    (-1 : ℂ)^n * canonicalDiscriminant hp (periodOnePotential φ)
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n) = 2 ∧
    (-1 : ℂ)^n * canonicalDiscriminant hp (periodOnePotential φ)
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n) = 2 := by
  have h := canonicalPeriodicEndpoints_discriminant_of_realType hp hp1 _ (periodOnePotential_mem φ)
    (isRealType_periodOnePotential φ hφ) n
  simp only [h.1,h.2,neg_one_zpow_eq_ite,Int.even_iff]
  split_ifs <;> norm_num

/-- The source lemma and its following gap assertions, without a simplicity condition. -/
structure SourceLemma8_2Data (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) : Prop where
  continuous_left : ∀ n : ℤ, ContinuousAt (fun ψ : CoeffPair p =>
    canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n) φ
  continuous_right : ∀ n : ℤ, ContinuousAt (fun ψ : CoeffPair p =>
    canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n) φ
  real_endpoints : ∀ n : ℤ,
    (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).im = 0 ∧
    (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).im = 0
  spectral_endpoints : ∀ n : ℤ,
    canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n ∈
      periodicSpectrum hp (periodOnePotential φ) ∧
    canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n ∈
      periodicSpectrum hp (periodOnePotential φ)
  interlacing : ∀ n : ℤ,
    let L := canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ)
    let R := canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ)
    (R (n-1)).re < (L n).re ∧ (L n).re ≤ (R n).re ∧ (R n).re < (L (n+1)).re
  disjoint_gaps : ∀ i j : ℤ, i ≠ j → Disjoint (sourceRealPeriodicGap hp hp1 φ i) (sourceRealPeriodicGap hp hp1 φ j)
  endpoint_levels : ∀ n : ℤ,
    (-1 : ℂ)^n * canonicalDiscriminant hp (periodOnePotential φ)
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n) = 2 ∧
    (-1 : ℂ)^n * canonicalDiscriminant hp (periodOnePotential φ)
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n) = 2
  gap_sign : ∀ n : ℤ, ∀ x ∈ sourceRealPeriodicGap hp hp1 φ n,
    2 ≤ (-1 : ℝ)^n * (canonicalDiscriminant hp (periodOnePotential φ) x).re
  closed_gaps : {x : ℝ | 2 ≤ ‖canonicalDiscriminant hp (periodOnePotential φ) x‖} =
    ⋃ n : ℤ, sourceRealPeriodicGap hp hp1 φ n
  open_gaps : ∀ x : ℝ, 2 < ‖canonicalDiscriminant hp (periodOnePotential φ) x‖ ↔ ∃ n : ℤ,
    x ∈ Ioo (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re
  endpoint_set : ∀ x : ℝ, ‖canonicalDiscriminant hp (periodOnePotential φ) x‖ = 2 ↔ ∃ n : ℤ,
    x = (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re ∨
    x = (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re

/-- Lemma 8.2 and the following discriminant characterization, for every finite p>1 source. -/
theorem sourceLemma8_2 (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) : SourceLemma8_2Data hp hp1 φ where
  continuous_left := continuousAt_canonicalPeriodicLeft_periodOne_of_realType hp hp1 φ hφ
  continuous_right := continuousAt_canonicalPeriodicRight_periodOne_of_realType hp hp1 φ hφ
  real_endpoints := canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1 _ (periodOnePotential_mem φ)
    (isRealType_periodOnePotential φ hφ)
  spectral_endpoints := canonicalPeriodicEndpoints_mem_spectrum hp hp1 _ (periodOnePotential_mem φ)
  interlacing := fun n => ⟨canonicalPeriodicRight_re_lt_left_of_lt hp hp1 _ (periodOnePotential_mem φ)
      (isRealType_periodOnePotential φ hφ) (by omega),
    re_le_of_complexLexLE ((canonicalPeriodicEndpoints_spec hp hp1 _ (periodOnePotential_mem φ)).2.1 n),
    canonicalPeriodicRight_re_lt_next_left hp hp1 _ (periodOnePotential_mem φ) (isRealType_periodOnePotential φ hφ) n⟩
  disjoint_gaps := fun _ _ hij => canonicalPeriodicGaps_disjoint hp hp1 _ (periodOnePotential_mem φ)
    (isRealType_periodOnePotential φ hφ) hij
  endpoint_levels := sourcePeriodicEndpoints_signed_discriminant hp hp1 φ hφ
  gap_sign := signed_discriminant_ge_two_on_canonicalGap hp hp1 _ (periodOnePotential_mem φ)
    (isRealType_periodOnePotential φ hφ)
  closed_gaps := real_discriminant_superlevel_eq_canonicalGaps hp hp1 _ (periodOnePotential_mem φ)
    (isRealType_periodOnePotential φ hφ)
  open_gaps := two_lt_norm_discriminant_iff_mem_canonicalGap_interior hp hp1 _ (periodOnePotential_mem φ)
    (isRealType_periodOnePotential φ hφ)
  endpoint_set := norm_discriminant_eq_two_iff_canonicalEndpoint hp hp1 _ (periodOnePotential_mem φ)
    (isRealType_periodOnePotential φ hφ)

/-- The real gap containing a superlevel point is unique, even at collapsed gaps. -/
theorem SourceLemma8_2Data.existsUnique_gap {hp : p ≠ ⊤} {hp1 : 1 < p} {φ : CoeffPair p}
    (D : SourceLemma8_2Data hp hp1 φ) (x : ℝ) :
    2 ≤ ‖canonicalDiscriminant hp (periodOnePotential φ) x‖ ↔ ∃! n : ℤ, x ∈ sourceRealPeriodicGap hp hp1 φ n := by
  have he : 2 ≤ ‖canonicalDiscriminant hp (periodOnePotential φ) x‖ ↔
      ∃ n : ℤ, x ∈ sourceRealPeriodicGap hp hp1 φ n := by
    change x ∈ {y : ℝ | 2 ≤ ‖canonicalDiscriminant hp (periodOnePotential φ) y‖} ↔ _
    rw [D.closed_gaps,mem_iUnion]
  rw [he]
  constructor
  · rintro ⟨n,hn⟩
    refine ⟨n,hn,?_⟩
    intro m hm
    by_contra hmn
    exact Set.disjoint_left.mp (D.disjoint_gaps m n hmn) hm hn
  · rintro ⟨n,hn,_⟩
    exact ⟨n,hn⟩

/-- Every free closed gap is the singleton at its signed lattice center. -/
@[simp] theorem sourceRealPeriodicGap_zero (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    sourceRealPeriodicGap hp hp1 (0 : CoeffPair p) n = {Real.pi*n} := by
  simp only [sourceRealPeriodicGap,map_zero,canonicalPeriodicLeft_zero,canonicalPeriodicRight_zero,Icc_self]
  congr 1
  simp

end NLS.ZakharovShabat
