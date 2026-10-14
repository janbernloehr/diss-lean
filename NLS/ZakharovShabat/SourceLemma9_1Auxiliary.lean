import NLS.ZakharovShabat.SourceLemma9_1
import NLS.ZakharovShabat.AuxiliaryPeriodOneBoundaryInterlacing

/-!
# The auxiliary analogue following Lemma 9.1

The actual auxiliary endpoint domains retain literal characteristic products,
exact spectra and multiplicities, and real-type continuity and interlacing.
Phase conjugation preserves the original periodic indices. This statement
uses the endpoint-domain labels; the printed monodromy formulas exchange
those labels, as recorded separately in the normalization audit.
-/

noncomputable section
open Set Filter
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual auxiliary displacement, as an ℓp sequence in the original source norm. -/
def sourceAuxiliaryBoundaryDisplacement (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (φ : CoeffPair p) : Coeff p :=
  sourceBoundaryDisplacement hp hp1 b (sourcePhase φ)

/-- Phase conjugation gives the actual signed auxiliary coordinates. -/
@[simp] theorem sourceAuxiliaryBoundaryDisplacement_apply (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (φ : CoeffPair p) (n : ℤ) :
    sourceAuxiliaryBoundaryDisplacement hp hp1 b φ n =
      canonicalAuxiliaryPeriodOneRoots hp hp1 b φ n-(Real.pi : ℂ)*n := by
  rw [sourceAuxiliaryBoundaryDisplacement,sourceBoundaryDisplacement_apply,
    canonicalAuxiliaryPeriodOneRoots_eq_sourcePhase]

/-- Literal products and exact spectral data for both actual auxiliary restrictions. -/
structure SourceLemma9_1AuxiliaryData (hp : p ≠ ⊤) (hp1 : 1 < p) : Prop where
  analytic : ∀ b : BoundaryCondition,
    AnalyticOnNhd ℂ (fun q : ℂ × CoeffPair p => auxiliaryPeriodOneCharacteristic hp hp1 b q.2 q.1) univ
  product : ∀ b : BoundaryCondition, ∀ φ : CoeffPair p,
    TendstoLocallyUniformlyOn
      (fun (M : ℕ) (z : ℂ) => -(∏ n ∈ Finset.Icc (-(M : ℤ)) M,
        (canonicalAuxiliaryPeriodOneRoots hp hp1 b φ n-z)/(if n = 0 then 1 else (Real.pi : ℂ)*n)))
      (auxiliaryPeriodOneCharacteristic hp hp1 b φ) atTop univ
  spectrum : ∀ b : BoundaryCondition, ∀ φ : CoeffPair p, ∀ z : ℂ,
    auxiliaryPeriodOneCharacteristic hp hp1 b φ z = 0 ↔
      z ∈ b.auxiliarySpectrum hp (auxiliaryPeriodOnePotential hp hp1 φ).val (auxiliaryPeriodOnePotential hp hp1 φ).property
  multiplicity : ∀ b : BoundaryCondition, ∀ φ : CoeffPair p, ∀ z : ℂ,
    analyticOrderAt (auxiliaryPeriodOneCharacteristic hp hp1 b φ) z =
      (b.auxiliaryAlgebraicMultiplicity hp (auxiliaryPeriodOnePotential hp hp1 φ).val
        (auxiliaryPeriodOnePotential hp hp1 φ).property z : ℕ∞)

/-- The auxiliary version of Lemma 9.1(i), on the entire original complex source space. -/
theorem sourceLemma9_1_auxiliary_data (hp : p ≠ ⊤) (hp1 : 1 < p) : SourceLemma9_1AuxiliaryData hp hp1 where
  analytic := analyticOnNhd_auxiliaryPeriodOneCharacteristic_joint hp hp1
  product := by
    intro b φ
    rw [auxiliaryPeriodOneCharacteristic_eq_sourcePhase,canonicalAuxiliaryPeriodOneRoots_eq_sourcePhase]
    exact (sourceLemma9_1_data hp hp1).product b (sourcePhase φ)
  spectrum := auxiliaryPeriodOneCharacteristic_eq_zero_iff hp hp1
  multiplicity := analyticOrderAt_auxiliaryPeriodOneCharacteristic hp hp1

/-- Real-type continuity and the strict neighboring-gap chain for the auxiliary roots. -/
structure SourceLemma9_1AuxiliaryRealData (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) : Prop where
  continuous : ∀ b : BoundaryCondition, ∀ n : ℤ,
    ContinuousAt (fun ψ : CoeffPair p => canonicalAuxiliaryPeriodOneRoots hp hp1 b ψ n) φ
  norm_continuity : ∀ b : BoundaryCondition, ContinuousAt (sourceAuxiliaryBoundaryDisplacement hp hp1 b) φ
  real : ∀ b : BoundaryCondition, ∀ n : ℤ, (canonicalAuxiliaryPeriodOneRoots hp hp1 b φ n).im = 0
  interlacing : ∀ b : BoundaryCondition, ∀ n : ℤ,
    let L := canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ)
    let R := canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ)
    let μ := canonicalAuxiliaryPeriodOneRoots hp hp1 b φ n
    (R (n-1)).re < (L n).re ∧ (L n).re ≤ μ.re ∧ μ.re ≤ (R n).re ∧ (R n).re < (L (n+1)).re
  signed_level : ∀ b : BoundaryCondition, ∀ n : ℤ,
    2 ≤ (-1 : ℝ)^n * (canonicalDiscriminant hp (periodOnePotential φ)
      (canonicalAuxiliaryPeriodOneRoots hp hp1 b φ n)).re

/-- The auxiliary version of Lemma 9.1(ii–iii), including full sequence-norm continuity. -/
theorem sourceLemma9_1_auxiliary_real (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) : SourceLemma9_1AuxiliaryRealData hp hp1 φ where
  continuous := fun b => continuousAt_canonicalAuxiliaryPeriodOneRoots_of_realType hp hp1 b φ hφ
  norm_continuity := fun b => ((sourceLemma9_1_real hp hp1 (sourcePhase φ)
    (isRealType_sourcePhase φ hφ)).norm_continuity b).comp (sourcePhase (p := p)).continuous.continuousAt
  real := fun b => canonicalAuxiliaryPeriodOneRoots_im_eq_zero hp hp1 b φ hφ
  interlacing := fun b => canonicalAuxiliaryPeriodOneRoots_interlacing_chain hp hp1 b φ hφ
  signed_level := fun b => signed_discriminant_auxiliaryPeriodOneRoot_ge_two hp hp1 b φ hφ

/-- All three auxiliary assertions, with the original endpoint-domain labels. -/
theorem sourceLemma9_1_auxiliary (hp : p ≠ ⊤) (hp1 : 1 < p) :
    SourceLemma9_1AuxiliaryData hp hp1 ∧ ∀ φ : CoeffPair p,
      IsRealType (CoeffPair.toMax p φ) → SourceLemma9_1AuxiliaryRealData hp hp1 φ :=
  ⟨sourceLemma9_1_auxiliary_data hp hp1,sourceLemma9_1_auxiliary_real hp hp1⟩

/-- One original neighborhood controls all four ordinary and auxiliary sequences. -/
theorem sourceLemma9_1_uniform_coordinate_neighborhood (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧ ∀ ψ ∈ V, ∀ b : BoundaryCondition, ∀ n : ℤ,
      ‖canonicalPeriodOneBoundaryRoots hp hp1 b ψ n-canonicalPeriodOneBoundaryRoots hp hp1 b φ n‖ < ε ∧
      ‖canonicalAuxiliaryPeriodOneRoots hp hp1 b ψ n-canonicalAuxiliaryPeriodOneRoots hp hp1 b φ n‖ < ε := by
  obtain ⟨V,hV,hφV,hv⟩ := (sourceLemma9_1_real hp hp1 φ hφ).exists_uniform_coordinate_neighborhood hε
  obtain ⟨W,hW,hφW,hw⟩ := (sourceLemma9_1_real hp hp1 (sourcePhase φ)
    (isRealType_sourcePhase φ hφ)).exists_uniform_coordinate_neighborhood hε
  refine ⟨V ∩ sourcePhase ⁻¹' W,hV.inter (hW.preimage (sourcePhase (p := p)).continuous),
    ⟨hφV,hφW⟩,?_⟩
  intro ψ hψ b n
  refine ⟨hv ψ hψ.1 b n,?_⟩
  simpa only [canonicalAuxiliaryPeriodOneRoots_eq_sourcePhase] using hw (sourcePhase ψ) hψ.2 b n

end NLS.ZakharovShabat
