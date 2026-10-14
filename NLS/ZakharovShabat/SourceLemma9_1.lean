import NLS.ZakharovShabat.BoundaryCharacteristicAnalytic
import NLS.ZakharovShabat.SourceBoundaryOverview
import NLS.ZakharovShabat.L2SourceCharacteristics
import NLS.ZakharovShabat.TriangularFourierBoundary
import NLS.ZakharovShabat.PeriodOneBoundaryInterlacing

/-!
# Lemma 9.1: ordinary characteristic products and real-type interlacing

Both actual boundary characteristics are jointly analytic in the original
source space. Their literal symmetric products retain the exceptional zero
factor, exact spectra, and algebraic multiplicities. At real type, arbitrary
complex perturbations preserve coordinate and full ℓp sequence continuity.
Both boundary roots lie in the indexed periodic gap with strict separation
from its neighbors, including collapsed gaps.

The physical Hilbert agreement and finite-source uniqueness fix the entire
function's normalization, in both directions of the exponent inclusion.
-/

noncomputable section
open Set Filter
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Literal products, joint analyticity, actual spectra, and exact zero orders. -/
structure SourceLemma9_1Data (hp : p ≠ ⊤) (hp1 : 1 < p) : Prop where
  analytic : ∀ b : BoundaryCondition,
    AnalyticOnNhd ℂ (fun q : ℂ × CoeffPair p => periodOneBoundaryCharacteristic hp hp1 b q.2 q.1) univ
  product : ∀ b : BoundaryCondition, ∀ φ : CoeffPair p,
    TendstoLocallyUniformlyOn
      (fun (M : ℕ) (z : ℂ) => -(∏ n ∈ Finset.Icc (-(M : ℤ)) M,
        (canonicalPeriodOneBoundaryRoots hp hp1 b φ n-z)/(if n = 0 then 1 else (Real.pi : ℂ)*n)))
      (periodOneBoundaryCharacteristic hp hp1 b φ) atTop univ
  spectrum : ∀ b : BoundaryCondition, ∀ φ : CoeffPair p, ∀ z : ℂ,
    periodOneBoundaryCharacteristic hp hp1 b φ z = 0 ↔
      z ∈ b.spectrum hp (periodOneBoundaryPotential hp hp1 φ).val (periodOneBoundaryPotential hp hp1 φ).property
  multiplicity : ∀ b : BoundaryCondition, ∀ φ : CoeffPair p, ∀ z : ℂ,
    analyticOrderAt (periodOneBoundaryCharacteristic hp hp1 b φ) z =
      (b.algebraicMultiplicity hp (periodOneBoundaryPotential hp hp1 φ).val
        (periodOneBoundaryPotential hp hp1 φ).property z : ℕ∞)

/-- Lemma 9.1(i), for both ordinary boundary conditions and all complex sources. -/
theorem sourceLemma9_1_data (hp : p ≠ ⊤) (hp1 : 1 < p) : SourceLemma9_1Data hp hp1 where
  analytic := analyticOnNhd_periodOneBoundaryCharacteristic_joint hp hp1
  product := by
    intro b φ
    unfold periodOneBoundaryCharacteristic
    simpa only [canonicalPeriodOneBoundaryRoots,periodOneBoundaryCharacteristic,
      boundaryCharacteristicPartialProduct,singleSpectralFactor,singleSpectralDenominator] using
      b.tendstoLocallyUniformlyOn_canonicalProduct hp hp1
        (periodOneBoundaryPotential hp hp1 φ).val (periodOneBoundaryPotential hp hp1 φ).property
  spectrum := periodOneBoundaryCharacteristic_eq_zero_iff hp hp1
  multiplicity := analyticOrderAt_periodOneBoundaryCharacteristic hp hp1

/-- Continuity under complex perturbations and the literal real interlacing chain. -/
structure SourceLemma9_1RealData (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) : Prop where
  continuous : ∀ b : BoundaryCondition, ∀ n : ℤ,
    ContinuousAt (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n) φ
  norm_continuity : ∀ b : BoundaryCondition, ContinuousAt (sourceBoundaryDisplacement hp hp1 b) φ
  real : ∀ b : BoundaryCondition, ∀ n : ℤ, (canonicalPeriodOneBoundaryRoots hp hp1 b φ n).im = 0
  interlacing : ∀ b : BoundaryCondition, ∀ n : ℤ,
    let L := canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ)
    let R := canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ)
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 b φ n
    (R (n-1)).re < (L n).re ∧ (L n).re ≤ μ.re ∧ μ.re ≤ (R n).re ∧ (R n).re < (L (n+1)).re
  signed_level : ∀ b : BoundaryCondition, ∀ n : ℤ,
    2 ≤ (-1 : ℝ)^n * (canonicalDiscriminant hp (periodOnePotential φ)
      (canonicalPeriodOneBoundaryRoots hp hp1 b φ n)).re

/-- Lemma 9.1(ii–iii), including full displacement norm continuity. -/
theorem sourceLemma9_1_real (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) : SourceLemma9_1RealData hp hp1 φ where
  continuous := fun b => continuousAt_canonicalPeriodOneBoundaryRoots_of_realType hp hp1 b φ hφ
  norm_continuity := by
    obtain ⟨W,_,hW,hA⟩ := exists_sourceBoundaryDisplacement_analytic_common_domain hp hp1
    exact fun b => (hA b φ (hW hφ)).continuousAt
  real := fun b => canonicalPeriodOneBoundaryRoots_im_eq_zero hp hp1 b φ hφ
  interlacing := fun b => canonicalPeriodOneBoundaryRoots_interlacing_chain hp hp1 b φ hφ
  signed_level := fun b => signed_discriminant_periodOneBoundaryRoot_ge_two hp hp1 b φ hφ

/-- Above two, the characteristic extends the physical Hilbert characteristic. -/
theorem sourceBoundaryCharacteristic_eq_l2_of_two_le (hp : p ≠ ⊤) (hp1 : 1 < p)
    (h2p : 2 ≤ p) (b : BoundaryCondition) (φ : CoeffPair 2) (z : ℂ) :
    periodOneBoundaryCharacteristic hp hp1 b (CoeffPair.exponentInclusion h2p φ) z =
      l2SeparatedCharacteristic b (sourcePhysicalL2 φ) z :=
  (congrFun (periodOneBoundaryCharacteristic_exponent (by simp) hp (by norm_num) hp1 h2p b φ) z).symm.trans
    (periodOneBoundaryCharacteristic_eq_l2 b φ z)

/-- Below two, it restricts the physical Hilbert characteristic along the inclusion. -/
theorem sourceBoundaryCharacteristic_eq_l2_of_le_two (hp : p ≠ ⊤) (hp1 : 1 < p)
    (hp2 : p ≤ 2) (b : BoundaryCondition) (φ : CoeffPair p) (z : ℂ) :
    periodOneBoundaryCharacteristic hp hp1 b φ z =
      l2SeparatedCharacteristic b (sourcePhysicalL2 (CoeffPair.exponentInclusion hp2 φ)) z :=
  (congrFun (periodOneBoundaryCharacteristic_exponent hp (by simp) hp1 (by norm_num) hp2 b φ) z).trans
    (periodOneBoundaryCharacteristic_eq_l2 b _ z)

/-- Agreement on finite Fourier inputs uniquely determines the continuous extension. -/
theorem sourceBoundaryCharacteristic_unique_continuous (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (z : ℂ) (F : CoeffPair p → ℂ) (hF : Continuous F)
    (hfinite : ∀ a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ),
      F (CoeffPair.ofFinsupp (p := p) a) = classicalSeparatedCharacteristic b (finiteSourceCurve a) z) :
    F = fun φ => periodOneBoundaryCharacteristic hp hp1 b φ z := by
  have hc : Continuous (fun φ : CoeffPair p => periodOneBoundaryCharacteristic hp hp1 b φ z) := by
    apply continuous_iff_continuousAt.mpr
    intro φ
    have hpair : AnalyticAt ℂ (fun ψ : CoeffPair p => (z,ψ)) φ := analyticAt_const.prod analyticAt_id
    exact ((analyticOnNhd_periodOneBoundaryCharacteristic_joint hp hp1 b
      (z,φ) (mem_univ _)).comp (f := fun ψ : CoeffPair p => (z,ψ)) hpair).continuousAt
  apply (denseRange_finiteSourcePairs hp).equalizer hF hc
  funext a
  exact (hfinite a).trans (periodOneBoundaryCharacteristic_finite_eq_classical_all hp hp1 b a z).symm

/-- All three parts of Lemma 9.1, with their original source quantifiers. -/
theorem sourceLemma9_1 (hp : p ≠ ⊤) (hp1 : 1 < p) :
    SourceLemma9_1Data hp hp1 ∧ ∀ φ : CoeffPair p,
      IsRealType (CoeffPair.toMax p φ) → SourceLemma9_1RealData hp hp1 φ :=
  ⟨sourceLemma9_1_data hp hp1,sourceLemma9_1_real hp hp1⟩

/-- One original neighborhood controls both boundary sequences at every signed index. -/
theorem SourceLemma9_1RealData.exists_uniform_coordinate_neighborhood
    {hp : p ≠ ⊤} {hp1 : 1 < p} {φ : CoeffPair p} (D : SourceLemma9_1RealData hp hp1 φ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧ ∀ ψ ∈ V, ∀ b : BoundaryCondition, ∀ n : ℤ,
      ‖canonicalPeriodOneBoundaryRoots hp hp1 b ψ n-canonicalPeriodOneBoundaryRoots hp hp1 b φ n‖ < ε := by
  obtain ⟨δD,hD,hdD⟩ := Metric.continuousAt_iff.mp (D.norm_continuity .dirichlet) ε hε
  obtain ⟨δN,hN,hdN⟩ := Metric.continuousAt_iff.mp (D.norm_continuity .neumann) ε hε
  refine ⟨Metric.ball φ δD ∩ Metric.ball φ δN,Metric.isOpen_ball.inter Metric.isOpen_ball,
    ⟨Metric.mem_ball_self hD,Metric.mem_ball_self hN⟩,?_⟩
  intro ψ hψ b n
  have hb : ‖sourceBoundaryDisplacement hp hp1 b ψ-sourceBoundaryDisplacement hp hp1 b φ‖ < ε := by
    cases b
    · simpa only [dist_eq_norm] using hdD hψ.1
    · simpa only [dist_eq_norm] using hdN hψ.2
  have h := (lp.norm_apply_le_norm ((zero_lt_one.trans hp1).ne')
    (sourceBoundaryDisplacement hp hp1 b ψ-sourceBoundaryDisplacement hp hp1 b φ) n).trans_lt hb
  simpa only [lp.coeFn_sub,Pi.sub_apply,sourceBoundaryDisplacement_apply,sub_sub_sub_cancel_right] using h

end NLS.ZakharovShabat
