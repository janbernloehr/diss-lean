import NLS.KdV.HillL2MomentSeriesBound
import NLS.KdV.HillMomentWeightedSeriesAnalytic
import NLS.SequenceSpaces.UnweightedPositiveMomentSeries
import NLS.SequenceSpaces.LocallyBoundedRealization
import NLS.FunctionalAnalysis.OpenMajorantNeighborhood

/-! Unweighted lp analyticity of the original moment sequence, on a
complex L2 neighborhood chosen before every exponent p > 1 and every index. -/
noncomputable section
open Set Complex NLS.ZakharovShabat NLS.LpSequence
open scoped ENNReal
namespace NLS.KdV.HillProductEquationPatch

private theorem moment_lp_of_majorants {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p) (P : HillProductEquationPatch)
    (D : P.MomentSeriesNeighborhood) (a : PeriodOneHminusOne)
    (hfull : ∀ n m : ℕ+,
      ‖(2*Real.pi:ℂ)⁻¹*P.centeredMoment D.ambient n m 1 a‖ ≤
        D.constant*‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (P.sourcePsi a) (m:ℤ)‖^2*
          (if m=n then 1 else 1/|((n:ℕ):ℝ)-(m:ℕ)|+1/((n:ℕ)+(m:ℕ):ℝ)))
    (G E : Coeff 2) (M : ℝ) (hGE : ‖G‖+‖E‖ ≤ M)
    (hw : ∀ m : ℕ+, (1+(m:ℝ))*(
      ‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (P.sourcePsi a) ((m:ℕ):ℤ)‖+
        ‖P.physicalAbelianMidpointDisplacement a ((m:ℕ):ℤ)‖) ≤
          ‖G ((m:ℕ):ℤ)‖+‖E ((m:ℕ):ℤ)‖) :
    ∃ b : Coeff p, (∀ k, b k = positiveScalarExtension
      (fun n => P.centeredSecondMomentSeries D.ambient n a) k) ∧
      ‖b‖ ≤ (2*(2*Real.pi*D.constant))*(1+3*‖Coeff.puncturedLattice p hp‖)*M^2 := by
  let H : Coeff 2 := Coeff.magnitude G+Coeff.magnitude E
  have hH (k : ℤ) : ‖H k‖=‖G k‖+‖E k‖ := by
    have he : H k=((‖G k‖+‖E k‖:ℝ):ℂ) := by
      simp only [H,lp.coeFn_add,Pi.add_apply,Coeff.magnitude_apply,ofReal_add]
    rw [he,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
  have hnorm : ‖H‖ ≤ M := (norm_add_le _ _).trans (by
    simpa only [Coeff.norm_magnitude] using hGE)
  let g : ℕ+ → ℝ := fun m =>
    ‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (P.sourcePsi a) ((m:ℕ):ℤ)‖
  have hweight (m : ℕ+) : (1+(m:ℝ))*g m ≤ ‖H ((m:ℕ):ℤ)‖ := by
    rw [hH]
    exact (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (norm_nonneg _))
      (by positivity : 0 ≤ 1+(m:ℝ))).trans (hw m)
  have hC := D.constant_pos
  have hu (i m : ℕ+) : ‖P.centeredMoment D.ambient i m 1 a‖ ≤
      (2*Real.pi*D.constant)*(g m)^2*
        (if m=i then 1 else 1/|((i:ℕ):ℝ)-(m:ℕ)|+1/((i:ℕ)+(m:ℕ):ℝ)) := by
    have he (z : ℂ) : ‖z‖=2*Real.pi*‖(2*Real.pi:ℂ)⁻¹*z‖ := by
      simp only [norm_mul,norm_inv,norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
      field_simp
    rw [he (P.centeredMoment D.ambient i m 1 a)]
    simpa only [g,mul_assoc] using mul_le_mul_of_nonneg_left (hfull i m) (by positivity : 0 ≤ 2*Real.pi)
  obtain ⟨b,hb,hn⟩ := Coeff.exists_unweighted_positive_moment_series hp H g
    (fun _ => norm_nonneg _) hweight (fun i m => P.centeredMoment D.ambient i m 1 a)
      (2*Real.pi*D.constant) (by positivity) hu
  refine ⟨b,hb,hn.trans ?_⟩
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg H) hnorm 2) (by positivity)

def l2CenteredSecondMomentLpSequence (P : HillProductEquationPatch)
    (D : P.MomentSeriesNeighborhood) (p : ℝ≥0∞) (q : Coeff 2) : Coeff p :=
  Coeff.ofFunctionOrZero p (positiveScalarExtension
    (fun n => P.centeredSecondMomentSeries D.ambient n (periodOneL2Inclusion q)))

private theorem analytic_realization_of_uniform_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (f : E → ℤ → ℂ) (U : Set E)
    (hU : IsOpen U) (ha : ∀ k, AnalyticOnNhd ℂ (fun a => f a k) U)
    (R : ℝ) (hb : ∀ r ∈ U, ∃ b : Coeff p, (∀ k, b k=f r k) ∧ ‖b‖ ≤ R) :
    AnalyticOnNhd ℂ (fun r => Coeff.ofFunctionOrZero p (f r)) U ∧
      ∀ r ∈ U, ‖Coeff.ofFunctionOrZero p (f r)‖ ≤ R ∧
        ∀ k, Coeff.ofFunctionOrZero p (f r) k = f r k := by
  obtain ⟨hc,hA⟩ := Coeff.analytic_realization_of_local_bounds f hU ha (by
    intro r hrU
    exact ⟨U,hU,hrU,Subset.rfl,R,hb⟩)
  refine ⟨hA,fun r hrU => ⟨?_,hc r hrU⟩⟩
  obtain ⟨b,hb,hbn⟩ := hb r hrU
  rwa [Coeff.ofFunctionOrZero_eq_of_coordinates _ b hb]

def L2FrequencyMomentBound (P : HillProductEquationPatch) (D : P.MomentSeriesNeighborhood) : Prop :=
  ∀ a ∈ D.source, ∀ n m : ℕ+,
      ‖(2*Real.pi:ℂ)⁻¹*P.centeredMoment D.ambient n m 1 a‖ ≤
        D.constant*‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (P.sourcePsi a) (m:ℤ)‖^2*
          (if m=n then 1 else 1/|((n:ℕ):ℝ)-(m:ℕ)|+1/((n:ℕ)+(m:ℕ):ℝ))

def L2FrequencyHilbertMajorant (P : HillProductEquationPatch) (r : Coeff 2) (M : ℝ) : Prop :=
  ∃ G E : Coeff 2, ‖G‖+‖E‖ ≤ M ∧ ∀ n : ℕ+,
      (1+(n:ℝ))*(‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num)
        (P.sourcePsi (periodOneL2Inclusion r)) ((n:ℕ):ℤ)‖+
          ‖P.physicalAbelianMidpointDisplacement (periodOneL2Inclusion r) ((n:ℕ):ℤ)‖) ≤
            ‖G ((n:ℕ):ℤ)‖+‖E ((n:ℕ):ℤ)‖

theorem l2MomentLp_analytic_of_majorants
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p)
    (P : HillProductEquationPatch) (D : P.MomentSeriesNeighborhood)
    (hfull : P.L2FrequencyMomentBound D)
    (U : Set (Coeff 2)) (hU : IsOpen U)
    (hUD : ∀ r ∈ U, periodOneL2Inclusion r ∈ D.source)
    (M : ℝ)
    (hweights : ∀ r ∈ U, P.L2FrequencyHilbertMajorant r M) :
    AnalyticOnNhd ℂ (P.l2CenteredSecondMomentLpSequence D p) U ∧
      ∃ R : ℝ, 0 ≤ R ∧ ∀ r ∈ U,
        ‖P.l2CenteredSecondMomentLpSequence D p r‖ ≤ R ∧
        ∀ k, P.l2CenteredSecondMomentLpSequence D p r k = positiveScalarExtension
          (fun n => P.centeredSecondMomentSeries D.ambient n (periodOneL2Inclusion r)) k := by
  let R := (2*(2*Real.pi*D.constant))*(1+3*‖Coeff.puncturedLattice p hp‖)*M^2
  have hC := D.constant_pos
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hb (r : Coeff 2) (hrU : r ∈ U) :
      ∃ b : Coeff p, (∀ k, b k = positiveScalarExtension
        (fun n => P.centeredSecondMomentSeries D.ambient n (periodOneL2Inclusion r)) k) ∧ ‖b‖ ≤ R := by
    obtain ⟨G,E,hGE,hw⟩ := hweights r hrU
    exact moment_lp_of_majorants hp P D _ (hfull _ (hUD r hrU)) G E M hGE hw
  have ha (k : ℤ) : AnalyticOnNhd ℂ (fun r : Coeff 2 => positiveScalarExtension
      (fun n => P.centeredSecondMomentSeries D.ambient n (periodOneL2Inclusion r)) k) U := by
    intro r hrU
    exact (P.analytic_positive_centeredSecondMomentSeries D k _ (hUD r hrU)).comp
      (periodOneL2Inclusion.analyticAt r)
  obtain ⟨hA,hdata⟩ := analytic_realization_of_uniform_bound _ U hU ha R hb
  exact ⟨hA,R,hR,hdata⟩




end NLS.KdV.HillProductEquationPatch
