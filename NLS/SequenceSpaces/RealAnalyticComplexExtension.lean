import NLS.SequenceSpaces.MultilinearComplexification
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Analytic.Constructions

/-! # Holomorphic extensions of real analytic coefficient germs

Complexify the multilinear coefficients with their exponential norm bound.
The resulting series has at least half the original convergence radius and
agrees exactly on real arguments. Translating the series gives local complex
extensions at arbitrary real centers, including infinite-exponent spaces.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal NNReal
namespace NLS.Coeff.Complexification
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Extend every coefficient of a real formal power series. -/
def complexifySeries (P : FormalMultilinearSeries ℝ (RealCoeff p) F) :
    FormalMultilinearSeries ℂ (Coeff p) F := fun n => complexifyMultilinear n (P n)

/-- Uniform exponential bound on the extended coefficients. -/
theorem norm_complexifySeries_le (P : FormalMultilinearSeries ℝ (RealCoeff p) F) (n : ℕ) :
    ‖complexifySeries P n‖ ≤ 2^n*‖P n‖ := norm_complexifyMultilinear_apply_le n (P n)

/-- The complex power series keeps at least half the original radius. -/
theorem half_radius_le_complexifySeries (P : FormalMultilinearSeries ℝ (RealCoeff p) F) :
    P.radius/2 ≤ (complexifySeries P).radius := by
  apply ENNReal.le_of_forall_nnreal_lt
  intro r hr
  have hr' : ((r*2 : ℝ≥0) : ℝ≥0∞) < P.radius := by
    simpa only [ENNReal.coe_mul,ENNReal.coe_ofNat] using
      (ENNReal.lt_div_iff_mul_lt (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ 0))
        (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))).mp hr
  obtain ⟨C,_,hC⟩ := P.norm_mul_pow_le_of_lt_radius hr'
  apply (complexifySeries P).le_radius_of_bound C
  intro n
  calc
    ‖complexifySeries P n‖*(r : ℝ)^n ≤ (2^n*‖P n‖)*(r : ℝ)^n := by
      gcongr
      exact norm_complexifySeries_le P n
    _ = ‖P n‖*((r*2 : ℝ≥0) : ℝ)^n := by simp only [NNReal.coe_mul,NNReal.coe_ofNat,mul_pow]; ring
    _ ≤ C := hC n

/-- A real analytic series extends with a positive complex convergence radius. -/
theorem radius_complexifySeries_pos (P : FormalMultilinearSeries ℝ (RealCoeff p) F)
    (hP : 0 < P.radius) : 0 < (complexifySeries P).radius :=
  (ENNReal.div_pos hP.ne' (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).trans_le (half_radius_le_complexifySeries P)

/-- The sums agree on every real argument, term by term. -/
@[simp] theorem complexifySeries_sum_real (P : FormalMultilinearSeries ℝ (RealCoeff p) F)
    (x : RealCoeff p) : (complexifySeries P).sum (RealCoeff.complexCLM p x) = P.sum x := by
  apply tsum_congr
  intro n
  exact complexifyMultilinear_real n (P n) (fun _ => x)

variable [CompleteSpace F]

/-- Every real analytic germ on real coefficient space has a holomorphic extension
at its actual included center, agreeing with the original map on a real neighborhood. -/
theorem exists_complex_extension_of_analyticAt
    {f : RealCoeff p → F} {x : RealCoeff p} (hf : AnalyticAt ℝ f x) :
    ∃ g : Coeff p → F, AnalyticAt ℂ g (RealCoeff.complexCLM p x) ∧
      (fun y => g (RealCoeff.complexCLM p y)) =ᶠ[𝓝 x] f := by
  obtain ⟨P,r,hP⟩ := hf
  let Q := complexifySeries P
  have hQ : 0 < Q.radius := radius_complexifySeries_pos P hP.radius_pos
  refine ⟨fun z => Q.sum (z-RealCoeff.complexCLM p x),?_,?_⟩
  · exact (Q.hasFPowerSeriesOnBall hQ).analyticAt.comp_of_eq
      (f := fun z => z-RealCoeff.complexCLM p x)
      (analyticAt_id.sub analyticAt_const) (sub_self _)
  · have ht : Tendsto (fun y : RealCoeff p => y-x) (𝓝 x) (𝓝 0) := by
      have hc : Continuous (fun y : RealCoeff p => y-x) := continuous_id.sub continuous_const
      simpa only [sub_self] using hc.tendsto x
    filter_upwards [ht (Metric.eball_mem_nhds (0 : RealCoeff p) hP.r_pos)] with y hy
    rw [← map_sub,complexifySeries_sum_real]
    have hh := hP.sum hy
    simpa only [add_sub_cancel] using hh.symm

end NLS.Coeff.Complexification
