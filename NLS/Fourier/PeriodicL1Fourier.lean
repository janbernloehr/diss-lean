import NLS.Fourier.PeriodicRiemannLebesgue
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
/-!
# The periodic L¹ Fourier transform into c₀

The actual L¹ quotient on the physical circle maps continuously and complex
linearly to continuous functions on the discrete integers vanishing at infinity.
Its operator norm is exactly one for normalized Haar measure. Its range is dense:
finite coefficient cutoffs are realized by physical trigonometric polynomials.
This does not assert surjectivity; the second claim in Remark A.6 remains open.
-/

noncomputable section
open Set MeasureTheory Filter Topology
open scoped ENNReal ZeroAtInfty
namespace NLS.Fourier
variable {L : ℝ} [Fact (0 < L)]

/-- Fourier coefficients packaged as an actual c₀ sequence. -/
def circleFourierC0 (f : AddCircle L → ℂ) : C₀(ℤ,ℂ) where
  toFun := fourierCoeff f
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    rw [Filter.cocompact_eq_cofinite]
    exact tendsto_fourierCoeff_cofinite f

@[simp] theorem circleFourierC0_apply (f : AddCircle L → ℂ) (n : ℤ) :
    circleFourierC0 f n = fourierCoeff f n := rfl

/-- The normalized L¹ bound on each physical Fourier coefficient. -/
theorem norm_fourierCoeff_le_integral_norm (f : AddCircle L → ℂ) (n : ℤ) :
    ‖fourierCoeff f n‖ ≤ ∫ x, ‖f x‖ ∂AddCircle.haarAddCircle := by
  calc
    _ ≤ ∫ x, ‖fourier (-n) x • f x‖ ∂AddCircle.haarAddCircle := norm_integral_le_integral_norm _
    _ = _ := by simp only [norm_smul,fourier_apply,Circle.norm_coe,one_mul]

/-- The c₀ uniform norm has the same constant-one L¹ bound. -/
theorem norm_circleFourierC0_le (f : AddCircle L → ℂ) :
    ‖circleFourierC0 f‖ ≤ ∫ x, ‖f x‖ ∂AddCircle.haarAddCircle := by
  apply (BoundedContinuousFunction.norm_le (integral_nonneg (fun _ => norm_nonneg _))).mpr
  exact norm_fourierCoeff_le_integral_norm f

/-- The Fourier transform on the actual L¹ quotient, with target c₀. -/
def circleL1Fourier : Lp ℂ 1 (AddCircle.haarAddCircle (T := L)) →L[ℂ] C₀(ℤ,ℂ) :=
  let F : Lp ℂ 1 (AddCircle.haarAddCircle (T := L)) →ₗ[ℂ] C₀(ℤ,ℂ) := {
    toFun f := circleFourierC0 f
    map_add' f g := by
      ext n
      change fourierCoeff (f + g) n = fourierCoeff f n + fourierCoeff g n
      rw [fourierCoeff_congr_ae (Lp.coeFn_add f g),fourierCoeff.add (L1.integrable_coeFn f) (L1.integrable_coeFn g)]
      rfl
    map_smul' c f := by
      ext n
      change fourierCoeff (c • f) n = c • fourierCoeff f n
      rw [fourierCoeff_congr_ae (Lp.coeFn_smul c f),fourierCoeff.const_smul] }
  F.mkContinuous 1 (by
    intro f
    simpa only [F,LinearMap.coe_mk,AddHom.coe_mk,one_mul,L1.norm_eq_integral_norm] using norm_circleFourierC0_le (f : AddCircle L → ℂ))

@[simp] theorem circleL1Fourier_apply (f : Lp ℂ 1 (AddCircle.haarAddCircle (T := L))) (n : ℤ) :
    circleL1Fourier f n = fourierCoeff f n := rfl

/-- The L¹-to-c₀ transform is a contraction. -/
theorem norm_circleL1Fourier_le : ‖circleL1Fourier (L := L)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖circleFourierC0 (f : AddCircle L → ℂ)‖ ≤ 1*‖f‖
  simpa only [one_mul,L1.norm_eq_integral_norm] using norm_circleFourierC0_le (f : AddCircle L → ℂ)

/-- Physical trigonometric polynomials realize every finite coefficient cutoff. -/
theorem circleL1Fourier_polynomial (S : Finset ℤ) (a : ℤ → ℂ) (n : ℤ) :
    circleL1Fourier (ContinuousMap.toLp 1 AddCircle.haarAddCircle ℂ
      (continuousFourierPolynomial (L := L) S a)) n = if n ∈ S then a n else 0 := by
  rw [circleL1Fourier_apply,fourierCoeff_congr_ae (ContinuousMap.coeFn_toLp _ _),continuousFourierPolynomial_coefficient]

/-- The image is dense in c₀ in the uniform coefficient norm. -/
theorem denseRange_circleL1Fourier : DenseRange (circleL1Fourier (L := L)) := by
  rw [Metric.denseRange_iff]
  intro a ε hε
  have h := Metric.tendsto_nhds.mp (zero_at_infty a) (ε/2) (half_pos hε)
  rw [Filter.cocompact_eq_cofinite] at h
  have hfin : {n : ℤ | ¬ ‖a n‖ < ε/2}.Finite := by
    simpa only [dist_zero_right,Filter.eventually_cofinite] using h
  let S := hfin.toFinset
  let f := ContinuousMap.toLp 1 AddCircle.haarAddCircle ℂ (continuousFourierPolynomial (L := L) S a)
  refine ⟨f,?_⟩
  have hle : ‖circleL1Fourier f - a‖ ≤ ε/2 := by
    apply (BoundedContinuousFunction.norm_le (half_pos hε).le).mpr
    intro n
    change ‖circleL1Fourier f n - a n‖ ≤ ε/2
    rw [show f = _ from rfl,circleL1Fourier_polynomial]
    split_ifs with hn
    · simp only [sub_self,norm_zero]; exact (half_pos hε).le
    · have hn' : ‖a n‖ < ε/2 := by
        simpa only [S,Set.Finite.mem_toFinset,mem_ofPred_eq,not_not] using hn
      simpa only [zero_sub,norm_neg] using hn'.le
  rw [dist_comm,dist_eq_norm]
  exact hle.trans_lt (half_lt_self hε)

/-- The constant function attains the sharp operator norm one. -/
theorem norm_circleL1Fourier : ‖circleL1Fourier (L := L)‖ = 1 := by
  apply le_antisymm norm_circleL1Fourier_le
  let g : C(AddCircle L,ℂ) := ContinuousMap.const _ 1
  let f := ContinuousMap.toLp 1 AddCircle.haarAddCircle ℂ g
  have hf : ‖f‖ = 1 := by
    rw [L1.norm_eq_integral_norm]
    have he : (fun x => ‖f x‖) =ᵐ[AddCircle.haarAddCircle] fun _ => (1:ℝ) := by
      filter_upwards [ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℂ) AddCircle.haarAddCircle g] with x hx
      simp only [f] at *
      rw [hx]
      simp [g]
    rw [integral_congr_ae he]
    simp
  have hc : circleL1Fourier f 0 = 1 := by
    rw [circleL1Fourier_apply,fourierCoeff_congr_ae (ContinuousMap.coeFn_toLp _ g)]
    simp [g,fourierCoeff]
  have h := (circleL1Fourier f).toBCF.norm_coe_le_norm 0
  change ‖circleL1Fourier f 0‖ ≤ ‖circleL1Fourier f‖ at h
  rw [hc,norm_one] at h
  exact h.trans (by simpa only [hf,mul_one] using circleL1Fourier.le_opNorm f)

end NLS.Fourier
