import NLS.FunctionalAnalysis.CompactUnitIntervalPrimitive
import NLS.FunctionalAnalysis.WeakDerivativeConstant

/-! # Zero weak derivative is constant on the original open interval

Only compact tests supported strictly inside (0,1) are used. No boundary
trace or periodic extension is assumed.
-/
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff
namespace NLS.FunctionalAnalysis

theorem ae_eq_const_on_unitInterval_of_weak_derivative_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : ℝ → E) (hf : LocallyIntegrable f volume)
    (hw : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo (0:ℝ) 1 → (∫ x : ℝ, deriv ψ x • f x)=0) :
    ∃ c : E, f =ᵐ[volume.restrict (Ioc (0:ℝ) 1)] fun _ => c := by
  let B : ContDiffBump (1/2:ℝ) := ⟨1/8,1/4,by norm_num,by norm_num⟩
  let ρ : ℝ → ℝ := B.normed volume
  have hρ : ContDiff ℝ ∞ ρ := B.contDiff_normed (n := ⊤)
  have hρc : HasCompactSupport ρ := B.hasCompactSupport_normed
  have hρi : Integrable ρ volume := B.integrable_normed
  have hρ1 : (∫ x : ℝ, ρ x)=1 := B.integral_normed
  have hρs : tsupport ρ ⊆ Ioo (0:ℝ) 1 := by
    rw [B.tsupport_normed_eq]
    intro x hx
    have h := abs_le.mp (show |x-(1/2:ℝ)| ≤ 1/4 from by simpa [Metric.mem_closedBall,Real.dist_eq,B] using hx)
    constructor <;> linarith [h.1,h.2]
  let c := ∫ x : ℝ, ρ x • f x
  have hc : LocallyIntegrable (fun _ : ℝ => c) volume := continuous_const.locallyIntegrable
  have hz : ∀ᵐ x : ℝ, x ∈ Ioo (0:ℝ) 1 → f x-c=0 := by
    apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((hf.sub hc).locallyIntegrableOn _)
    intro χ hχ hχc hχs
    let d := ∫ x : ℝ, χ x
    let ψ : ℝ → ℝ := fun x => χ x-d*ρ x
    have hψ : ContDiff ℝ ∞ ψ := hχ.sub (hρ.const_smul d)
    have hψc : HasCompactSupport ψ := hχc.sub (hρc.smul_left (f := fun _ : ℝ => d))
    have hψs : tsupport ψ ⊆ Ioo (0:ℝ) 1 :=
      (tsupport_sub χ (fun x => d*ρ x)).trans
        (union_subset hχs ((tsupport_mul_subset_right (f := fun _ => d) (g := ρ)).trans hρs))
    have hψi : (∫ x : ℝ, ψ x)=0 := by
      change (∫ x : ℝ, χ x-d*ρ x)=0
      rw [integral_sub (hχ.continuous.integrable_of_hasCompactSupport hχc) (hρi.const_mul d),
        integral_const_mul,hρ1,mul_one]
      exact sub_self d
    obtain ⟨F,hF,hFc,hFs,hFd⟩ := exists_compact_unitInterval_primitive ψ hψ hψc hψs hψi
    have h := hw F hF hFc hFs
    rw [show deriv F=ψ from funext fun x => (hFd x).deriv] at h
    have hiχ := hf.integrable_smul_left_of_hasCompactSupport hχ.continuous hχc
    have hiρ := hf.integrable_smul_left_of_hasCompactSupport hρ.continuous hρc
    change (∫ x : ℝ, (χ x-d*ρ x) • f x)=0 at h
    simp only [sub_smul,mul_smul] at h
    have his : Integrable (fun x => d • (ρ x • f x)) volume := by
      simpa only [Pi.smul_apply] using! hiρ.smul d
    rw [integral_sub hiχ his,integral_smul] at h
    simp only [Pi.sub_apply,smul_sub]
    rw [integral_sub hiχ (hc.integrable_smul_left_of_hasCompactSupport hχ.continuous hχc),
      integral_smul_const]
    exact h
  refine ⟨c,?_⟩
  rw [← restrict_Ioo_eq_restrict_Ioc]
  exact (ae_restrict_iff' measurableSet_Ioo).mpr (hz.mono fun x hx hxi => sub_eq_zero.mp (hx hxi))

end NLS.FunctionalAnalysis
