import NLS.ZakharovShabat.SourceNormalizedWeightedActionCalibration
import NLS.ZakharovShabat.SourceNormalizedActionComplexAllCoordinates
import NLS.ZakharovShabat.SourceHolomorphicRealCenteredBalls
import NLS.SequenceSpaces.LocallyBoundedRealization

/-! The actual Cauchy normalized zeroth action agrees with the canonical
normalized action on a common complex ball. Its regular deviation is a
bounded analytic Hilbert packet, including closed gaps. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
variable {W : Set (CoeffPair 2)}

theorem exists_ball_normalizedWeightedAction_zero_l2
    (C : SourceFullAbelianUniformCauchyFamily (by norm_num) (by norm_num) W)
    (φ : realTypeSourceSubmodule 2) (hφC : φ.val∈ball C.discs.source.val C.discs.sourceRadius) :
    ∃ r : ℝ, 0<r ∧ ball φ.val r⊆ball C.discs.source.val C.discs.sourceRadius ∧
      (∀ ψ∈ball φ.val r, ∀ n : ℤ, C.normalizedWeightedAction n 0 ψ=
        sourceNormalizedActionComplexExtension (by norm_num) (by norm_num) n ψ) ∧
      ∃ M : ℝ, 0≤M ∧ ∃ G : CoeffPair 2 → Coeff 2,
        AnalyticOnNhd ℂ G (ball φ.val r) ∧
        (∀ ψ∈ball φ.val r, ∀ n : ℤ, G ψ n=4*C.normalizedWeightedAction n 0 ψ-1) ∧
        ∀ ψ∈ball φ.val r, ‖G ψ‖≤M := by
  obtain ⟨V,hV,hφV,M,hdiff,hbound⟩ :=
    exists_local_sourceNormalizedActionComplexExtension_allCoordinates_boundedCoeff (q := 2)
      (by norm_num : (2 : ℝ≥0∞)≠⊤) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) φ.val φ.property
  obtain ⟨a,ha,hasub,hNa⟩ := C.exists_ball_normalizedWeightedActions
    (sourceHigherActionAtlas (by norm_num) (by norm_num)) φ hφC
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp
    ((hV.inter isOpen_ball).mem_nhds ⟨hφV,mem_ball_self ha⟩)
  let U := ball φ.val r
  have hUC (ψ : CoeffPair 2) (hψ : ψ∈U) := (hasub (hsub hψ).2).2
  have hN (n : ℤ) := ((hNa n 0).1).mono (fun ψ hψ => (hsub hψ).2)
  have he (ψ : CoeffPair 2) (hψ : ψ∈U) (n : ℤ) : C.normalizedWeightedAction n 0 ψ=
      sourceNormalizedActionComplexExtension (by norm_num) (by norm_num) n ψ := by
    have h := eqOn_sourceRealCenteredBalls_of_real_agreement
      (by norm_num : (2 : ℝ≥0∞)≠⊤) ⟨φ.val,φ.property⟩ ⟨φ.val,φ.property⟩ r r
      (C.normalizedWeightedAction n 0)
      (sourceNormalizedActionComplexExtension (by norm_num) (by norm_num) n)
      (hN n).differentiableOn ((hdiff n).mono (fun χ hχ => (hsub hχ).1)) (by
        intro χ hχ
        exact C.normalizedWeightedAction_zero_eq_canonical ⟨χ.val,χ.property⟩ (hUC χ.val hχ.1) n)
    exact h ⟨hψ,hψ⟩
  let f := fun ψ n => 4*C.normalizedWeightedAction n 0 ψ-1
  have hb (ψ : CoeffPair 2) (hψ : ψ∈U) : ∃ b : Coeff 2, (∀ n, b n=f ψ n) ∧ ‖b‖≤M := by
    obtain ⟨b,hb,hbn⟩ := hbound ψ (hsub hψ).1
    refine ⟨b,?_,hbn⟩
    intro n
    rw [hb n]
    change 4*sourceNormalizedActionComplexExtension (by norm_num) (by norm_num) n ψ-1=_
    rw [←he ψ hψ n]
  have hM : 0≤M := by
    obtain ⟨b,_hb,hbn⟩ := hb φ.val (mem_ball_self hr)
    exact (norm_nonneg b).trans hbn
  have hf (n : ℤ) : AnalyticOnNhd ℂ (fun ψ => f ψ n) U :=
    (analyticOnNhd_const.mul (hN n)).sub analyticOnNhd_const
  obtain ⟨hval,hG⟩ := Coeff.analytic_realization_of_local_bounds (r := 2) f isOpen_ball hf
    (fun ψ hψ => ⟨U,isOpen_ball,hψ,Subset.refl _,M,hb⟩)
  refine ⟨r,hr,hUC,he,M,hM,(fun ψ => Coeff.ofFunctionOrZero 2 (f ψ)),hG,hval,?_⟩
  intro ψ hψ
  obtain ⟨b,hb,hbn⟩ := hb ψ hψ
  change ‖Coeff.ofFunctionOrZero 2 (f ψ)‖≤M
  rwa [Coeff.ofFunctionOrZero_eq_of_coordinates _ b hb]

end NLS.ZakharovShabat.SourceFullAbelianUniformCauchyFamily
