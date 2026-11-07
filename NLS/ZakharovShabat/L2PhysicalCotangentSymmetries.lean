import NLS.ZakharovShabat.L2SourceGradientUniqueness
import NLS.ZakharovShabat.SourceSymmetryCore
import NLS.Fourier.UnitFourierReflection

/-! # From full Hilbert cotangents to pointwise physical symmetries

Single Fourier directions and uniqueness recover both physical components.
This proves the transpose action for unconjugated complex gradients, including
pure midpoint reflection, without assuming a gradient transformation rule.
-/
noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra NLS.Fourier
namespace NLS.ZakharovShabat

def sourceFirstUnitMode (k : ℤ) : CoeffPair 2 := CoeffPair.ofFinsupp (Finsupp.single k 1,0)
def sourceSecondUnitMode (k : ℤ) : CoeffPair 2 := CoeffPair.ofFinsupp (0,Finsupp.single k 1)

theorem SourcePhysicalGradientRepresents.first_mode {L : CoeffPair 2 →L[ℂ] ℂ}
    {g : Curve (ℂ × ℂ)} (hg : SourcePhysicalGradientRepresents L g) (k : ℤ) :
    L (sourceFirstUnitMode k) = unitFourierCoefficient (fun x => (extend g x).1) (-k) :=
  (hg _).trans (source_physical_gradient_pairing_single_fst _ _)

theorem SourcePhysicalGradientRepresents.second_mode {L : CoeffPair 2 →L[ℂ] ℂ}
    {g : Curve (ℂ × ℂ)} (hg : SourcePhysicalGradientRepresents L g) (k : ℤ) :
    L (sourceSecondUnitMode k) = unitFourierCoefficient (fun x => (extend g x).2) (-k) :=
  (hg _).trans (source_physical_gradient_pairing_single_snd _ _)

private theorem eqOn_unit_of_coefficients (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g)
    (h : ∀ k, unitFourierCoefficient f k = unitFourierCoefficient g k) : EqOn f g (Icc 0 1) := by
  apply eqOn_Icc_of_intervalFourierCoefficient_eq (by norm_num : (0:ℝ) < 1) f g hf hg
  intro k
  rw [intervalFourierCoefficient_eq_fourierCoeffOn (by norm_num : (0:ℝ) < 1),
    intervalFourierCoefficient_eq_fourierCoeffOn (by norm_num : (0:ℝ) < 1),
    ← unitFourierCoefficient_eq_fourierCoeffOn,← unitFourierCoefficient_eq_fourierCoeffOn]
  exact h k

private theorem midpoint_first_mode (k : ℤ) :
    sourceMidpointReflection (sourceFirstUnitMode k) = sourceFirstUnitMode (-k) := by
  apply (CoeffPair.toMax 2).injective
  apply Prod.ext <;> ext j <;>
    simp [sourceFirstUnitMode,Coeff.reflection_apply,Finsupp.single_apply,eq_comm]
  all_goals split_ifs <;> simp_all

private theorem midpoint_second_mode (k : ℤ) :
    sourceMidpointReflection (sourceSecondUnitMode k) = sourceSecondUnitMode (-k) := by
  apply (CoeffPair.toMax 2).injective
  apply Prod.ext <;> ext j <;>
    simp [sourceSecondUnitMode,Coeff.reflection_apply,Finsupp.single_apply,eq_comm]
  all_goals split_ifs <;> simp_all

theorem SourcePhysicalGradientRepresents.componentSwap
    {L K : CoeffPair 2 →L[ℂ] ℂ} {g h : Curve (ℂ × ℂ)}
    (hg : SourcePhysicalGradientRepresents L g) (hh : SourcePhysicalGradientRepresents K h)
    (a : ℂ) (he : K.comp sourceComponentSwap.toContinuousLinearEquiv.toContinuousLinearMap = a • L)
    (x : Icc (0:ℝ) 1) : h x = a • ((g x).2,(g x).1) := by
  have hc₁ (k : ℤ) : unitFourierCoefficient (fun y => (extend h y).1) k =
      a*unitFourierCoefficient (fun y => (extend g y).2) k := by
    have e := congrArg (fun T : CoeffPair 2 →L[ℂ] ℂ => T (sourceSecondUnitMode (-k))) he
    change K (sourceComponentSwap (sourceSecondUnitMode (-k))) = a*L (sourceSecondUnitMode (-k)) at e
    have hm : sourceComponentSwap (sourceSecondUnitMode (-k)) = sourceFirstUnitMode (-k) := by
      rfl
    rw [hm,hh.first_mode,hg.second_mode] at e
    simpa only [neg_neg] using e
  have hc₂ (k : ℤ) : unitFourierCoefficient (fun y => (extend h y).2) k =
      a*unitFourierCoefficient (fun y => (extend g y).1) k := by
    have e := congrArg (fun T : CoeffPair 2 →L[ℂ] ℂ => T (sourceFirstUnitMode (-k))) he
    change K (sourceComponentSwap (sourceFirstUnitMode (-k))) = a*L (sourceFirstUnitMode (-k)) at e
    have hm : sourceComponentSwap (sourceFirstUnitMode (-k)) = sourceSecondUnitMode (-k) := by
      rfl
    rw [hm,hh.second_mode,hg.first_mode] at e
    simpa only [neg_neg] using e
  have h₁ := eqOn_unit_of_coefficients (fun y => (extend h y).1) (fun y => a*(extend g y).2)
    (continuous_extend h).fst ((continuous_extend g).snd.const_mul a) (fun k => by
      rw [unitFourierCoefficient_const_mul]; exact hc₁ k)
  have h₂ := eqOn_unit_of_coefficients (fun y => (extend h y).2) (fun y => a*(extend g y).1)
    (continuous_extend h).snd ((continuous_extend g).fst.const_mul a) (fun k => by
      rw [unitFourierCoefficient_const_mul]; exact hc₂ k)
  apply Prod.ext
  · simpa only [extend_coe,Prod.smul_fst,smul_eq_mul] using h₁ x.property
  · simpa only [extend_coe,Prod.smul_snd,smul_eq_mul] using h₂ x.property

theorem SourcePhysicalGradientRepresents.midpointReflection
    {L K : CoeffPair 2 →L[ℂ] ℂ} {g h : Curve (ℂ × ℂ)}
    (hg : SourcePhysicalGradientRepresents L g) (hh : SourcePhysicalGradientRepresents K h)
    (a : ℂ) (he : K.comp sourceMidpointReflection.toContinuousLinearEquiv.toContinuousLinearMap = a • L)
    (x : Icc (0:ℝ) 1) : h x = a • g ⟨1-x.val,by constructor <;> linarith [x.property.1,x.property.2]⟩ := by
  have hc₁ (k : ℤ) : unitFourierCoefficient (fun y => (extend h y).1) k =
      a*unitFourierCoefficient (fun y => (extend g y).1) (-k) := by
    have e := congrArg (fun T : CoeffPair 2 →L[ℂ] ℂ => T (sourceFirstUnitMode k)) he
    change K (sourceMidpointReflection (sourceFirstUnitMode k)) = a*L (sourceFirstUnitMode k) at e
    rw [midpoint_first_mode,hh.first_mode,hg.first_mode] at e
    simpa only [neg_neg] using e
  have hc₂ (k : ℤ) : unitFourierCoefficient (fun y => (extend h y).2) k =
      a*unitFourierCoefficient (fun y => (extend g y).2) (-k) := by
    have e := congrArg (fun T : CoeffPair 2 →L[ℂ] ℂ => T (sourceSecondUnitMode k)) he
    change K (sourceMidpointReflection (sourceSecondUnitMode k)) = a*L (sourceSecondUnitMode k) at e
    rw [midpoint_second_mode,hh.second_mode,hg.second_mode] at e
    simpa only [neg_neg] using e
  have h₁ := eqOn_unit_of_coefficients (fun y => (extend h y).1) (fun y => a*(extend g (1-y)).1)
    (continuous_extend h).fst (((continuous_extend g).fst.comp (continuous_const.sub continuous_id)).const_mul a) (fun k => by
      rw [unitFourierCoefficient_const_mul,unitFourierCoefficient_one_sub (fun t => (extend g t).1)]; exact hc₁ k)
  have h₂ := eqOn_unit_of_coefficients (fun y => (extend h y).2) (fun y => a*(extend g (1-y)).2)
    (continuous_extend h).snd (((continuous_extend g).snd.comp (continuous_const.sub continuous_id)).const_mul a) (fun k => by
      rw [unitFourierCoefficient_const_mul,unitFourierCoefficient_one_sub (fun t => (extend g t).2)]; exact hc₂ k)
  have hx : 1-x.val ∈ Icc (0:ℝ) 1 := by constructor <;> linarith [x.property.1,x.property.2]
  have hxe : extend g (1-x.val) = g ⟨1-x.val,hx⟩ := extend_coe g ⟨1-x.val,hx⟩
  apply Prod.ext
  · simpa only [extend_coe,hxe,Prod.smul_fst,smul_eq_mul] using h₁ x.property
  · simpa only [extend_coe,hxe,Prod.smul_snd,smul_eq_mul] using h₂ x.property

theorem SourcePhysicalGradientRepresents.reciprocalScaling
    {L K : CoeffPair 2 →L[ℂ] ℂ} {g h : Curve (ℂ × ℂ)}
    (hg : SourcePhysicalGradientRepresents L g) (hh : SourcePhysicalGradientRepresents K h)
    (c : ℂ) (he : K.comp (sourceReciprocalScaling c) = L)
    (x : Icc (0:ℝ) 1) : g x = (c*(h x).1,c⁻¹*(h x).2) := by
  have hmode₁ (k : ℤ) : sourceReciprocalScaling c (sourceFirstUnitMode k) = c • sourceFirstUnitMode k := by
    apply (CoeffPair.toMax 2).injective
    apply Prod.ext <;> ext j <;> simp [sourceFirstUnitMode,Finsupp.single_apply]
  have hmode₂ (k : ℤ) : sourceReciprocalScaling c (sourceSecondUnitMode k) = c⁻¹ • sourceSecondUnitMode k := by
    apply (CoeffPair.toMax 2).injective
    apply Prod.ext <;> ext j <;> simp [sourceSecondUnitMode,Finsupp.single_apply]
  have hc₁ (k : ℤ) : unitFourierCoefficient (fun y => (extend g y).1) k =
      c*unitFourierCoefficient (fun y => (extend h y).1) k := by
    have e := congrArg (fun T : CoeffPair 2 →L[ℂ] ℂ => T (sourceFirstUnitMode (-k))) he
    change K (sourceReciprocalScaling c (sourceFirstUnitMode (-k))) = L (sourceFirstUnitMode (-k)) at e
    rw [hmode₁,map_smul,hg.first_mode,hh.first_mode] at e
    simpa only [neg_neg,smul_eq_mul] using e.symm
  have hc₂ (k : ℤ) : unitFourierCoefficient (fun y => (extend g y).2) k =
      c⁻¹*unitFourierCoefficient (fun y => (extend h y).2) k := by
    have e := congrArg (fun T : CoeffPair 2 →L[ℂ] ℂ => T (sourceSecondUnitMode (-k))) he
    change K (sourceReciprocalScaling c (sourceSecondUnitMode (-k))) = L (sourceSecondUnitMode (-k)) at e
    rw [hmode₂,map_smul,hg.second_mode,hh.second_mode] at e
    simpa only [neg_neg,smul_eq_mul] using e.symm
  have h₁ := eqOn_unit_of_coefficients (fun y => (extend g y).1) (fun y => c*(extend h y).1)
    (continuous_extend g).fst ((continuous_extend h).fst.const_mul c) (fun k => by
      rw [unitFourierCoefficient_const_mul]; exact hc₁ k)
  have h₂ := eqOn_unit_of_coefficients (fun y => (extend g y).2) (fun y => c⁻¹*(extend h y).2)
    (continuous_extend g).snd ((continuous_extend h).snd.const_mul c⁻¹) (fun k => by
      rw [unitFourierCoefficient_const_mul]; exact hc₂ k)
  apply Prod.ext
  · simpa only [extend_coe] using h₁ x.property
  · simpa only [extend_coe] using h₂ x.property

end NLS.ZakharovShabat
