import NLS.SequenceSpaces.PhysicalRealImag
import NLS.ComplexAnalysis.ContinuousRealFormIdentity

/-! Analytic uniqueness from the physical real form in EVERY symmetric
weighted Banach sequence space, at an arbitrary real base point. -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.WeightedCoeff

theorem physical_real_form_identity {p : ℝ≥0∞} [Fact (1≤p)]
    (w : Weight) (hw : ∀ j,w (-j)=w j)
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
    (U : Set (WeightedCoeff w p)) (hU : IsOpen U) (hc : IsPreconnected U)
    (q : WeightedCoeff w p) (hq : q∈U) (hqr : conjugateReflection w hw q=q)
    (F G : WeightedCoeff w p → Y) (hF : AnalyticOnNhd ℂ F U) (hG : AnalyticOnNhd ℂ G U)
    (he : ∀ a∈U, conjugateReflection w hw a=a → F a=G a) : EqOn F G U := by
  let R := {a : WeightedCoeff w p | conjugateReflection w hw a=a}
  have hRadd : ∀ {x y : WeightedCoeff w p}, x∈R → y∈R → x+y∈R := by
    intro x y hx hy
    change conjugateReflection w hw (x+y)=x+y
    rw [conjugateReflection_add,show conjugateReflection w hw x=x from hx,
      show conjugateReflection w hw y=y from hy]
  have hRsmul : ∀ t : ℝ, ∀ {x : WeightedCoeff w p}, x∈R → (t:ℂ) • x∈R := by
    intro t x hx
    change conjugateReflection w hw ((t:ℂ) • x)=(t:ℂ) • x
    rw [conjugateReflection_smul,conj_ofReal,show conjugateReflection w hw x=x from hx]
  have hz := NLS.ComplexAnalysis.AnalyticOnNhd.eqOn_zero_of_continuous_real_form R
    (fun _ _ hx hy => hRadd hx hy) (fun t _ hx => hRsmul t hx)
    (physicalRealPart w hw) (physicalImagPart w hw)
    (conjugateReflection_physicalRealPart w hw) (conjugateReflection_physicalImagPart w hw)
    (fun a => (physicalRealPart_add_I_physicalImagPart w hw a).symm)
    (continuous_physicalRealPart w hw).continuousAt (physicalRealPart_zero w hw)
    (continuous_physicalImagPart w hw).continuousAt (physicalImagPart_zero w hw)
    U hU hc ⟨q,hq,hqr⟩ (F-G) (hF.sub hG) (fun a ha hr => sub_eq_zero.mpr (he a ha hr))
  exact fun a ha => sub_eq_zero.mp (hz ha)

end NLS.WeightedCoeff
