import NLS.KdV.ClassicalHillPotentialVariation
import NLS.KdV.ClassicalHillFreeFlow
import NLS.ComplexAnalysis.SecondOrderDuhamel

/-! Explicit ACTUAL free potential-variation kernels, with scalar initial
position/derivative normalization and arbitrary initial vector. The formulas
are Fréchet derivatives in the whole continuous-potential Banach space. -/
noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.KdV

theorem classicalHillPotentialVariation_free_sq (h : Curve ℂ) (z : ℂ) (hz : z ≠ 0)
    (v : ℂ × ℂ) (t : Icc (0:ℝ) 1) :
    (classicalHillPotentialVariation 0 h (z^2) v t).1 =
      ∫ s in (0:ℝ)..t.val, (sin (z*(t.val-s))/z)*extend h s*
        (cos (z*(s:ℂ))*v.1+sin (z*(s:ℂ))/z*v.2) ∧
    (classicalHillPotentialVariation 0 h (z^2) v t).2 =
      ∫ s in (0:ℝ)..t.val, cos (z*(t.val-s))*extend h s*
        (cos (z*(s:ℂ))*v.1+sin (z*(s:ℂ))/z*v.2) := by
  let u := classicalHillPotentialVariation 0 h (z^2) v
  let g : ℝ → ℂ := fun s => (extend (classicalHillPotentialVariationSource 0 h (z^2) v) s).2
  have huc : Continuous u := (contDiff_classicalHillPotentialVariation 0 h (z^2) v).continuous
  have hgc : Continuous g := (continuous_extend _).snd
  have hg (s : Icc (0:ℝ) 1) : g s = h s*(classicalHillFlow 0 (z^2) v s).1 := by
    dsimp only [g]
    rw [extend_coe,classicalHillPotentialVariationSource_apply]
  have hdu (s : Icc (0:ℝ) 1) : HasDerivAt u ((u s).2,-z^2*(u s).1+g s) s := by
    rw [hg]
    simpa only [u,ContinuousMap.zero_apply,zero_sub] using
      hasDerivAt_classicalHillPotentialVariation 0 h (z^2) v s
  have hF (s : ℝ) (hs : s ∈ Ioo 0 t.val) : HasDerivAt (fun x => (u x).1) (u s).2 s := by
    simpa using! HasFDerivAt.hasDerivAt (hdu ⟨s,⟨hs.1.le,hs.2.le.trans t.property.2⟩⟩).fst
  have hG (s : ℝ) (hs : s ∈ Ioo 0 t.val) :
      HasDerivAt (fun x => (u x).2) (-z^2*(u s).1+g s) s := by
    simpa using! HasFDerivAt.hasDerivAt (hdu ⟨s,⟨hs.1.le,hs.2.le.trans t.property.2⟩⟩).snd
  have hzero : u 0 = 0 := classicalHillPotentialVariation_zero _ _ _ _
  have hD := secondOrder_duhamel (fun x => (u x).1) (fun x => (u x).2) g z hz t.val t.property.1
    huc.fst huc.snd hgc (congrArg Prod.fst hzero) (congrArg Prod.snd hzero) hF hG
  have hgreal (s : ℝ) (hs : s ∈ uIcc 0 t.val) :
      g s = extend h s*(cos (z*(s:ℂ))*v.1+sin (z*(s:ℂ))/z*v.2) := by
    have hsi : s ∈ Icc (0:ℝ) 1 := by
      rw [uIcc_of_le t.property.1] at hs
      exact ⟨hs.1,hs.2.trans t.property.2⟩
    have he := hg ⟨s,hsi⟩
    rw [classicalHillFlow_free_sq z hz v s hsi] at he
    rw [← extend_coe h ⟨s,hsi⟩] at he
    exact he
  constructor
  · apply hD.1.trans
    apply intervalIntegral.integral_congr
    intro s hs
    dsimp only
    rw [hgreal s hs]
    ring
  · apply hD.2.trans
    apply intervalIntegral.integral_congr
    intro s hs
    dsimp only
    rw [hgreal s hs]
    ring

theorem fderiv_classicalHillDirichlet_free (h : Curve ℂ) (z : ℂ) (hz : z ≠ 0) :
    (fderiv ℂ (fun q => classicalHillDirichlet q (z^2)) 0) h =
      ∫ s in (0:ℝ)..1, (sin (z*(1-s))/z)*extend h s*(sin (z*(s:ℂ))/z) := by
  rw [fderiv_classicalHillDirichlet_potential]
  have hD := (classicalHillPotentialVariation_free_sq h z hz (0,1) ⟨1,by constructor <;> norm_num⟩).1
  simpa only [mul_zero,mul_one,zero_add,Complex.ofReal_one] using hD

theorem fderiv_classicalHillDirichletTerminal_free (h : Curve ℂ) (z : ℂ) (hz : z ≠ 0) :
    (fderiv ℂ (fun q => classicalHillDirichletTerminal q (z^2)) 0) h =
      ∫ s in (0:ℝ)..1, cos (z*(1-s))*extend h s*(sin (z*(s:ℂ))/z) := by
  rw [fderiv_classicalHillDirichletTerminal_potential]
  have hD := (classicalHillPotentialVariation_free_sq h z hz (0,1) ⟨1,by constructor <;> norm_num⟩).2
  simpa only [mul_zero,mul_one,zero_add,Complex.ofReal_one] using hD

end NLS.KdV
