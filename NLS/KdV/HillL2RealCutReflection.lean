import NLS.KdV.HillFreeUpperArcs
import NLS.KdV.ClassicalHillConjugation
import NLS.KdV.HillL2DirichletCharacteristic
import NLS.KdV.HillL2RealCutDifferential

/-! # Conjugation of the actual Hill primitive, root and Dirichlet characteristic -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open scoped ContDiff ComplexConjugate Interval
namespace NLS.KdV
theorem hillL2RealCutPrimitive_conj
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (z : ℂ) (hz : z.im≠0) :
    hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) (conj z)=
      -conj (hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) z) := by
  have hc : (conj z).im≠0 := by simpa only [conj_im,neg_ne_zero] using hz
  have h := hillL2ContinuedPrimitive_conj _ hr z
    (mem_hillL2ContinuationDomain_of_im_ne_zero q hq hr z hz)
  simpa only [hillL2RealCutPrimitive,if_neg hz,if_neg hc] using h

theorem hillL2RealCutRoot_conj
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (z : ℂ) (hz : z.im≠0) :
    hillL2RealCutRoot (SpectralWeight.one.toCoeff q) (conj z)=
      -conj (hillL2RealCutRoot (SpectralWeight.one.toCoeff q) z) := by
  simp only [hillL2RealCutRoot,hillL2RealCutPrimitive_conj q hq hr z hz,
    sinh_neg,sinh_conj,map_mul,map_ofNat]
  ring

theorem hillL2DirichletCharacteristic_conj_of_continuous
    (Q : C(AddCircle (2:ℝ),ℂ)) (hreal : ∀ x, (Q x).im=0) (z : ℂ) :
    hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) (conj z)=
      conj (hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) z) := by
  rw [hillL2DirichletCharacteristic_eq_classical,hillL2DirichletCharacteristic_eq_classical]
  have h := classicalHillFlow_conj (hillUnitPotentialCurve Q)
    (fun t => hreal (t.val : AddCircle (2:ℝ))) z (0,1) ⟨1,by norm_num⟩
  simpa only [map_zero,map_one] using congrArg Prod.fst h

end NLS.KdV
