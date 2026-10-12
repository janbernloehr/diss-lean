import NLS.ZakharovShabat.L2PotentialVariation
import NLS.ZakharovShabat.L2SolutionDifferentialEquation

/-! # The linearized physical L2 differential equation

The integral variation has an actual derivative almost everywhere.
Both the base coefficient and perturbation may be arbitrary physical
L2 classes, or any of their square-integrable representatives.
-/
noncomputable section
open Set Complex MeasureTheory Filter Topology
open NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- Differentiating the two actual integrals gives the linearized equation a.e. -/
theorem ae_hasDerivAt_l2VariationCurve (q d : ℂ × IntervalPairL2) (v : ℂ × ℂ) :
    ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) 1),
      HasDerivAt (extend (l2VariationCurve q d v))
        (classicalODECoefficient (intervalL2Representative d.2 s) d.1
          (extend (l2SolutionCurve q.2 q.1 v) s)+
         classicalODECoefficient (intervalL2Representative q.2 s) q.1
          (extend (l2VariationCurve q d v) s)) s := by
  have hi := (intervalIntegrable_l2ODECoefficient d.2 d.1 (l2SolutionCurve q.2 q.1 v)
    ⟨1,by constructor <;> norm_num⟩).ae_hasDerivAt_integral
  have hj := (intervalIntegrable_l2ODECoefficient q.2 q.1 (l2VariationCurve q d v)
    ⟨1,by constructor <;> norm_num⟩).ae_hasDerivAt_integral
  rw [ae_restrict_iff' measurableSet_Ioc]
  have hn : ∀ᵐ s : ℝ ∂volume, s ≠ 1 := by simp [ae_iff]
  filter_upwards [hi,hj,hn] with s hs ht hn hmem
  have hs' : s ∈ Ioo (0 : ℝ) 1 := ⟨hmem.1,lt_of_le_of_ne hmem.2 hn⟩
  have hsc : s ∈ uIcc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using Ioc_subset_Icc_self hmem
  have hd := (hs hsc 0 (by simp)).add (ht hsc 0 (by simp))
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hs'.1 hs'.2] with x hx
  have hx' : x ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hx
  have he := l2VariationCurve_eq_integral q d v ⟨x,hx'⟩
  simpa only [l2ODEIntegral,NLS.LinearVolterra.extend,projIcc_of_mem _ hx',Pi.add_apply] using he

/-- In a pure potential direction the two off-diagonal forcing signs are explicit. -/
theorem ae_hasDerivAt_l2PotentialVariation (u h : IntervalPairL2) (z : ℂ) (v : ℂ × ℂ) :
    ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) 1),
      HasDerivAt (extend (l2VariationCurve (z,u) (0,h) v))
        ((I*h.ofLp.1 s*(extend (l2SolutionCurve u z v) s).2,
          -I*h.ofLp.2 s*(extend (l2SolutionCurve u z v) s).1)+
         classicalODECoefficient (intervalL2Representative u s) z
          (extend (l2VariationCurve (z,u) (0,h) v) s)) s := by
  simpa only [classicalODECoefficient_apply,intervalL2Representative,mul_zero,zero_mul,
    zero_add,add_zero] using ae_hasDerivAt_l2VariationCurve (z,u) (0,h) v

/-- Original square-integrable functions give the same variation equation. -/
theorem l2VariationCurve_eq_integral_ofFunction (φ ψ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1)))
    (hψ : MemLp ψ 2 (volume.restrict (Ioc 0 1))) (z dz : ℂ) (v : ℂ × ℂ)
    (t : Icc (0 : ℝ) 1) :
    let q := (z,intervalL2OfFunction φ hφ)
    let d := (dz,intervalL2OfFunction ψ hψ)
    l2VariationCurve q d v t =
      (∫ s in (0 : ℝ)..t.val, classicalODECoefficient (ψ s) dz
        (extend (l2SolutionCurve q.2 z v) s))+
      (∫ s in (0 : ℝ)..t.val, classicalODECoefficient (φ s) z
        (extend (l2VariationCurve q d v) s)) := by
  dsimp only
  rw [l2VariationCurve_eq_integral,l2ODEIntegral_ofFunction,l2ODEIntegral_ofFunction]

/-- The a.e. derivative also uses arbitrary original representatives. -/
theorem ae_hasDerivAt_l2VariationCurve_ofFunction (φ ψ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1)))
    (hψ : MemLp ψ 2 (volume.restrict (Ioc 0 1))) (z dz : ℂ) (v : ℂ × ℂ) :
    let q := (z,intervalL2OfFunction φ hφ)
    let d := (dz,intervalL2OfFunction ψ hψ)
    ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) 1),
      HasDerivAt (extend (l2VariationCurve q d v))
        (classicalODECoefficient (ψ s) dz (extend (l2SolutionCurve q.2 z v) s)+
         classicalODECoefficient (φ s) z (extend (l2VariationCurve q d v) s)) s := by
  dsimp only
  filter_upwards [ae_hasDerivAt_l2VariationCurve
    (z,intervalL2OfFunction φ hφ) (dz,intervalL2OfFunction ψ hψ) v,
    intervalL2Representative_ofFunction φ hφ,intervalL2Representative_ofFunction ψ hψ] with s hs hφs hψs
  simpa only [hφs,hψs] using hs

end NLS.ZakharovShabat
