import NLS.ZakharovShabat.L2VolterraEquation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-! # The original spectral equation almost everywhere for physical L2 potentials

The integral equation gives actual derivatives almost everywhere by Lebesgue
differentiation. No pointwise smoothness of the potential is required.
-/
noncomputable section
open Set Complex MeasureTheory Filter Topology
open NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- The L2 solution satisfies the original signed first-order system almost everywhere. -/
theorem ae_hasDerivAt_l2SolutionCurve (u : IntervalPairL2) (z : ℂ) (v : ℂ × ℂ) :
    ∀ᵐ s ∂volume.restrict (Ioc (0:ℝ) 1),
      HasDerivAt (extend (l2SolutionCurve u z v))
        (classicalODECoefficient (intervalL2Representative u s) z (extend (l2SolutionCurve u z v) s)) s := by
  have hi := (intervalIntegrable_l2ODECoefficient u z (l2SolutionCurve u z v)
    ⟨1,by constructor <;> norm_num⟩).ae_hasDerivAt_integral
  rw [ae_restrict_iff' measurableSet_Ioc]
  have hn : ∀ᵐ s : ℝ ∂volume, s ≠ 1 := by simp [ae_iff]
  filter_upwards [hi,hn] with s hs hn hmem
  have hs' : s ∈ Ioo (0:ℝ) 1 := ⟨hmem.1,lt_of_le_of_ne hmem.2 hn⟩
  have hd := (hs (by simpa only [uIcc_of_le (show (0:ℝ) ≤ 1 by norm_num)] using Ioc_subset_Icc_self hmem)
    0 (by simp)).const_add v
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hs'.1 hs'.2] with x hx
  have hx' : x ∈ Icc (0:ℝ) 1 := Ioo_subset_Icc_self hx
  have he := l2SolutionCurve_eq_integral u z v ⟨x,hx'⟩
  simpa only [NLS.LinearVolterra.extend,projIcc_of_mem _ hx'] using he

/-- The actual physical Zakharov-Shabat expression equals z times the L2 solution almost everywhere. -/
theorem ae_physicalOperator_l2SolutionCurve (u : IntervalPairL2) (z : ℂ) (v : ℂ × ℂ) :
    physicalOperator (intervalL2Representative u) (extend (l2SolutionCurve u z v))
      =ᵐ[volume.restrict (Ioc (0:ℝ) 1)] (fun s => z • extend (l2SolutionCurve u z v) s) := by
  filter_upwards [ae_hasDerivAt_l2SolutionCurve u z v] with s hs
  simp only [physicalOperator,(HasFDerivAt.hasDerivAt hs.fst).deriv,
    (HasFDerivAt.hasDerivAt hs.snd).deriv,classicalODECoefficient_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.toSpanSingleton_apply,one_smul]
  apply Prod.ext <;> dsimp <;> ring_nf <;> simp [I_sq]

/-- The spectral equation uses any original square-integrable representative. -/
theorem ae_physicalOperator_l2SolutionCurve_ofFunction (φ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) (z : ℂ) (v : ℂ × ℂ) :
    physicalOperator φ (extend (l2SolutionCurve (intervalL2OfFunction φ hφ) z v))
      =ᵐ[volume.restrict (Ioc (0:ℝ) 1)]
        (fun s => z • extend (l2SolutionCurve (intervalL2OfFunction φ hφ) z v) s) := by
  filter_upwards [ae_physicalOperator_l2SolutionCurve (intervalL2OfFunction φ hφ) z v,
    intervalL2Representative_ofFunction φ hφ] with s hs hφs
  simpa only [physicalOperator,hφs] using hs

end NLS.ZakharovShabat
