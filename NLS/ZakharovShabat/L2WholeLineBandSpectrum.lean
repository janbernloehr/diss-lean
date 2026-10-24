import NLS.FunctionalAnalysis.CutoffMassEstimates
import NLS.ZakharovShabat.L2WholeLineCutoffResidual
import NLS.ZakharovShabat.L2WholeLineWeylGrowth
import Mathlib.Topology.Instances.Real.Lemmas

/-! # Floquet bands belong to the actual whole-line spectrum

Expanding smooth cutoffs have linearly growing physical mass and uniformly
bounded original pencil residual. The bounded-inverse definition of the
spectrum therefore includes every unit-multiplier Floquet parameter.
-/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Complex Matrix
open NLS.FunctionalAnalysis
namespace NLS.ZakharovShabat

/-- Periodicity and continuity give a uniform upper bound for the actual
Hermitian mass density. -/
theorem bounded_wholeLineSolutionMass (u : IntervalPairL2) (z μ : ℂ)
    (hμ : ‖μ‖ = 1) (v : Fin 2 → ℂ) (hv : l2Monodromy u z *ᵥ v = μ • v) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t, wholeLineSolutionMass u z v t ≤ B := by
  obtain ⟨B,hB,hbound⟩ := ((periodic_wholeLineSolutionMass u z μ hμ v hv).isBounded_of_continuous
    one_ne_zero (continuous_wholeLineSolutionMass u z v)).exists_pos_norm_le
  refine ⟨B,hB.le,fun t => ?_⟩
  exact (le_abs_self _).trans (hbound _ ⟨t,rfl⟩)

/-- A nonzero unit-multiplier Floquet solution forces membership in the
independently defined spectrum of the original physical operator. -/
theorem mem_wholeLineSpectrum_of_unit_floquet (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (z μ : ℂ)
    (hμ : ‖μ‖ = 1) (v : Fin 2 → ℂ) (hv0 : v ≠ 0)
    (hv : l2Monodromy u z *ᵥ v = μ • v) : z ∈ wholeLineSpectrum u := by
  let m := ∫ t in (0 : ℝ)..1, wholeLineSolutionMass u z v t
  have hm : 0 < m := wholeLineSolution_unit_mass_pos u z v hv0
  obtain ⟨B,hB0,hB⟩ := bounded_wholeLineSolutionMass u z μ hμ v hv
  apply mem_wholeLineSpectrum_of_mass_growth u z m
    (B * ∫ t : ℝ, ‖deriv unitSmoothCutoff t‖ ^ 2) hm
  intro n
  let R : ℝ := (n+1 : ℕ)
  have hR : 1 ≤ R := by dsimp [R]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  let ψ := scaledCutoff unitSmoothCutoff R
  have hψ : ContDiff ℝ 1 ψ := contDiff_scaledCutoff _ contDiff_unitSmoothCutoff R
  have hc : HasCompactSupport ψ := hasCompactSupport_scaledCutoff _ hasCompactSupport_unitSmoothCutoff R hRp.ne'
  refine ⟨⟨wholeLineCutoff u z v ψ hψ.continuous hc,
    wholeLineCutoff_mem_closure_domain u hu z v ψ hψ hc⟩,?_,?_⟩
  · change (n : ℝ) * m ≤ ‖wholeLineCutoff u z v ψ hψ.continuous hc‖ ^ 2
    rw [norm_wholeLineCutoff_sq]
    calc
      (n : ℝ) * m ≤ R * m := mul_le_mul_of_nonneg_right (by dsimp [R]; push_cast; linarith) hm.le
      _ = ∫ t in (0 : ℝ)..R, wholeLineSolutionMass u z v t :=
        (wholeLineSolution_mass_nat_periods u z μ hμ v hv (n+1)).symm
      _ ≤ _ := interval_mass_le_cutoff_mass ψ hψ.continuous hc _
        (continuous_wholeLineSolutionMass u z v) (fun t => sq_nonneg _) R hRp.le
        (fun _ ht => scaled_unitSmoothCutoff_eq_one R hRp ht)
  · rw [norm_wholeLinePencil_cutoff_sq u hu z v ψ hψ hc]
    exact scaled_derivative_cutoff_mass_le unitSmoothCutoff contDiff_unitSmoothCutoff
      hasCompactSupport_unitSmoothCutoff _ (continuous_wholeLineSolutionMass u z v)
      B hB0 hB R hR

/-- Every point of the full closed Floquet band set of the unchanged
original real source lies in the actual whole-line operator spectrum.
This includes all gap endpoints and collapsed gaps. -/
theorem source_band_mem_wholeLineSpectrum (φ : CoeffPair 2)
    (hφ : IsRealType (CoeffPair.toMax 2 φ)) (x : ℝ)
    (hx : x ∈ sourceFloquetBandSet (by simp) (by norm_num) φ) :
    (x : ℂ) ∈ wholeLineSpectrum (sourcePhysicalL2 φ) := by
  obtain ⟨μ,hμ,v,hv0,hv⟩ := (source_l2_unit_monodromy_eigenvector_iff_mem_band φ hφ x).mpr hx
  exact mem_wholeLineSpectrum_of_unit_floquet _ ((sourcePhysicalL2_realType_iff φ).mpr hφ)
    x μ hμ v hv0 hv

/-- Set form of physical Floquet band spectral inclusion. -/
theorem sourceFloquetBandSet_subset_wholeLineSpectrum (φ : CoeffPair 2)
    (hφ : IsRealType (CoeffPair.toMax 2 φ)) :
    Complex.ofReal '' sourceFloquetBandSet (by simp) (by norm_num) φ ⊆
      wholeLineSpectrum (sourcePhysicalL2 φ) := by
  rintro _ ⟨x,hx,rfl⟩
  exact source_band_mem_wholeLineSpectrum φ hφ x hx

end NLS.ZakharovShabat
