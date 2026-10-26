import NLS.ZakharovShabat.L2WholeLineGreenFormula
import NLS.ZakharovShabat.L2WholeLineGreenKernelEstimate

/-! # Uniform local bounds for the original resolvent on compact forcing -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter Complex
open scoped Matrix.Norms.Elementwise Topology
namespace NLS.ZakharovShabat

/-- The original pair norm of an L2 vector is locally integrable. -/
theorem wholeLineL2Pair_norm_intervalIntegrable (g : WholeLineL2) (a c : ℝ) :
    IntervalIntegrable (fun t => ‖wholeLineL2Pair g t‖) volume a c :=
  ((intervalIntegrable_iff').mpr
    (((memLp_wholeLineL2Pair g).locallyIntegrable (by norm_num)).integrableOn_isCompact
      isCompact_uIcc)).norm

/-- Away from repeated Floquet roots, compact-input physical resolvents have
a uniform local pair bound, independent of the nonzero imaginary part. -/
theorem eventually_wholeLineNonrealResolvent_pair_bound (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (z₀ : ℂ)
    (hdisc : (l2Monodromy u z₀).trace^2-4 ≠ 0) (a c : ℝ) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ z in 𝓝 z₀, ∀ hz : z.im ≠ 0, ∀ g : WholeLineL2,
      (∀ᵐ s : ℝ, s ≤ a → wholeLineL2Pair g s = 0) →
      (∀ᵐ s : ℝ, c ≤ s → wholeLineL2Pair g s = 0) →
      ∀ᵐ t : ℝ, t ∈ Icc a c →
        ‖wholeLineL2Pair (wholeLineNonrealResolvent u hu z hz g) t‖ ≤
          D*(∫ s in a..c, ‖wholeLineL2Pair g s‖) := by
  obtain ⟨C,hC,hK⟩ := eventually_norm_l2FloquetModeKernel_le u z₀ hdisc (Icc a c) isCompact_Icc
  refine ⟨2*C,by positivity,?_⟩
  filter_upwards [hK] with z hzK hz g hleft hright
  obtain ⟨μ,ν,hsum,hprod,_,_,hformula⟩ :=
    wholeLineNonrealResolvent_exists_green_formula u hu z hz
  have hfirst := hzK μ ν hsum hprod
  have hsecond := hzK ν μ (by rw [hsum,add_comm]) (by simpa [mul_comm] using hprod)
  filter_upwards [hformula g a c hleft hright] with t ht
  intro hti
  have h0 := norm_integral_wholeLineMatrixAction_le
    (fun s => l2FloquetModeKernel u z μ ν t s)
    (fun s => (I*(wholeLineL2Pair g s).1,-I*(wholeLineL2Pair g s).2)) a t C hti.1
    (by simpa only [norm_wholeLinePencilForcing_pair] using wholeLineL2Pair_norm_intervalIntegrable g a t)
    (fun s hs => hfirst t hti s ⟨hs.1,hs.2.trans hti.2⟩)
  have h1 := norm_integral_wholeLineMatrixAction_le
    (fun s => l2FloquetModeKernel u z ν μ t s)
    (fun s => (I*(wholeLineL2Pair g s).1,-I*(wholeLineL2Pair g s).2)) t c C hti.2
    (by simpa only [norm_wholeLinePencilForcing_pair] using wholeLineL2Pair_norm_intervalIntegrable g t c)
    (fun s hs => hsecond t hti s ⟨hti.1.trans hs.1,hs.2⟩)
  simp only [norm_wholeLinePencilForcing_pair] at h0 h1
  rw [ht]
  calc
    _ ≤ ‖∫ s in a..t, wholeLineMatrixAction (l2FloquetModeKernel u z μ ν t s)
        (I*(wholeLineL2Pair g s).1,-I*(wholeLineL2Pair g s).2)‖+
      ‖∫ s in t..c, wholeLineMatrixAction (l2FloquetModeKernel u z ν μ t s)
        (I*(wholeLineL2Pair g s).1,-I*(wholeLineL2Pair g s).2)‖ := norm_sub_le _ _
    _ ≤ (2*C)*(∫ s in a..t, ‖wholeLineL2Pair g s‖)+
      (2*C)*(∫ s in t..c, ‖wholeLineL2Pair g s‖) := add_le_add h0 h1
    _ = _ := by
      rw [← mul_add,intervalIntegral.integral_add_adjacent_intervals
        (wholeLineL2Pair_norm_intervalIntegrable g a t) (wholeLineL2Pair_norm_intervalIntegrable g t c)]

end NLS.ZakharovShabat
