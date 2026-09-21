import NLS.ZakharovShabat.UniformSmallDeletedPairErrors
import NLS.ZakharovShabat.UniformSmallCriticalDisplacements
import NLS.ZakharovShabat.DeletedProductCriticalValues

/-! # Remaining-product critical values locally uniformly close to their free values
The disc comparison errors and the free squared-quotient displacement
bounds give uniform smallness of both G(c)-1 and G'(c). This supplies the
extra control needed beyond bounded lp norms in Lemma 8.6.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The remaining-product value tends to one and its derivative to zero locally uniformly at canonical critical points. -/
theorem exists_uniform_small_deletedProduct_critical_values (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∃ U : Set (PairSpace p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ heven : ψ ∈ pairParitySubspace 0, ∀ n : ℤ, N < n.natAbs →
        ‖canonicalDeletedCriticalValueError hp hp1 ψ heven n‖ ≤ ε ∧
        ‖canonicalDeletedCriticalDerivative hp hp1 ψ heven n‖ ≤ ε := by
  obtain ⟨C,hC,hfree⟩ := exists_freeSquaredSine_displacement_bounds (Real.pi/4)
  let δ := min (Real.pi/4) (ε/(2*(C+1)))
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδC : C*δ ≤ ε/2 := by
    have he : δ*(2*(C+1)) ≤ ε := (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    nlinarith
  let η := ε/(2*(1+4/Real.pi))
  have hη : 0 < η := by dsimp [η]; positivity
  have hηe : η*(2*(1+4/Real.pi)) = ε := div_mul_cancel₀ ε (by positivity)
  have hηv : η ≤ ε/2 := by nlinarith [show 0 ≤ 4/Real.pi by positivity]
  have hηd : (4/Real.pi)*η ≤ ε/2 := by nlinarith
  obtain ⟨N,hN,V,hvo,hvc,hvφ,hv0,hcrit⟩ := exists_uniform_small_canonicalCriticalDisplacements hp hp1 φ hδ
  obtain ⟨M,_,W,hwo,hwc,hwφ,hw0,herr⟩ := exists_uniform_small_canonicalDeletedPairErrors hp hp1 φ hη
  refine ⟨max N M,lt_of_lt_of_le hN (le_max_left _ _),V ∩ W,hvo.inter hwo,hvc.inter hwc,
    ⟨hvφ,hwφ⟩,⟨hv0,hw0⟩,fun ψ hψ heven n hn => ?_⟩
  let c := canonicalCriticalPoints hp hp1 ψ heven n
  have hdisp : ‖c-(Real.pi : ℂ)*n‖ ≤ δ := by
    simpa only [canonicalCriticalDisplacement_apply] using
      (hcrit ψ hψ.1 heven n (lt_of_le_of_lt (le_max_left _ _) hn)).le
  have hc : ‖c-(Real.pi : ℂ)*n‖ ≤ Real.pi/4 := hdisp.trans (min_le_left _ _)
  have hCf : C*‖c-(Real.pi : ℂ)*n‖ ≤ ε/2 := (mul_le_mul_of_nonneg_left hdisp hC).trans hδC
  have hf := hfree n c hc
  obtain ⟨hv,hd⟩ := herr ψ hψ.2 heven n (lt_of_le_of_lt (le_max_right _ _) hn)
  have hv' := (hv c (by linarith [Real.pi_pos])).trans hηv
  have hd' := (hd c hc).trans hηd
  constructor
  · have he : canonicalDeletedCriticalValueError hp hp1 ψ heven n =
        canonicalDeletedPairError hp hp1 ψ heven n c+((freeSineQuotient n c)^2-1) := by
      dsimp [canonicalDeletedCriticalValueError,canonicalDeletedPairError,c]
      ring
    rw [he]
    exact (norm_add_le _ _).trans (by linarith [hf.1.trans hCf])
  · have he : canonicalDeletedCriticalDerivative hp hp1 ψ heven n =
        deriv (canonicalDeletedPairError hp hp1 ψ heven n) c+
          deriv (fun z => (freeSineQuotient n z)^2) c := by
      rw [deriv_canonicalDeletedPairError]
      dsimp [canonicalDeletedCriticalDerivative,c]
      ring
    rw [he]
    exact (norm_add_le _ _).trans (by linarith [hf.2.trans hCf])

end NLS.ZakharovShabat
