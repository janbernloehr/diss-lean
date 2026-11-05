import NLS.MKdV.MiuraGardnerGeneratorAngularDescent
import NLS.MKdV.MiuraNativeNLSAngularDomain

/-! # Global phase-product descent from actual open-domain Gardner generators

An independently specified H¹ phase need only have physical H¹ gradients
on its selected open-action domain. Its actual negative unit Gardner
generator integrates on the complete orbit. Zero extension of the phase
is used only for a bounded auxiliary; its amplitude-weighted product is
continuous, and the final factor recovers the full unit-phase product on
the exact selected open domain. No independent phase is constructed here.
-/
noncomputable section
open Set Complex NLS.Poisson NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem exists_independent_open_Gardner_phase_action_factor
    (s : ℕ) (hs : 1 ≤ s) (m : ℕ) (hm : 1 ≤ m) (F : ScalarDomain 2 → ℂ)
    (P : ∀ a : MiuraRealSobolevSource s, miuraNativeNLSAngularCoordinate s m a ≠ 0 →
      SobolevGardnerGradientAt F (hierarchySobolevToScalarDomain s hs a.val))
    (hunit : ∀ a : MiuraRealSobolevSource s, miuraNativeNLSAngularCoordinate s m a ≠ 0 →
      ‖F (hierarchySobolevToScalarDomain s hs a.val)‖ = 1)
    (hgen : ∀ (a : MiuraRealSobolevSource s) (ha : miuraNativeNLSAngularCoordinate s m a ≠ 0),
      ∀ n : ℕ, 1 ≤ n →
      reflectedHilbertPairing (scalarInclusion (P a ha).gradient)
        (l2GardnerDirection (miuraL2Action n) (hierarchySobolevJetL2 s 0 (Nat.zero_le _) a.val)) =
          -(if m = n then I else 0)*F (hierarchySobolevToScalarDomain s hs a.val)) :
    ∃ f : MiuraNativeActionMeanTarget s → ℂ, ∀ a : MiuraRealSobolevSource s,
      miuraNativeNLSAngularCoordinate s m a ≠ 0 →
      f (miuraNativeActionMeanMap s a.val) =
        miuraNativeNLSUnitPhase s m a*F (hierarchySobolevToScalarDomain s hs a.val) := by
  classical
  let U := miuraNativeNLSAngularCoordinate s m
  let H := hierarchySobolevToScalarDomain s hs
  let Q : MiuraRealSobolevSource s → ℂ := fun a => if U a ≠ 0 then F (H a.val) else 0
  have hH : Continuous (fun a : MiuraRealSobolevSource s => H a.val) := H.continuous.comp continuous_subtype_val
  have hQ : ContinuousOn Q {a | U a ≠ 0} := by
    have hc : ContinuousOn (fun a : MiuraRealSobolevSource s => F (H a.val)) {a | U a ≠ 0} := by
      intro a ha
      exact ((P a ha).hasFDerivAt.continuousAt.comp
        (f := fun b : MiuraRealSobolevSource s => H b.val) (x := a) hH.continuousAt).continuousWithinAt
    apply hc.congr
    intro a ha
    exact if_pos ha
  have hbound : ∀ a, ‖Q a‖ ≤ 1 := by
    intro a
    dsimp only [Q]
    split_ifs with ha
    · exact (hunit a ha).le
    · simp only [norm_zero,zero_le_one]
  have hflow : ∀ a : MiuraRealSobolevSource s, U a ≠ 0 → ∀ n : ℕ, 1 ≤ n → ∀ t : ℝ,
      Q (miuraNativeRealActionFlow s a n t) = Complex.exp (-(if m = n then I else 0)*(t : ℂ))*Q a := by
    intro a ha n hn t
    have hopen (r : ℝ) : U (miuraNativeRealActionFlow s a n r) ≠ 0 := by
      change miuraNativeNLSAngularCoordinate s m (miuraNativeRealActionFlow s a n r) ≠ 0
      rw [miuraNativeNLSAngularCoordinate_actionFlow s m hm a n hn r]
      exact mul_ne_zero (Complex.exp_ne_zero _) ha
    let g : ℝ → ℂ := fun r => F (H (miuraNativeRealActionFlow s a n r).val)
    have hd (r : ℝ) : HasDerivAt g (-(if m = n then I else 0)*g r) r := by
      have h := hasDerivAt_independent_functional_miuraActionFlow_allTimes s hs a n hn r F
        (P (miuraNativeRealActionFlow s a n r) (hopen r))
      rw [hgen _ (hopen r) n hn] at h
      exact h
    have hg := NLS.FunctionalAnalysis.eq_scalarExponential_of_hasDerivAt _ g hd t
    have hz : g 0 = F (H a.val) := by
      change F (H (miuraActionFlow s a.val (fun j => a.property j) n 0)) = _
      rw [miuraActionFlow_zero]
    change (if U (miuraNativeRealActionFlow s a n t) ≠ 0 then g t else 0) = _
    rw [if_pos (hopen t),hg,hz]
    dsimp only [Q]
    rw [if_pos ha]
  obtain ⟨f,hf⟩ := exists_opposite_unit_phase_action_factor s hs m hm Q hQ hbound hflow
  refine ⟨f,fun a ha => ?_⟩
  have he : Q a = F (H a.val) := if_pos ha
  simpa only [he,H] using hf a

end NLS.MKdV
