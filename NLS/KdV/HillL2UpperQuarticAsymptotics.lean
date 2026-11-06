import NLS.KdV.HillL2UpperArcAsymptotics
import NLS.KdV.ClassicalHillQuarticModel

/-! # The physical energy coefficient of the actual source primitive on upper arcs -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ContDiff
namespace NLS.KdV

theorem exists_hillL2Quartic_upper_arc_energy_remainder
    (Q : C(AddCircle (2 : ℝ), ℂ))
    (hq : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2 : ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) 1)
    (hmean : (∫ x in (0 : ℝ)..1, Q (x : AddCircle (2 : ℝ))) = 0) :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, ∀ n : ℕ, K ≤ n → ∀ t : Icc (0 : ℝ) Real.pi,
      let z := hillFreeUpperFrequency n t
      (hillFreeBandFrequency n)^3 *
        ‖hillL2RealCutPrimitive (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) (z^2)^4-z^4+
          classicalQuadraticInvariant (fun x : ℝ => Q (x : AddCircle (2 : ℝ)))+
          classicalHamiltonian (fun x : ℝ => Q (x : AddCircle (2 : ℝ)))/(4*z^2)‖ ≤ C := by
  let f : ℝ → ℂ := fun x => Q (x : AddCircle (2 : ℝ))
  let H6 := classicalNLSHamiltonian (fun _ => -1) (-f) 6
  let B : ℝ := 1+‖I*classicalQuadraticInvariant f/4‖+‖I*classicalHamiltonian f/16‖
  obtain ⟨R,_hR,C,hC,hmodel⟩ := exists_classicalHill_phase_five_quartic_error_bound f hf hp hmean
  obtain ⟨D,hD,K,hsource⟩ := exists_hillL2RealCutPrimitive_upper_arc_error_bound Q hq hr hf hp 6 (by norm_num)
  obtain ⟨K1,hK1⟩ := Filter.eventually_atTop.mp
    ((tendsto_hillFreeBandFrequency.eventually_ge_atTop 1).and
      (tendsto_hillFreeBandFrequency.eventually_gt_atTop R))
  refine ⟨4*(B+(D+‖H6‖))^3*(D+‖H6‖)+C,by dsimp [B]; positivity,max K K1,?_⟩
  intro n hn t
  let z := hillFreeUpperFrequency n t
  let F := hillL2RealCutPrimitive (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) (z^2)
  let P := nlsHamiltonianPhase (fun _ => -1) (-f) 5 z
  have hnorm : ‖z‖ = hillFreeBandFrequency n := norm_hillFreeUpperFrequency n t
  have hz1 : 1 ≤ ‖z‖ := by rw [hnorm];exact (hK1 n (by omega)).1
  have hz0 : z ≠ 0 := norm_pos_iff.mp (by linarith)
  have heP : nlsHamiltonianPhase (fun _ => -1) (-f) 6 z = P+I*H6/(2*z)^6 := by
    dsimp only [P,nlsHamiltonianPhase]
    rw [show (6 : ℕ)=5+1 from rfl,Finset.sum_range_succ]
    dsimp only [H6]
    ring
  have hs : ‖F-(P+I*H6/(2*z)^6)‖ ≤ D/(2*‖z‖)^6 := by
    have hh : ‖F-nlsHamiltonianPhase (fun _ => -1) (-f) 6 z‖ ≤
        D/(2*hillFreeBandFrequency n)^6 := hsource n (by omega) t
    rw [heP,←hnorm] at hh
    exact hh
  have hscaled : ‖z‖^6*‖F-(P+I*H6/(2*z)^6)‖ ≤ D := by
    have hh := mul_le_mul_of_nonneg_left hs (pow_nonneg (norm_nonneg z) 6)
    have he : ‖z‖^6*(D/(2*‖z‖)^6)=D/64 := by field_simp;ring
    exact hh.trans (he ▸ (by linarith : D/64 ≤ D))
  have hterm : ‖z‖^6*‖I*H6/(2*z)^6‖ = ‖H6‖/64 := by
    rw [norm_div,norm_pow,norm_mul,norm_mul,norm_I,one_mul,norm_ofNat]
    field_simp
    ring
  have herr : ‖z‖^6*‖F-P‖ ≤ D+‖H6‖ := by
    have hh := mul_le_mul_of_nonneg_left
      (norm_add_le (F-(P+I*H6/(2*z)^6)) (I*H6/(2*z)^6)) (pow_nonneg (norm_nonneg z) 6)
    rw [show F-(P+I*H6/(2*z)^6)+I*H6/(2*z)^6=F-P by ring,mul_add,hterm] at hh
    linarith [norm_nonneg H6]
  have hquartic := norm_weighted_fourth_error_of_phase_error F P z (D+‖H6‖) B hz1
    (by positivity) (by dsimp [B]; positivity)
    (norm_classicalHill_phase_five_le f hf hp hmean z hz1) herr
  have hm := hmodel z (by rw [hnorm];exact (hK1 n (by omega)).2)
  have he : F^4-z^4+classicalQuadraticInvariant f+classicalHamiltonian f/(4*z^2) =
      (F^4-P^4)+(P^4-z^4+classicalQuadraticInvariant f+classicalHamiltonian f/(4*z^2)) := by ring
  dsimp only
  rw [←hnorm,he]
  have hh := mul_le_mul_of_nonneg_left
    (norm_add_le (F^4-P^4) (P^4-z^4+classicalQuadraticInvariant f+classicalHamiltonian f/(4*z^2)))
    (pow_nonneg (norm_nonneg z) 3)
  rw [mul_add] at hh
  exact hh.trans (add_le_add hquartic hm)

end NLS.KdV
