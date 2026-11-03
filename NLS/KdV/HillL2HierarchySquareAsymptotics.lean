import NLS.KdV.HillHierarchyPhaseModel
import NLS.KdV.HillHierarchyReality
import NLS.KdV.HillL2SquareCircleAsymptotics

/-! # The actual all-order squared Hill primitive error on upper arcs and full circles. -/

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ContDiff ComplexConjugate
namespace NLS.KdV
open NLS.ComplexAnalysis
theorem exists_hillSquaredPhaseModel_upper_arc_error
    (Q : C(AddCircle (2 : ℝ), ℂ))
    (hq : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2 : ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) 1)
    (hmean : (∫ x in (0 : ℝ)..1, Q (x : AddCircle (2 : ℝ))) = 0) (M : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, ∀ n : ℕ, K ≤ n → ∀ t : Icc (0 : ℝ) Real.pi,
      (hillFreeBandFrequency n)^(2*M)*
        ‖hillL2RealCutPrimitive (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q))
            (hillFreeUpperFrequency n t ^ 2)^2 -
          hillSourceSquaredPhaseModel
            (classicalKdVHierarchyHamiltonian (fun x : ℝ => Q (x : AddCircle (2 : ℝ))))
            M (hillFreeUpperFrequency n t ^ 2)‖ ≤ C := by
  let f : ℝ → ℂ := fun x => Q (x : AddCircle (2 : ℝ))
  let H := classicalKdVHierarchyHamiltonian f
  let B := 1+∑ i ∈ Finset.range M, ‖H i/4^(i+1)‖
  have hB : 0 < B := by dsimp [B]; positivity
  obtain ⟨D,hD,K,herror⟩ := exists_hillL2RealCutPrimitive_upper_arc_source_hamiltonian_error_bound
    Q hq hr hf hp M
  obtain ⟨K0,hK0⟩ := eventually_atTop.mp (tendsto_hillFreeBandFrequency.eventually_ge_atTop 1)
  refine ⟨D*(2*B+D),by positivity,max K K0,?_⟩
  intro n hn t
  let z := hillFreeUpperFrequency n t
  let F := hillL2RealCutPrimitive (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) (z^2)
  have hzn : ‖z‖ = hillFreeBandFrequency n := norm_hillFreeUpperFrequency n t
  have hzone : 1 ≤ ‖z‖ := by rw [hzn]; exact hK0 n (le_trans (le_max_right _ _) hn)
  have he := herror n (le_trans (le_max_left _ _) hn) t
  rw [hillHamiltonianPhase_mean_zero _ hmean] at he
  have hden : (hillFreeBandFrequency n)^(2*M+1) ≤ (2*hillFreeBandFrequency n)^(2*M+1) :=
    pow_le_pow_left₀ (hillFreeBandFrequency_pos n).le (by nlinarith [hillFreeBandFrequency_pos n]) _
  have herr : ‖F-hillFiniteSourcePhase H M z‖ ≤ D/(hillFreeBandFrequency n)^(2*M+1) :=
    he.trans (div_le_div_of_nonneg_left hD.le (pow_pos (hillFreeBandFrequency_pos n) _) hden)
  have hw : ‖z‖^(2*M+1)*‖F-hillFiniteSourcePhase H M z‖ ≤ D := by
    rw [hzn]
    have h := (le_div_iff₀ (pow_pos (hillFreeBandFrequency_pos n) (2*M+1))).mp herr
    simpa only [mul_comm] using h
  have h := norm_hillSquaredPhaseModel_error H M z F D hzone hD.le hw
  rw [hzn] at h
  exact h


theorem exists_hillSquaredPhaseModel_circle_error
    (Q : C(AddCircle (2 : ℝ), ℂ))
    (hq : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)))
    (hreal : ∀ x : AddCircle (2 : ℝ), (Q x).im = 0)
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2 : ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2 : ℝ))) 1)
    (hmean : (∫ x in (0 : ℝ)..1, Q (x : AddCircle (2 : ℝ))) = 0) (M : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, ∀ n : ℕ, K ≤ n →
      ∀ w ∈ sphere (0 : ℂ) ((hillFreeBandFrequency n)^2),
        (hillFreeBandFrequency n)^(2*M)*
          ‖hillL2RealCutPrimitive (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) w^2-
            hillSourceSquaredPhaseModel
              (classicalKdVHierarchyHamiltonian (fun x : ℝ => Q (x : AddCircle (2 : ℝ)))) M w‖ ≤ C := by
  let q := hillContinuousCoefficients Q
  let H := classicalKdVHierarchyHamiltonian (fun x : ℝ => Q (x : AddCircle (2 : ℝ)))
  let F : ℂ → ℂ := fun w => hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) w^2-
    hillSourceSquaredPhaseModel H M w
  have hH (m : ℕ) : conj (H m) = H m :=
    conj_classicalKdVHierarchyHamiltonian_of_real _ hf (fun x => hreal (x : AddCircle (2 : ℝ))) m
  obtain ⟨C,hC,K,hupper⟩ := exists_hillSquaredPhaseModel_upper_arc_error Q hq hr hf hp hmean M
  refine ⟨C,hC,K,?_⟩
  intro n hn
  apply weighted_norm_bound_on_circle_of_upper_reflection F _ _ C
  · intro w hw hi
    have hnorm : ‖w‖ = (hillFreeBandFrequency n)^2 := by
      simpa only [mem_sphere_iff_norm, sub_zero] using hw
    obtain ⟨t,ht⟩ := exists_upper_circleMap_parameter w _ hnorm hi
    have he : hillFreeUpperFrequency n t^2 = w := (hillFreeUpperFrequency_sq n t).trans ht
    have h := hupper n hn t
    rw [he] at h
    exact h
  · intro w hw
    dsimp only [F]
    rw [hillL2RealCutPrimitive_sq_conj q hq hr w hw, hillSourceSquaredPhaseModel_conj H hH M w]
    simp only [map_sub]


end NLS.KdV
