import NLS.ZakharovShabat.ClassicalSeparatedGradient
import NLS.ZakharovShabat.ClassicalSobolevRemainderSequenceBounds
import NLS.ZakharovShabat.FreeSineDisplacementBound

/-! # Inverse-index displacement of physical H¹ boundary roots

The actual separated characteristic differs from sine by O(1/|z|).
The nonvanishing filled sine quotient on the quarter-pi discs turns this
into a uniform O(1/|n|) displacement of every enclosed boundary zero.
-/

noncomputable section
open Set Complex NLS.LinearVolterra
namespace NLS.ZakharovShabat
open BoundaryCondition

/-- The normalized separated endpoint functional is contractive. -/
theorem norm_classicalSeparatedEndpointCLM_apply_le (b : BoundaryCondition) (v : ℂ × ℂ) :
    ‖classicalSeparatedEndpointCLM b v‖ ≤ ‖v‖ := by
  have hs : ‖extensionSign b‖ = 1 := by cases b <;> norm_num [extensionSign]
  rw [classicalSeparatedEndpointCLM_apply,norm_div]
  have hd : ‖(2 : ℂ)*I‖ = 2 := by norm_num
  rw [hd]
  have hn := norm_sub_le (extensionSign b*v.2) v.1
  rw [norm_mul,hs,one_mul] at hn
  have h₁ := norm_fst_le v
  have h₂ := norm_snd_le v
  linarith

/-- The characteristic error is the original endpoint functional of the
actual solution remainder, with its sine normalization unchanged. -/
theorem classicalSeparatedCharacteristic_sub_sin_eq_remainder
    (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    classicalSeparatedCharacteristic b Φ z-sin z =
      classicalSeparatedEndpointCLM b (classicalSolutionRemainder Φ z (1,extensionSign b) 1) := by
  rw [← classicalSeparatedCharacteristic_free b z,
    classicalSeparatedCharacteristic_eq_endpoint b Φ z,
    classicalSeparatedCharacteristic_eq_endpoint b 0 z,← map_sub]
  congr 1
  rw [classicalSolution_free z (1,extensionSign b) ⟨1,by constructor <;> norm_num⟩]
  rfl

/-- The actual sine error is uniformly O(1/|z|) on physical H¹ balls and strips. -/
theorem norm_classicalSeparatedCharacteristic_sub_sin_sobolev_le
    (M H : ℝ) (a : Domain 2) (ha : ‖a‖ ≤ M) (b : BoundaryCondition)
    (z : ℂ) (hz : z ≠ 0) (him : |z.im| ≤ H) :
    ‖classicalSeparatedCharacteristic b (classicalSobolevPotential a) z-sin z‖ ≤
      classicalSobolevErrorConstant M H/‖z‖ := by
  rw [classicalSeparatedCharacteristic_sub_sin_eq_remainder]
  apply (norm_classicalSeparatedEndpointCLM_apply_le b _).trans
  have h := norm_classicalSolutionRemainder_sobolev_strip_le M H a ha z hz him
    (1,extensionSign b) ⟨1,by constructor <;> norm_num⟩
  have hv : ‖((1 : ℂ),extensionSign b)‖ = 1 := by cases b <;> simp [extensionSign]
  rw [hv] at h
  have he : (4+Real.pi)*M*1/‖z‖*Real.exp (4*M+H) =
      classicalSobolevErrorConstant M H/‖z‖ := by
    unfold classicalSobolevErrorConstant
    ring
  rw [he] at h
  exact h

/-- Every zero in a distant quarter-pi disc has inverse-index displacement,
uniformly for both ordinary boundary conditions and the whole physical H¹ ball. -/
theorem exists_classicalSeparatedRoot_sobolev_inverse_index_bound
    (M : ℝ) (hM : 0 ≤ M) :
    ∃ N : ℕ, 0 < N ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∀ (a : Domain 2), ‖a‖ ≤ M → ∀ b : BoundaryCondition, ∀ n : ℤ, N ≤ n.natAbs →
      ∀ z : ℂ, ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/4 →
        classicalSeparatedCharacteristic b (classicalSobolevPotential a) z = 0 →
        ‖z-(Real.pi : ℂ)*n‖ ≤ B/(n.natAbs : ℝ) := by
  obtain ⟨C,hC,hdisp⟩ := exists_freeDisc_sine_displacement_bound
    (r := Real.pi/4) (by nlinarith [Real.pi_pos])
  obtain ⟨N,hN,hcut⟩ := exists_near_free_frequency_cutoff (Real.pi/4) (by positivity)
  let E := classicalSobolevErrorConstant M (Real.pi/4)
  have hE : 0 ≤ E := classicalSobolevErrorConstant_nonneg _ _ hM
  refine ⟨N,hN,2*C*E/Real.pi,by positivity,?_⟩
  intro a ha b n hn z hz hzero
  obtain ⟨him,hz1,hzn⟩ := hcut n hn z hz
  have hnpos : 0 < (n.natAbs : ℝ) := by exact_mod_cast hN.trans_le hn
  have hzne : z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hz1)
  have hs := norm_classicalSeparatedCharacteristic_sub_sin_sobolev_le M (Real.pi/4) a ha b z hzne him
  rw [hzero,zero_sub,norm_neg] at hs
  calc
    ‖z-(Real.pi : ℂ)*n‖ ≤ C*‖sin z‖ := hdisp n z hz
    _ ≤ C*(E/‖z‖) := mul_le_mul_of_nonneg_left hs hC
    _ ≤ C*(E/(Real.pi*(n.natAbs : ℝ)/2)) := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_left hE (by positivity) hzn) hC
    _ = (2*C*E/Real.pi)/(n.natAbs : ℝ) := by ring

end NLS.ZakharovShabat
