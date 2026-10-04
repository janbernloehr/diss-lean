import NLS.ComplexAnalysis.CubicInversionContour
import NLS.ZakharovShabat.SourceFullAbelianHamiltonianInversion

/-! # The first contour identity in Lemma 20.2

The actual physical Hamiltonian combination `H_3 - 2*H_1^2` equals
`8/(6*pi)` times the exterior integral of the cubed full primitive.
The equality holds on every sufficiently large circle, at every finite
exponent above one and every real finite-gap source.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

theorem exists_sourceFullAbelian_finiteGap_cube_contour
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (φ : realTypeSourceSubmodule p)
    (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ T : ℝ, 0 < T ∧ ∀ R : ℝ, T ≤ R → ∀ n : ℤ,
      (∮ z in C(0,R), (sourceFullAbelianPrimitive hp hp1 W n (z,φ.val)-I*(Real.pi : ℂ)*n)^3) =
        (3*Real.pi/4 : ℂ)*(sourceFiniteGapNLSHamiltonian hp hp1 φ hf 3-
          2*(sourceFiniteGapNLSHamiltonian hp hp1 φ hf 1)^2) := by
  obtain ⟨S,hS,A,hA,hA0,hder,hval⟩ := exists_sourceFullAbelian_finiteGap_hamiltonian_inversion C φ hφ hf
  have h₁ : iteratedDeriv 1 A 0 = I*sourceFiniteGapNLSHamiltonian hp hp1 φ hf 1/2 := by simpa using hder 0
  have h₂ : iteratedDeriv 2 A 0 = I*sourceFiniteGapNLSHamiltonian hp hp1 φ hf 2/2 := by
    have h := hder 1
    norm_num [Nat.factorial] at h
    convert h using 1
    ring
  have h₃ : iteratedDeriv 3 A 0 = 3*I*sourceFiniteGapNLSHamiltonian hp hp1 φ hf 3/4 := by
    have h := hder 2
    norm_num [Nat.factorial] at h
    convert h using 1
    ring
  obtain ⟨T,hT,hcontour⟩ := exists_phase_cube_contour A hA hA0 _ _ _ h₁ h₂ h₃
  refine ⟨max (S+1) T,hT.trans_le (le_max_right _ _),?_⟩
  intro R hR n
  have hTR : T ≤ R := (le_max_right _ _).trans hR
  have hSR : S < R := by linarith [le_max_left (S+1) T]
  rw [← hcontour R hTR]
  apply circleIntegral.integral_congr (hT.trans_le hTR).le
  intro z hz
  have hn : ‖z‖ = R := by simpa only [mem_sphere,dist_zero_right] using hz
  dsimp only
  rw [hval n z (by rw [hn]; exact hSR)]
  congr 1
  ring

/-- The Hamiltonian contour identity exactly as used at the start of
Lemma 20.2, with the physical Hamiltonians and original primitive. -/
theorem exists_sourceFullAbelian_finiteGap_hamiltonian_cube_contour
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (φ : realTypeSourceSubmodule p)
    (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ T : ℝ, 0 < T ∧ ∀ R : ℝ, T ≤ R →
      sourceFiniteGapNLSHamiltonian hp hp1 φ hf 3-2*(sourceFiniteGapNLSHamiltonian hp hp1 φ hf 1)^2 =
        (8/(6*Real.pi) : ℂ)*(∮ z in C(0,R), (sourceFullAbelianPrimitive hp hp1 W 0 (z,φ.val))^3) := by
  obtain ⟨T,hT,hc⟩ := exists_sourceFullAbelian_finiteGap_cube_contour C φ hφ hf
  refine ⟨T,hT,?_⟩
  intro R hR
  have h := hc R hR 0
  simp only [Int.cast_zero,mul_zero,sub_zero] at h
  rw [h]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp; ring

/-- No caller-supplied chart or asymptotic expansion is needed for the
finite-gap Hamiltonian contour formula. -/
theorem exists_sourceFullAbelian_hamiltonian_cube_contour_neighborhood (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      ∀ (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1),
        ∃ T : ℝ, 0 < T ∧ ∀ R : ℝ, T ≤ R →
          sourceFiniteGapNLSHamiltonian hp hp1 φ hf 3-2*(sourceFiniteGapNLSHamiltonian hp hp1 φ hf 1)^2 =
            (8/(6*Real.pi) : ℂ)*(∮ z in C(0,R), (sourceFullAbelianPrimitive hp hp1 W 0 (z,φ.val))^3) := by
  obtain ⟨W,hW,hreal,hfamilies⟩ := exists_sourceFullAbelianUniformCauchyFamilies hp hp1
  refine ⟨W,hW,hreal,?_⟩
  intro φ hf
  obtain ⟨C,hC⟩ := hfamilies φ
  exact exists_sourceFullAbelian_finiteGap_hamiltonian_cube_contour C φ
    (by rw [hC]; exact mem_ball_self C.discs.sourceRadius_pos) hf

/-- The contour formula is available in any ambient neighborhood
admitting an actual chart at the finite-gap source. This lets the
Hamiltonian and normalized moments use the same primitive. -/
theorem exists_sourceFullAbelian_hamiltonian_cube_contour_of_chart
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1)
    (D : SourceAbelianSpectralChart hp hp1 W φ.val) :
    ∃ T : ℝ, 0 < T ∧ ∀ R : ℝ, T ≤ R →
      sourceFiniteGapNLSHamiltonian hp hp1 φ hf 3-2*(sourceFiniteGapNLSHamiltonian hp hp1 φ hf 1)^2 =
        (8/(6*Real.pi) : ℂ)*(∮ z in C(0,R), (sourceFullAbelianPrimitive hp hp1 W 0 (z,φ.val))^3) := by
  obtain ⟨V,_,_,hfamilies⟩ := exists_sourceFullAbelianUniformCauchyFamilies hp hp1
  obtain ⟨C,hC⟩ := hfamilies φ
  have hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius := by
    rw [hC]
    exact mem_ball_self C.discs.sourceRadius_pos
  obtain ⟨E⟩ := C.charts φ.val hφ
  obtain ⟨T,hT,hcontour⟩ := exists_sourceFullAbelian_finiteGap_hamiltonian_cube_contour C φ hφ hf
  obtain ⟨S,_,hS⟩ := exists_exterior_subset_sourceOpenGapComplement_finiteGap hp hp1 φ hf
  refine ⟨max T (S+1),hT.trans_le (le_max_left _ _),?_⟩
  intro R hR
  rw [hcontour R ((le_max_left _ _).trans hR)]
  congr 1
  apply circleIntegral.integral_congr (hT.trans_le ((le_max_left _ _).trans hR)).le
  intro z hz
  have hn : ‖z‖ = R := by simpa only [mem_sphere,dist_zero_right] using hz
  dsimp only
  rw [sourceFullAbelianPrimitive_independent_neighborhood E D 0 z (hS (by
    change S < ‖z‖
    rw [hn]
    linarith [le_max_right T (S+1)]))]

end NLS.ZakharovShabat
