import NLS.ComplexAnalysis.QuarticInversionContour
import NLS.ZakharovShabat.SourceFullAbelianHamiltonianInversion

/-! # The physical H₄ contour coefficient

The quartic full primitive recovers the independently defined physical
Hamiltonian combination H₄ − 6H₁H₂. Its normalization is 2i/π times
the exterior contour, as required before differentiating Lemma 5.2.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

/-- The actual quartic phase has exactly the physical simple-pole period,
for every normalization index and every sufficiently large circle. -/
theorem exists_sourceFullAbelian_finiteGap_fourth_contour
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (φ : realTypeSourceSubmodule p)
    (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ T : ℝ, 0 < T ∧ ∀ R : ℝ, T ≤ R → ∀ n : ℤ,
      (∮ z in C(0,R), (sourceFullAbelianPrimitive hp hp1 W n (z,φ.val)-I*(Real.pi:ℂ)*n)^4) =
        -(Real.pi*I/2:ℂ)*(sourceFiniteGapNLSHamiltonian hp hp1 φ hf 4-
          6*sourceFiniteGapNLSHamiltonian hp hp1 φ hf 1*sourceFiniteGapNLSHamiltonian hp hp1 φ hf 2) := by
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
  have h₄ : iteratedDeriv 4 A 0 = 3*I*sourceFiniteGapNLSHamiltonian hp hp1 φ hf 4/2 := by
    have h := hder 3
    norm_num [Nat.factorial] at h
    convert h using 1
    ring
  obtain ⟨T,hT,hcontour⟩ := exists_phase_fourth_contour A hA hA0 _ _ _ _ h₁ h₂ h₃ h₄
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

/-- The physical quartic Hamiltonian contour identity, before any frequency
or action-derivative identification. -/
theorem exists_sourceFullAbelian_finiteGap_hamiltonian_fourth_contour
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (φ : realTypeSourceSubmodule p)
    (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ T : ℝ, 0 < T ∧ ∀ R : ℝ, T ≤ R →
      sourceFiniteGapNLSHamiltonian hp hp1 φ hf 4-
        6*sourceFiniteGapNLSHamiltonian hp hp1 φ hf 1*sourceFiniteGapNLSHamiltonian hp hp1 φ hf 2 =
      (2*I/Real.pi:ℂ)*(∮ z in C(0,R), (sourceFullAbelianPrimitive hp hp1 W 0 (z,φ.val))^4) := by
  obtain ⟨T,hT,hc⟩ := exists_sourceFullAbelian_finiteGap_fourth_contour C φ hφ hf
  refine ⟨T,hT,?_⟩
  intro R hR
  have h := hc R hR 0
  simp only [Int.cast_zero,mul_zero,sub_zero] at h
  rw [h]
  have hπ : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  ring_nf
  simp only [I_sq]
  ring

/-- Any actual spectral chart admits the same physical quartic contour.
The primitive's ambient neighborhood imposes no compatibility premise. -/
theorem exists_sourceFullAbelian_hamiltonian_fourth_contour_of_chart
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1)
    (D : SourceAbelianSpectralChart hp hp1 W φ.val) :
    ∃ T : ℝ, 0 < T ∧ ∀ R : ℝ, T ≤ R →
      sourceFiniteGapNLSHamiltonian hp hp1 φ hf 4-
        6*sourceFiniteGapNLSHamiltonian hp hp1 φ hf 1*sourceFiniteGapNLSHamiltonian hp hp1 φ hf 2 =
      (2*I/Real.pi:ℂ)*(∮ z in C(0,R), (sourceFullAbelianPrimitive hp hp1 W 0 (z,φ.val))^4) := by
  obtain ⟨V,_,_,hfamilies⟩ := exists_sourceFullAbelianUniformCauchyFamilies hp hp1
  obtain ⟨C,hC⟩ := hfamilies φ
  have hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius := by
    rw [hC]
    exact mem_ball_self C.discs.sourceRadius_pos
  obtain ⟨E⟩ := C.charts φ.val hφ
  obtain ⟨T,hT,hcontour⟩ := exists_sourceFullAbelian_finiteGap_hamiltonian_fourth_contour C φ hφ hf
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
