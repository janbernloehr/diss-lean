import NLS.ComplexAnalysis.CubicInversionRemainder
import NLS.ZakharovShabat.SourceFullAbelianHamiltonianInversion

/-! # Corollary 19.3: the cubic expansion of the actual primitive

The inverse-frequency term is `-(3*i/8)*(H_3 - 2*H_1^2)/z`.
An explicit uniform quadratic bound supplies the printed big-O remainder
in every complex direction. Subtracting the prescribed index constant
gives the same estimate for every normalization index.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

/-- Corollary 19.3 with exterior analyticity and a uniform quantitative
remainder. The bound also holds for every normalized primitive index. -/
theorem exists_sourceFullAbelian_finiteGap_cube_asymptotics
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (φ : realTypeSourceSubmodule p)
    (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ R : ℝ, 0 < R ∧ ∃ K : ℝ, 0 < K ∧
      (∀ n : ℤ, AnalyticOnNhd ℂ
        (fun z => (sourceFullAbelianPrimitive hp hp1 W n (z,φ.val)-I*(Real.pi : ℂ)*n)^3)
        {z : ℂ | R < ‖z‖}) ∧
      ∀ (n : ℤ) (z : ℂ), R < ‖z‖ →
        ‖(sourceFullAbelianPrimitive hp hp1 W n (z,φ.val)-I*(Real.pi : ℂ)*n)^3-
          phaseCubeLaurentPart (sourceFiniteGapNLSHamiltonian hp hp1 φ hf 1)
            (sourceFiniteGapNLSHamiltonian hp hp1 φ hf 2)
            (sourceFiniteGapNLSHamiltonian hp hp1 φ hf 3) z‖ ≤ K/‖z‖^2 := by
  obtain ⟨R,hR,A,hA,hA0,hder,hval⟩ :=
    exists_sourceFullAbelian_finiteGap_hamiltonian_inversion C φ hφ hf
  have h₁ : iteratedDeriv 1 A 0 = I*sourceFiniteGapNLSHamiltonian hp hp1 φ hf 1/2 := by
    simpa using hder 0
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
  obtain ⟨S,hS,K,hK,hbound⟩ := exists_phase_cube_error_bound A hA hA0 _ _ _ h₁ h₂ h₃
  obtain ⟨T,_,hTan,_⟩ := exists_sourceFullAbelian_finiteGap_hamiltonian_laurent C φ hφ hf
  let U := max (max R S) T
  have hRU : R ≤ U := (le_max_left R S).trans (le_max_left _ _)
  have hSU : S ≤ U := (le_max_right R S).trans (le_max_left _ _)
  have hTU : T ≤ U := le_max_right _ _
  refine ⟨U,hR.trans_le hRU,K,hK,?_,?_⟩
  · intro n z hz
    exact ((hTan n z (hTU.trans_lt hz)).sub analyticAt_const).pow 3
  · intro n z hz
    have he : sourceFullAbelianPrimitive hp hp1 W n (z,φ.val)-I*(Real.pi : ℂ)*n = -I*z+A z⁻¹ := by
      rw [hval n z (hRU.trans_lt hz)]
      ring
    rw [he]
    exact hbound z (hSU.trans_lt hz)

/-- The literal big-O formulation of the printed cubic expansion. -/
theorem sourceFullAbelian_finiteGap_cube_isBigO
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (φ : realTypeSourceSubmodule p)
    (hφ : φ.val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    (fun z : ℂ => (sourceFullAbelianPrimitive hp hp1 W 0 (z,φ.val))^3-
      phaseCubeLaurentPart (sourceFiniteGapNLSHamiltonian hp hp1 φ hf 1)
        (sourceFiniteGapNLSHamiltonian hp hp1 φ hf 2)
        (sourceFiniteGapNLSHamiltonian hp hp1 φ hf 3) z)
      =O[Bornology.cobounded ℂ] (fun z : ℂ => z⁻¹^2) := by
  obtain ⟨R,_,K,_,_,hb⟩ := exists_sourceFullAbelian_finiteGap_cube_asymptotics C φ hφ hf
  apply Asymptotics.IsBigO.of_bound K
  filter_upwards [tendsto_norm_cobounded_atTop.eventually (eventually_gt_atTop R)] with z hz
  simpa only [Int.cast_zero,mul_zero,sub_zero,norm_pow,norm_inv,div_eq_mul_inv,inv_pow] using hb 0 z hz

/-- A common almost-real neighborhood supports Corollary 19.3 at every
real finite-gap source, without any additional realization hypothesis. -/
theorem exists_sourceFullAbelian_finiteGap_cube_neighborhood (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      ∀ (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1),
        ∃ R : ℝ, 0 < R ∧ ∃ K : ℝ, 0 < K ∧
          AnalyticOnNhd ℂ (fun z => (sourceFullAbelianPrimitive hp hp1 W 0 (z,φ.val))^3)
            {z : ℂ | R < ‖z‖} ∧
          ∀ z : ℂ, R < ‖z‖ →
            ‖(sourceFullAbelianPrimitive hp hp1 W 0 (z,φ.val))^3-
              phaseCubeLaurentPart (sourceFiniteGapNLSHamiltonian hp hp1 φ hf 1)
                (sourceFiniteGapNLSHamiltonian hp hp1 φ hf 2)
                (sourceFiniteGapNLSHamiltonian hp hp1 φ hf 3) z‖ ≤ K/‖z‖^2 := by
  obtain ⟨W,hW,hreal,hfamilies⟩ := exists_sourceFullAbelianUniformCauchyFamilies hp hp1
  refine ⟨W,hW,hreal,?_⟩
  intro φ hf
  obtain ⟨C,hC⟩ := hfamilies φ
  obtain ⟨R,hR,K,hK,ha,hb⟩ := exists_sourceFullAbelian_finiteGap_cube_asymptotics C φ
    (by rw [hC]; exact mem_ball_self C.discs.sourceRadius_pos) hf
  refine ⟨R,hR,K,hK,?_,?_⟩
  · simpa only [Int.cast_zero,mul_zero,sub_zero] using ha 0
  · intro z hz
    simpa only [Int.cast_zero,mul_zero,sub_zero] using hb 0 z hz

end NLS.ZakharovShabat
