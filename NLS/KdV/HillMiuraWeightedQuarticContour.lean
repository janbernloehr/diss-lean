import NLS.KdV.HillMiuraFiniteGapHamiltonianSymmetry
import NLS.ZakharovShabat.SourceFullAbelianHamiltonianInversion
import NLS.ComplexAnalysis.WeightedQuarticInversionContour

/-! The actual finite-gap scalar Miura primitive has an exact weighted
quartic contour. Its coefficient is the genuine centered KdV hierarchy
combination, with no supplied Laurent expansion or model primitive. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat NLS.ComplexAnalysis
namespace NLS.KdV
variable {W : Set (CoeffPair 2)}

theorem hillMiura_finiteGap_weighted_quartic_contour
    (C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W)
    (u : PeriodOneRealL2)
    (hC : (hillMiuraRealSource u).val ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hf : hillMiuraRealSource u ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    ∃ T : ℝ, 0 < T ∧ ∀ R : ℝ, T ≤ R → ∀ n : ℤ,
      (∮ z in C(0,R), z*(sourceFullAbelianPrimitive (by simp) (by norm_num) W n
          (z,(hillMiuraRealSource u).val)-I*(Real.pi:ℂ)*n)^4)=
        (-(Real.pi:ℂ)*I/2)*
          (sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) (hillMiuraRealSource u) hf 5/2-
            3*sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) (hillMiuraRealSource u) hf 1*
              sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) (hillMiuraRealSource u) hf 3+
            2*(sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) (hillMiuraRealSource u) hf 1)^3) := by
  let H := sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) (hillMiuraRealSource u) hf
  obtain ⟨S,hS,A,hA,hA0,hder,hval⟩ := exists_sourceFullAbelian_finiteGap_hamiltonian_inversion C
    (hillMiuraRealSource u) hC hf
  have h₁ : iteratedDeriv 1 A 0=I*H 1/2 := by simpa only [Nat.zero_add,Nat.factorial_one,Nat.cast_one,one_mul,pow_one] using hder 0
  have hz : H 2=0 := by simpa only [Nat.mul_zero,Nat.zero_add] using sourceFiniteGapNLSHamiltonian_hillMiura_even u hf 0
  have h₂ : iteratedDeriv 2 A 0=0 := by
    have h := hder 1
    change iteratedDeriv 2 A 0=(2:ℂ)*(I*H 2/2^2) at h
    simpa only [hz,mul_zero,zero_div] using h
  have h₃ : iteratedDeriv 3 A 0=3*I*H 3/4 := by
    have h := hder 2
    norm_num [Nat.factorial] at h
    convert h using 1; ring
  have h₅ : iteratedDeriv 5 A 0=15*I*H 5/4 := by
    have h := hder 4
    norm_num [Nat.factorial] at h
    convert h using 1; ring
  obtain ⟨T,hT,hcontour⟩ := exists_phase_weighted_quartic_contour A hA hA0 (H 1) (H 3) (H 5) h₁ h₂ h₃ h₅
  refine ⟨max (S+1) T,hT.trans_le (le_max_right _ _),?_⟩
  intro R hR n
  have hTR : T ≤ R := (le_max_right _ _).trans hR
  have hSR : S < R := by linarith [le_max_left (S+1) T]
  rw [← hcontour R hTR]
  apply circleIntegral.integral_congr (hT.trans_le hTR).le
  intro z hz
  have hn : ‖z‖=R := by simpa only [mem_sphere,dist_zero_right] using hz
  dsimp only
  rw [hval n z (by rw [hn]; exact hSR)]
  congr 1
  ring

end NLS.KdV
