import NLS.MKdV.NativeMiuraHillGradient

/-! # All-order physical even NLS cotangents transfer to the native Hill cotangent

The original S_(2s+2) differential at a complex diagonal H^(s+1)
profile is the independent native K_(s+1) differential applied to the
spatial difference of its two variation components, with the actual
period-one multiplier and no parity factor. This precedes any angle or
frequency definition.
-/
noncomputable section
open Complex NLS.ZakharovShabat
namespace NLS.MKdV

def miuraEvenCotangentDirection (s : ℕ) : SobolevSource (s+1) →L[ℂ] ScalarSobolev s :=
  I • ((hierarchySobolevDerivative (s+1) s le_rfl).comp (ContinuousLinearMap.fst ℂ _ _) -
    (hierarchySobolevDerivative (s+1) s le_rfl).comp (ContinuousLinearMap.snd ℂ _ _))

@[simp] theorem miuraEvenCotangentDirection_apply (s : ℕ) (h : SobolevSource (s+1)) (n : ℤ) :
    (miuraEvenCotangentDirection s h).val n =
      I*(2*I*(Real.pi : ℂ)*n*h.1.val n-2*I*(Real.pi : ℂ)*n*h.2.val n) := by
  change I*((hierarchySobolevDerivative (s+1) s le_rfl h.1).val n -
    (hierarchySobolevDerivative (s+1) s le_rfl h.2).val n) = _
  rw [hierarchySobolevDerivative_apply,hierarchySobolevDerivative_apply]

theorem fderiv_even_diagonal_eq_nativeHill_cotangent (s : ℕ)
    (a : ScalarSobolev (s+1)) (h : SobolevSource (s+1)) :
    fderiv ℂ (sobolevEvenHamiltonian (s+1) (by omega)) (a,a) h =
      fderiv ℂ (nativeMiuraHillHamiltonian s)
        (hierarchySobolevInclusion (s+1) s (by omega) a) (miuraEvenCotangentDirection s h) := by
  let G := nativeMiuraHillGradient s (hierarchySobolevInclusion (s+1) s (by omega) a)
  let H := sobolevEvenHierarchyGradient (s+1) (by omega) (a,a)
  have hgrad (n : ℤ) :
      H.1.val (-n) = -(2*(Real.pi : ℂ)*n)*G.val (-n) ∧
      H.2.val (-n) = (2*(Real.pi : ℂ)*n)*G.val (-n) := by
    have he := sobolevMiuraHillFlowRestriction_coefficients (s+1) (by omega) a (-n)
    change (-I*H.2.val (-n),I*H.1.val (-n)) = _ at he
    have hg := nativeMiuraHillGradient_eq_previous s a (-n)
    change G.val (-n) = _ at hg
    rw [← hg,Int.cast_neg] at he
    constructor
    · apply mul_left_cancel₀ I_ne_zero
      calc
        I*H.1.val (-n) = 2*I*(Real.pi : ℂ)*(-n)*G.val (-n) := congrArg Prod.snd he
        _ = I*(-(2*(Real.pi : ℂ)*n)*G.val (-n)) := by ring
    · apply mul_left_cancel₀ (neg_ne_zero.mpr I_ne_zero)
      calc
        -I*H.2.val (-n) = 2*I*(Real.pi : ℂ)*(-n)*G.val (-n) := congrArg Prod.fst he
        _ = -I*((2*(Real.pi : ℂ)*n)*G.val (-n)) := by ring
  rw [← sobolevEvenHierarchyGradient_represents,
    ← nativeMiuraHillGradient_represents]
  change WeightedCoeff.sobolevBilinearPairing ((s+1 : ℕ) : ℝ) h.1 H.1 +
    WeightedCoeff.sobolevBilinearPairing ((s+1 : ℕ) : ℝ) h.2 H.2 =
      WeightedCoeff.sobolevBilinearPairing (s : ℝ) (miuraEvenCotangentDirection s h) G
  change _ = WeightedCoeff.sobolevBilinearPairing (s : ℝ)
    (I • (hierarchySobolevDerivative (s+1) s le_rfl h.1 -
      hierarchySobolevDerivative (s+1) s le_rfl h.2)) G
  rw [map_smul,map_sub]
  have hx : WeightedCoeff.sobolevBilinearPairing ((s+1 : ℕ) : ℝ) h.1 H.1 =
      I*WeightedCoeff.sobolevBilinearPairing (s : ℝ)
        (hierarchySobolevDerivative (s+1) s le_rfl h.1) G := by
    rw [WeightedCoeff.sobolevBilinearPairing_apply,WeightedCoeff.sobolevBilinearPairing_apply,
      ← tsum_mul_left]
    apply tsum_congr
    intro n
    rw [(hgrad n).1,hierarchySobolevDerivative_apply]
    linear_combination -(2*(Real.pi : ℂ)*n*h.1.val n*G.val (-n))*I_sq
  have hy : WeightedCoeff.sobolevBilinearPairing ((s+1 : ℕ) : ℝ) h.2 H.2 =
      -I*WeightedCoeff.sobolevBilinearPairing (s : ℝ)
        (hierarchySobolevDerivative (s+1) s le_rfl h.2) G := by
    rw [WeightedCoeff.sobolevBilinearPairing_apply,WeightedCoeff.sobolevBilinearPairing_apply,
      ← tsum_mul_left]
    apply tsum_congr
    intro n
    rw [(hgrad n).2,hierarchySobolevDerivative_apply]
    linear_combination (2*(Real.pi : ℂ)*n*h.2.val n*G.val (-n))*I_sq
  rw [hx,hy]
  simp only [smul_apply,sub_apply,smul_eq_mul]
  ring

end NLS.MKdV
