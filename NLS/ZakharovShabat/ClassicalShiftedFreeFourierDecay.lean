import NLS.Fourier.UnitIntervalC1Interpolation
import NLS.ZakharovShabat.ClassicalShiftedFreeRemainder
import NLS.ZakharovShabat.ClassicalSobolevRemainderInterpolation

/-! # Appendix G.3 comparison with the free solution at nπ

Inverse-index displacement permits the free frequency to be replaced by
the unperturbed lattice frequency. The final coefficients are the actual
Fourier integrals of the whole solution minus that reference solution.
-/

noncomputable section
open Set NLS.Fourier NLS.LinearVolterra
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Fourier coefficients of the actual solution minus the reference free solution. -/
def classicalShiftedFreeFourierCoefficients {q : ℝ≥0∞} (hq : 1 < q)
    (φ : Curve (ℂ × ℂ)) (z : ℂ) (x : ℝ) (v : ℂ × ℂ) (L : (ℂ × ℂ) →L[ℝ] ℂ) : Coeff q :=
  unitIntervalC1Coefficients hq (fun t => L (classicalShiftedFreeRemainder φ z x v t))
    (L.contDiff.comp (contDiff_classicalShiftedFreeRemainder φ z x v))

@[simp] theorem classicalShiftedFreeFourierCoefficients_apply {q : ℝ≥0∞} (hq : 1 < q)
    (φ : Curve (ℂ × ℂ)) (z : ℂ) (x : ℝ) (v : ℂ × ℂ) (L : (ℂ × ℂ) →L[ℝ] ℂ) (k : ℤ) :
    classicalShiftedFreeFourierCoefficients hq φ z x v L k =
      intervalFourierCoefficient 1 (fun t => L (classicalSolution φ z v t-classicalFreeVector x v t)) k := rfl

/-- A uniform constant for the shifted-free comparison. -/
def classicalShiftedFreeInterpolationConstant (ε : ℝ) (hε : 0 < ε) (M B : ℝ) : ℝ :=
  (2*(classicalSobolevErrorConstant M B+2*B)+
      (classicalSobolevDerivativeConstant M B+(2*Real.pi+3)*B))*
    unitIntervalC1FourierConstant (q := ENNReal.ofReal (1+ε)) (ENNReal.one_lt_ofReal.mpr (by linarith))+
      (classicalSobolevErrorConstant M B+2*B)

/-- Interpolation for the full reference error at one sufficiently distant lattice index. -/
theorem norm_classicalShiftedFreeFourierCoefficients_le
    (ε q : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hq0 : 1+ε ≤ q) (hq2 : q ≤ 2)
    (M B : ℝ) (hB : 0 ≤ B) (a : ScalarDomain 2 × ScalarDomain 2) (ha : ‖a‖ ≤ M)
    (n : ℤ) (hn : 1 ≤ (n.natAbs : ℝ)) (hBn : B ≤ (n.natAbs : ℝ)) (z : ℂ)
    (hδ : ‖z-((Real.pi*(n : ℝ) : ℝ) : ℂ)‖ ≤ B/(n.natAbs : ℝ))
    (v : ℂ × ℂ) (L : (ℂ × ℂ) →L[ℝ] ℂ) (hL : ‖L‖ ≤ 1) :
    ‖classicalShiftedFreeFourierCoefficients (q := ENNReal.ofReal q)
      (ENNReal.one_lt_ofReal.mpr (by linarith)) (classicalSobolevPotential a) z (Real.pi*(n : ℝ)) v L‖ ≤
      classicalShiftedFreeInterpolationConstant ε hε M B*‖v‖/
        (n.natAbs : ℝ)^(fundamentalFourierDecayExponent ε q) := by
  let R := classicalShiftedFreeRemainder (classicalSobolevPotential a) z (Real.pi*(n : ℝ)) v
  have hR : ContDiff ℝ 1 R := contDiff_classicalShiftedFreeRemainder _ _ _ _
  have hC := classicalSobolevErrorConstant_nonneg M B ((norm_nonneg a).trans ha)
  have hD := classicalSobolevDerivativeConstant_nonneg M B ((norm_nonneg a).trans ha)
  have hobs (w : ℂ × ℂ) : ‖L w‖ ≤ ‖w‖ :=
    (L.le_opNorm w).trans (by simpa using mul_le_mul_of_nonneg_right hL (norm_nonneg w))
  have hv (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖L (R t)‖ ≤ ((classicalSobolevErrorConstant M B+2*B)*‖v‖)/(n.natAbs : ℝ) :=
    (hobs (R t)).trans (classicalShiftedFreeRemainder_time_bounds M B hB a ha n hn hBn z hδ v ⟨t,ht⟩).1
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖deriv (fun s => L (R s)) t‖ ≤ (classicalSobolevDerivativeConstant M B+(2*Real.pi+3)*B)*‖v‖ := by
    have he : deriv (fun s => L (R s)) t = L (deriv R t) :=
      (L.hasFDerivAt.comp_hasDerivAt t ((contDiff_one_iff_deriv.mp hR).1 t).hasDerivAt).deriv
    rw [he]
    exact (hobs (deriv R t)).trans
      (classicalShiftedFreeRemainder_time_bounds M B hB a ha n hn hBn z hδ v ⟨t,ht⟩).2
  have h := norm_unitIntervalC1Coefficients_interpolate (fun t => L (R t)) (L.contDiff.comp hR)
    (1+ε) q (by linarith) (by linarith) hq0 hq2
    ((classicalSobolevErrorConstant M B+2*B)*‖v‖)
    ((classicalSobolevDerivativeConstant M B+(2*Real.pi+3)*B)*‖v‖)
    (n.natAbs : ℝ) (by positivity) (by positivity) hn hv hd
  have he : (q-(1+ε))/(2-(1+ε)) = fundamentalFourierDecayExponent ε q := by
    unfold fundamentalFourierDecayExponent
    congr 1 <;> ring
  rw [he] at h
  exact h.trans_eq (by unfold classicalShiftedFreeInterpolationConstant; ring)

/-- The final shifted-free assertion of G.3, uniformly under O(1/|n|) displacement.
The finite initial portion of each sequence remains unrestricted. -/
theorem exists_classicalShiftedFree_sequence_fourier_decay
    (ε q : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hq0 : 1+ε ≤ q) (hq2 : q ≤ 2)
    (M B : ℝ) (hB : 0 ≤ B) (N₀ : ℕ) :
    ∃ N : ℕ, 0 < N ∧ ∀ (ν : ℤ → ℂ),
      (∀ n : ℤ, N₀ ≤ n.natAbs → ‖ν n-(Real.pi : ℂ)*(n : ℂ)‖ ≤ B/(n.natAbs : ℝ)) →
      ∀ (a : ScalarDomain 2 × ScalarDomain 2), ‖a‖ ≤ M →
      ∀ (v : ℂ × ℂ) (L : (ℂ × ℂ) →L[ℝ] ℂ), ‖L‖ ≤ 1 →
      ∀ n : ℤ, N ≤ n.natAbs →
      ‖classicalShiftedFreeFourierCoefficients (q := ENNReal.ofReal q)
        (ENNReal.one_lt_ofReal.mpr (by linarith)) (classicalSobolevPotential a) (ν n) (Real.pi*(n : ℝ)) v L‖ ≤
        classicalShiftedFreeInterpolationConstant ε hε M B*‖v‖/
          (n.natAbs : ℝ)^(fundamentalFourierDecayExponent ε q) := by
  obtain ⟨N,hN⟩ := exists_nat_gt B
  have hNpos : 0 < N := by exact_mod_cast lt_of_le_of_lt hB hN
  refine ⟨max N N₀,lt_of_lt_of_le hNpos (le_max_left _ _),?_⟩
  intro ν hν a ha v L hL n hn
  have hnN := (le_max_left N N₀).trans hn
  have hn1 : 1 ≤ (n.natAbs : ℝ) := by exact_mod_cast lt_of_lt_of_le hNpos hnN
  have hBn : B ≤ (n.natAbs : ℝ) := hN.le.trans (by exact_mod_cast hnN)
  apply norm_classicalShiftedFreeFourierCoefficients_le ε q hε hε1 hq0 hq2 M B hB a ha n hn1 hBn
    (ν n) _ v L hL
  simpa only [Complex.ofReal_mul,Complex.ofReal_intCast] using hν n ((le_max_right N N₀).trans hn)

end NLS.ZakharovShabat
