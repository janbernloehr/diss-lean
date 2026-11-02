import NLS.SequenceSpaces.PeriodOneMiuraCharts
import NLS.SequenceSpaces.PeriodOneMiuraRegularity

/-! # Literal distributional Miura lifts and their energy translation

Adding the constant (m+1)/2 converts the shifted Riccati equation into
q = u' + u² - (m+1)²/4. The coefficient identity fixes the exact constant
energy shift for subsequent comparison with the physical Hill trace.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS

/-- Unit-period raw L2 Fourier coefficients embedded in H^-1. -/
def periodOneL2Inclusion : Coeff 2 →L[ℂ] PeriodOneHminusOne :=
  boundedCoefficientsHminusOne.comp (Coeff.exponentInclusion (show (2 : ℝ≥0∞) ≤ ⊤ from le_top))

@[simp] theorem periodOneL2Inclusion_apply (a : Coeff 2) (k : ℤ) :
    (periodOneL2Inclusion a).val k = a k := by
  change (boundedCoefficientsHminusOne (Coeff.exponentInclusion le_top a)).val k = _
  rw [boundedCoefficientsHminusOne_apply,Coeff.exponentInclusion_apply]

/-- The literal distributional Miura potential u' + u². -/
def periodOneMiura (u : Coeff 2) : PeriodOneHminusOne :=
  periodOneShiftedMiura 0 u-periodOneL2Inclusion u

@[simp] theorem periodOneMiura_apply (u : Coeff 2) (k : ℤ) :
    (periodOneMiura u).val k = 2*I*(Real.pi : ℂ)*k*u k+∑' j : ℤ, u (k-j)*u j := by
  change (periodOneShiftedMiura 0 u).val k-(periodOneL2Inclusion u).val k = _
  rw [periodOneShiftedMiura_apply,periodOneL2Inclusion_apply]
  simp only [periodOneMassSymbol,Nat.cast_zero,zero_add,ofReal_one]
  ring

theorem periodOneMiuraProduct_single (v : Coeff 2) (c : ℂ) :
    periodOneMiuraProduct v (lp.single 2 0 c) = c • periodOneL2Inclusion v := by
  apply Subtype.ext
  funext k
  simp [periodOneMiuraProduct_apply,lp.single_apply,Pi.single_apply,mul_comm]

theorem periodOneMassOperator_single (c : ℂ) :
    periodOneMassOperator 0 (lp.single 2 0 c) = periodOneL2Inclusion (lp.single 2 0 c) := by
  apply Subtype.ext
  funext k
  rw [periodOneMassOperator_apply,periodOneL2Inclusion_apply]
  by_cases hk : k = 0
  · simp [hk,periodOneMassSymbol]
  · simp [lp.single_apply,hk]

theorem periodOneMiura_shift (m : ℕ) (v : Coeff 2) :
    periodOneMiura (v+lp.single 2 0 (((m : ℝ)+1 : ℝ)/2 : ℂ)) =
      periodOneShiftedMiura m v+
        periodOneL2Inclusion (lp.single 2 0 ((((m : ℝ)+1 : ℝ)/2 : ℂ)^2)) := by
  set c : ℂ := (((m : ℝ)+1 : ℝ)/2 : ℂ)
  have he : 2*c = (((m : ℝ)+1 : ℝ) : ℂ) := by dsimp [c]; push_cast; ring
  have hc : c • periodOneL2Inclusion (lp.single 2 0 c) =
      periodOneL2Inclusion (lp.single 2 0 (c^2)) := by
    rw [← map_smul]
    congr 1
    ext k
    simp [lp.single_apply,Pi.single_apply,pow_two]
  unfold periodOneMiura periodOneShiftedMiura
  simp only [map_add,add_apply]
  rw [periodOneMassOperator_single,periodOneMiuraProduct_single,
    periodOneMiuraProduct_comm (lp.single 2 0 c) v,periodOneMiuraProduct_single,
    periodOneMiuraProduct_single,hc]
  have hlinear : periodOneMassOperator 0 v+(c+c) • periodOneL2Inclusion v-
      periodOneL2Inclusion v = periodOneMassOperator m v := by
    apply Subtype.ext
    funext k
    change (periodOneMassOperator 0 v).val k+(c+c)*(periodOneL2Inclusion v).val k-
      (periodOneL2Inclusion v).val k = (periodOneMassOperator m v).val k
    rw [periodOneMassOperator_apply,periodOneMassOperator_apply,periodOneL2Inclusion_apply]
    have hc2 : c+c = (((m : ℝ)+1 : ℝ) : ℂ) := by simpa only [two_mul] using he
    rw [hc2]
    simp only [periodOneMassSymbol,Nat.cast_zero,zero_add,ofReal_one]
    ring
  rw [add_smul] at hlinear
  rw [← hlinear]
  abel

/-- Actual Miura lifts with the constant energy translation fixed explicitly. -/
theorem exists_periodOneMiura_energyChart (q : PeriodOneHminusOne) :
    ∃ m : ℕ, ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q ∈ U ∧
      ∃ u : PeriodOneHminusOne → Coeff 2, AnalyticOnNhd ℂ u U ∧
        ∀ r ∈ U, periodOneMiura (u r) = r+
          periodOneL2Inclusion (lp.single 2 0 ((((m : ℝ)+1 : ℝ)/2 : ℂ)^2)) := by
  obtain ⟨m,U,hU,hq,s,hs,_,hsolve⟩ := exists_periodOneMiuraChart q
  refine ⟨m,U,hU,hq,(fun r => s r+lp.single 2 0 (((m : ℝ)+1 : ℝ)/2 : ℂ)),?_,?_⟩
  · intro r hr
    exact (hs r hr).add analyticAt_const
  · intro r hr
    rw [periodOneMiura_shift,hsolve r hr]

/-- The literal Miura potential being L2 forces an L2 lift to be H1. -/
theorem periodOneMiura_memlp_sobolev_one (u q : Coeff 2)
    (himage : periodOneMiura u = periodOneL2Inclusion q) :
    Memℓp (fun k => (Weight.sobolev 1 k : ℂ)*u k) 2 := by
  apply periodOneMiuraSolution_memlp_sobolev_one 0 u (q+u)
  intro k
  have h := congrArg (fun a : PeriodOneHminusOne => a.val k) himage
  rw [periodOneMiura_apply,periodOneL2Inclusion_apply] at h
  change periodOneMassSymbol 0 k*u k+(∑' j : ℤ, u (k-j)*u j) = q k+u k
  rw [← h]
  simp only [periodOneMassSymbol,Nat.cast_zero,zero_add,ofReal_one]
  ring

end NLS
