import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Prescribing a fixed-time phase by a vanishing amplitude adjustment

Rounding a divergent positive mass to a prescribed phase lattice changes it
by a bounded amount. The square-root amplitude adjustment tends to one,
while its rescaled quadratic mass has exactly the selected phase.
-/
noncomputable section
set_option autoImplicit false
open Filter Topology
namespace NLS.Dynamics

def roundedPhaseMass (c δ M : ℝ) : ℝ := ((⌈c*M⌉ : ℤ)+δ)/c

def massPhaseScale (c δ M : ℝ) : ℝ := Real.sqrt (roundedPhaseMass c δ M/M)

theorem roundedPhaseMass_bounds (c δ M : ℝ) (hc : 0 < c) (hδ : 0 ≤ δ) :
    M ≤ roundedPhaseMass c δ M ∧ roundedPhaseMass c δ M ≤ M+(1+δ)/c := by
  constructor
  · apply (le_div_iff₀ hc).mpr
    linarith [Int.le_ceil (c*M)]
  · change ((⌈c*M⌉ : ℤ)+δ)/c ≤ _
    calc
      _ ≤ (c*M+1+δ)/c := div_le_div_of_nonneg_right (by linarith [Int.ceil_lt_add_one (c*M)]) hc.le
      _ = M+(1+δ)/c := by field_simp; ring

/-- The actual quadratic mass after amplitude rescaling is the chosen lattice point. -/
theorem massPhaseScale_sq_mul (c δ M : ℝ) (hc : 0 < c) (hδ : 0 ≤ δ) (hM : 0 < M) :
    (massPhaseScale c δ M)^2*M = roundedPhaseMass c δ M := by
  unfold massPhaseScale
  rw [Real.sq_sqrt (div_nonneg ((roundedPhaseMass_bounds c δ M hc hδ).1.trans' hM.le) hM.le),
    div_mul_cancel₀ _ hM.ne']

/-- Bounded mass rounding is invisible to the original amplitude in the divergent-mass limit. -/
theorem tendsto_massPhaseScale {ι : Type*} {l : Filter ι} (M : ι → ℝ)
    (hM : ∀ i, 0 < M i) (hdiv : Tendsto M l atTop)
    (c δ : ℝ) (hc : 0 < c) (hδ : 0 ≤ δ) :
    Tendsto (fun i => massPhaseScale c δ (M i)) l (𝓝 1) := by
  have hup : Tendsto (fun i => 1+((1+δ)/c)/M i) l (𝓝 (1:ℝ)) := by
    simpa only [add_zero] using tendsto_const_nhds.add (hdiv.const_div_atTop ((1+δ)/c))
  have hr : Tendsto (fun i => roundedPhaseMass c δ (M i)/M i) l (𝓝 (1:ℝ)) := by
    apply tendsto_const_nhds.squeeze hup
    · intro i
      exact (le_div_iff₀ (hM i)).mpr (by simpa only [one_mul] using (roundedPhaseMass_bounds c δ (M i) hc hδ).1)
    · intro i
      calc
        _ ≤ (M i+(1+δ)/c)/M i := div_le_div_of_nonneg_right (roundedPhaseMass_bounds c δ (M i) hc hδ).2 (hM i).le
        _ = 1+((1+δ)/c)/M i := by rw [add_div,div_self (hM i).ne']
  simpa only [massPhaseScale,Real.sqrt_one] using hr.sqrt

/-- At any prescribed real phase offset, the rounded mass has exactly that
phase; the rapidly growing integer part contributes one. -/
theorem exp_roundedPhaseMass (c δ M : ℝ) (hc : c ≠ 0) :
    Complex.exp (((2*Real.pi*c*roundedPhaseMass c δ M : ℝ) : ℂ)*Complex.I) =
      Complex.exp (((2*Real.pi*δ : ℝ) : ℂ)*Complex.I) := by
  have he : 2*Real.pi*c*roundedPhaseMass c δ M =
      (⌈c*M⌉ : ℤ)*(2*Real.pi)+2*Real.pi*δ := by
    unfold roundedPhaseMass
    field_simp
  rw [he,Complex.ofReal_add,add_mul,Complex.exp_add]
  have hi : Complex.exp ((((⌈c*M⌉ : ℤ) : ℝ)*(2*Real.pi) : ℝ)*Complex.I) = 1 := by
    have harg : ((((⌈c*M⌉ : ℤ) : ℝ)*(2*Real.pi) : ℝ) : ℂ)*Complex.I =
        (⌈c*M⌉ : ℤ)*(2*Real.pi*Complex.I) := by push_cast; ring
    rw [harg]
    exact Complex.exp_int_mul_two_pi_mul_I ⌈c*M⌉
  rw [hi,one_mul]

/-- A single fixed-time phase may be prescribed without changing the limiting
amplitude, even though the underlying positive mass diverges. -/
theorem exists_mass_phase_scales {ι : Type*} {l : Filter ι} (M : ι → ℝ)
    (hM : ∀ i, 0 < M i) (hdiv : Tendsto M l atTop)
    (c δ : ℝ) (hc : 0 < c) (hδ : 0 ≤ δ) :
    ∃ α : ι → ℝ, Tendsto α l (𝓝 1) ∧
      (∀ i, 0 ≤ α i) ∧
      ∀ i, Complex.exp (((2*Real.pi*c*(α i)^2*M i : ℝ) : ℂ)*Complex.I) =
        Complex.exp (((2*Real.pi*δ : ℝ) : ℂ)*Complex.I) := by
  refine ⟨fun i => massPhaseScale c δ (M i),tendsto_massPhaseScale M hM hdiv c δ hc hδ,
    fun i => Real.sqrt_nonneg _,fun i => ?_⟩
  rw [mul_assoc (2*Real.pi*c),massPhaseScale_sq_mul c δ (M i) hc hδ (hM i)]
  exact exp_roundedPhaseMass c δ (M i) hc.ne'

/-- Reversing a real mass frequency preserves either of the two separating
phases, one and minus one. -/
theorem exp_signed_mass_phase (c M : ℝ) (σ : ℂ) (hσ : σ = 1 ∨ σ = -1)
    (hphase : Complex.exp (((2*Real.pi*|c| * M : ℝ) : ℂ)*Complex.I) = σ) :
    Complex.exp (((2*Real.pi*c*M : ℝ) : ℂ)*Complex.I) = σ := by
  by_cases hc : 0 ≤ c
  · simpa only [abs_of_nonneg hc] using hphase
  · have he : (((2*Real.pi*c*M : ℝ) : ℂ)*Complex.I) =
        -(((2*Real.pi*|c| * M : ℝ) : ℂ)*Complex.I) := by
      rw [abs_of_neg (lt_of_not_ge hc)]
      push_cast
      ring
    rw [he,Complex.exp_neg,hphase]
    rcases hσ with rfl | rfl <;> norm_num

end NLS.Dynamics
