import NLS.Fourier.IntervalL2Realization
import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# The physical interval Hilbert space

The original `L²_c[0,1]` space consists of two scalar Lebesgue `L²` classes,
with the component-sum Hilbert norm. No endpoint matching is imposed. Actual
functions give elements of this space, independently of null-set changes.
-/

noncomputable section
open MeasureTheory Set
namespace NLS.ZakharovShabat

/-- Scalar Lebesgue square-integrable classes on the original interval. -/
abbrev IntervalL2 := Lp ℂ 2 (volume.restrict (Ioc (0 : ℝ) 1))

/-- The original potential/base space, with the sum of the two component energies. -/
abbrev IntervalPairL2 := WithLp 2 (IntervalL2 × IntervalL2)

/-- A measurable real-line representative; only its a.e. class on `[0,1]` matters. -/
def intervalL2Representative (u : IntervalPairL2) (x : ℝ) : ℂ × ℂ :=
  (u.ofLp.1 x, u.ofLp.2 x)

theorem memLp_intervalL2Representative (u : IntervalPairL2) :
    MemLp (intervalL2Representative u) 2 (volume.restrict (Ioc 0 1)) :=
  memLp_prod_iff.mpr ⟨Lp.memLp u.ofLp.1, Lp.memLp u.ofLp.2⟩

/-- The class of an arbitrary original square-integrable pair. -/
def intervalL2OfFunction (φ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) : IntervalPairL2 :=
  WithLp.toLp 2 (hφ.fst.toLp (fun x => (φ x).1), hφ.snd.toLp (fun x => (φ x).2))

theorem intervalL2Representative_ofFunction (φ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) :
    intervalL2Representative (intervalL2OfFunction φ hφ) =ᵐ[volume.restrict (Ioc 0 1)] φ := by
  filter_upwards [hφ.fst.coeFn_toLp, hφ.snd.coeFn_toLp] with x hx hy
  exact Prod.ext hx hy

/-- Equality of physical representatives on the interval determines the class. -/
theorem intervalL2Representative_injective (u v : IntervalPairL2)
    (h : intervalL2Representative u =ᵐ[volume.restrict (Ioc 0 1)] intervalL2Representative v) : u = v := by
  apply WithLp.ofLp_injective
  apply Prod.ext
  · exact Lp.ext (h.fun_comp Prod.fst)
  · exact Lp.ext (h.fun_comp Prod.snd)

@[simp] theorem intervalL2OfFunction_representative (u : IntervalPairL2) :
    intervalL2OfFunction (intervalL2Representative u) (memLp_intervalL2Representative u) = u :=
  intervalL2Representative_injective _ _ (intervalL2Representative_ofFunction _ _)

theorem intervalL2OfFunction_eq_iff (φ ψ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) (hψ : MemLp ψ 2 (volume.restrict (Ioc 0 1))) :
    intervalL2OfFunction φ hφ = intervalL2OfFunction ψ hψ ↔ φ =ᵐ[volume.restrict (Ioc 0 1)] ψ := by
  constructor
  · intro he
    exact (intervalL2Representative_ofFunction φ hφ).symm.trans
      (he ▸ intervalL2Representative_ofFunction ψ hψ)
  · intro he
    exact intervalL2Representative_injective _ _
      ((intervalL2Representative_ofFunction φ hφ).trans (he.trans (intervalL2Representative_ofFunction ψ hψ).symm))

theorem intervalL2Representative_add (u v : IntervalPairL2) :
    intervalL2Representative (u + v) =ᵐ[volume.restrict (Ioc 0 1)]
      (fun x => intervalL2Representative u x + intervalL2Representative v x) := by
  filter_upwards [Lp.coeFn_add u.ofLp.1 v.ofLp.1, Lp.coeFn_add u.ofLp.2 v.ofLp.2] with x hx hy
  exact Prod.ext hx hy

theorem intervalL2Representative_smul (c : ℂ) (u : IntervalPairL2) :
    intervalL2Representative (c • u) =ᵐ[volume.restrict (Ioc 0 1)]
      (fun x => c • intervalL2Representative u x) := by
  filter_upwards [Lp.coeFn_smul c u.ofLp.1, Lp.coeFn_smul c u.ofLp.2] with x hx hy
  exact Prod.ext hx hy

/-- The class norm uses ordinary Lebesgue measure, without period normalization. -/
theorem norm_sq_intervalL2 (u : IntervalL2) :
    ‖u‖ ^ 2 = ∫ x in (0 : ℝ)..1, ‖u x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def, intervalIntegral.integral_of_le (by norm_num)]
  simp only [real_inner_self_eq_norm_sq]

/-- Exact physical component-sum energy of the chosen representative. -/
theorem norm_sq_intervalL2Representative (u : IntervalPairL2) :
    ‖u‖ ^ 2 = (∫ x in (0 : ℝ)..1, ‖(intervalL2Representative u x).1‖ ^ 2) +
      ∫ x in (0 : ℝ)..1, ‖(intervalL2Representative u x).2‖ ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  exact congrArg₂ (· + ·) (norm_sq_intervalL2 u.ofLp.1) (norm_sq_intervalL2 u.ofLp.2)

/-- The original function has exactly its usual physical component-sum `L²` energy. -/
theorem norm_sq_intervalL2OfFunction (φ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) :
    ‖intervalL2OfFunction φ hφ‖ ^ 2 = (∫ x in (0 : ℝ)..1, ‖(φ x).1‖ ^ 2) +
      ∫ x in (0 : ℝ)..1, ‖(φ x).2‖ ^ 2 := by
  rw [norm_sq_intervalL2Representative]
  apply congrArg₂ (· + ·) <;> apply intervalIntegral.integral_congr_ae_restrict
  · simpa only [uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num), Function.comp_def] using
      (intervalL2Representative_ofFunction φ hφ).fun_comp (fun v => ‖v.1‖ ^ 2)
  · simpa only [uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num), Function.comp_def] using
      (intervalL2Representative_ofFunction φ hφ).fun_comp (fun v => ‖v.2‖ ^ 2)

end NLS.ZakharovShabat
