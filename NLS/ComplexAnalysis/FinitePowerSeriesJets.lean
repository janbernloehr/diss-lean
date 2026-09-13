import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Ext
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Finite Taylor jets and formal power-series multiplication

A finite coefficient vector is extended by zero to a formal power series.
Multiplication followed by restriction is the usual finite Taylor convolution.
Truncating an intermediate product does not change any retained coefficient.
-/

noncomputable section
open Complex PowerSeries
namespace NLS.ComplexAnalysis

/-- Extend a finite complex coefficient vector by zero to a formal power series. -/
def finiteJetSeries (N : ℕ) : (Fin N → ℂ) →ₗ[ℂ] PowerSeries ℂ where
  toFun v := PowerSeries.mk (fun j => if h : j < N then v ⟨j,h⟩ else 0)
  map_add' := by
    intro u v
    ext j
    by_cases h : j < N <;> simp [PowerSeries.coeff_mk,h]
  map_smul' := by
    intro c v
    ext j
    by_cases h : j < N <;> simp [PowerSeries.coeff_mk,h]

/-- Retained coefficients are exactly the original finite vector. -/
@[simp] theorem coeff_finiteJetSeries (N : ℕ) (v : Fin N → ℂ) (j : ℕ) :
    PowerSeries.coeff j (finiteJetSeries N v) = if h : j < N then v ⟨j,h⟩ else 0 :=
  by simp [finiteJetSeries]

/-- Restrict a formal series to its first `N` coefficients. -/
def seriesFiniteJet (N : ℕ) : PowerSeries ℂ →ₗ[ℂ] (Fin N → ℂ) where
  toFun f j := PowerSeries.coeff j.val f
  map_add' := by intro f g; funext j; exact map_add _ _ _
  map_smul' := by intro c f; funext j; exact map_smul _ _ _

@[simp] theorem seriesFiniteJet_apply (N : ℕ) (f : PowerSeries ℂ) (j : Fin N) :
    seriesFiniteJet N f j = PowerSeries.coeff j.val f := rfl

/-- Restriction recovers every finite coefficient vector. -/
@[simp] theorem seriesFiniteJet_finiteJetSeries (N : ℕ) (v : Fin N → ℂ) :
    seriesFiniteJet N (finiteJetSeries N v) = v := by
  funext j
  simp

/-- Vanishing of all retained coefficients is equivalent to the corresponding order bound. -/
theorem seriesFiniteJet_eq_zero_iff_order (N : ℕ) (f : PowerSeries ℂ) :
    seriesFiniteJet N f = 0 ↔ (N : ℕ∞) ≤ f.order := by
  constructor
  · intro h
    exact PowerSeries.nat_le_order f N (fun j hj => congrFun h ⟨j,hj⟩)
  · intro h
    funext j
    exact PowerSeries.coeff_of_lt_order j.val ((by exact_mod_cast j.isLt : (j.val : ℕ∞) < N).trans_le h)

/-- Removing the first `N` coefficients leaves a series of order at least `N`. -/
theorem finiteJetSeries_remainder_order (N : ℕ) (f : PowerSeries ℂ) :
    (N : ℕ∞) ≤ (f-finiteJetSeries N (seriesFiniteJet N f)).order := by
  apply PowerSeries.nat_le_order
  intro j hj
  simp [hj]

/-- A factor of order at least `N` makes every retained coefficient of its product vanish. -/
theorem seriesFiniteJet_mul_eq_zero_of_order (N : ℕ) (f g : PowerSeries ℂ)
    (hg : (N : ℕ∞) ≤ g.order) : seriesFiniteJet N (f*g) = 0 := by
  rw [seriesFiniteJet_eq_zero_iff_order,PowerSeries.order_mul]
  exact hg.trans (le_add_self : g.order ≤ f.order+g.order)

/-- Replacing the right factor by its truncated coefficient vector preserves the product jet. -/
theorem seriesFiniteJet_mul_truncate (N : ℕ) (f g : PowerSeries ℂ) :
    seriesFiniteJet N (f*finiteJetSeries N (seriesFiniteJet N g)) = seriesFiniteJet N (f*g) := by
  have h := seriesFiniteJet_mul_eq_zero_of_order N f (g-finiteJetSeries N (seriesFiniteJet N g))
    (finiteJetSeries_remainder_order N g)
  rw [mul_sub,map_sub,sub_eq_zero] at h
  exact h.symm

/-- Truncated multiplication by a formal power series, on scalar Taylor coefficients. -/
def scalarTaylorJetMap (f : PowerSeries ℂ) (N : ℕ) : (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ) where
  toFun v := seriesFiniteJet N (f*finiteJetSeries N v)
  map_add' := by intro u v; rw [map_add,mul_add,map_add]
  map_smul' := by intro c v; rw [map_smul,mul_smul_comm,map_smul]; rfl

@[simp] theorem scalarTaylorJetMap_apply (f : PowerSeries ℂ) (N : ℕ) (v : Fin N → ℂ) (j : Fin N) :
    scalarTaylorJetMap f N v j = PowerSeries.coeff j.val (f*finiteJetSeries N v) := rfl

/-- The formal action is the ordinary lower triangular Taylor convolution. -/
theorem scalarTaylorJetMap_apply_eq_sum (f : PowerSeries ℂ) (N : ℕ) (v : Fin N → ℂ) (k : Fin N) :
    scalarTaylorJetMap f N v k = ∑ j ∈ Finset.range (k.val+1), PowerSeries.coeff j f *
      (if h : k.val-j < N then v ⟨k.val-j,h⟩ else 0) := by
  rw [scalarTaylorJetMap_apply,PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_finiteJetSeries]

/-- Constant one acts as the identity on every finite Taylor space. -/
@[simp] theorem scalarTaylorJetMap_one (N : ℕ) : scalarTaylorJetMap 1 N = LinearMap.id := by
  ext v j
  simp

/-- The zero series acts by the zero map. -/
@[simp] theorem scalarTaylorJetMap_zero (N : ℕ) : scalarTaylorJetMap 0 N = 0 := by
  ext v j
  simp

/-- Formal multiplication becomes composition of finite Taylor convolution maps. -/
theorem scalarTaylorJetMap_mul (f g : PowerSeries ℂ) (N : ℕ) :
    scalarTaylorJetMap (f*g) N = (scalarTaylorJetMap f N).comp (scalarTaylorJetMap g N) := by
  apply LinearMap.ext
  intro v
  change seriesFiniteJet N ((f*g)*finiteJetSeries N v) =
    seriesFiniteJet N (f*finiteJetSeries N (seriesFiniteJet N (g*finiteJetSeries N v)))
  rw [seriesFiniteJet_mul_truncate,mul_assoc]

/-- The finite Taylor action is additive in the multiplying series. -/
theorem scalarTaylorJetMap_add (f g : PowerSeries ℂ) (N : ℕ) :
    scalarTaylorJetMap (f+g) N = scalarTaylorJetMap f N+scalarTaylorJetMap g N := by
  ext v j
  simp [add_mul]

/-- Multiplying by a formal unit gives a bijection on every finite Taylor space. -/
theorem scalarTaylorJetMap_bijective_of_isUnit (f : PowerSeries ℂ) (hf : IsUnit f) (N : ℕ) :
    Function.Bijective (scalarTaylorJetMap f N) := by
  obtain ⟨u,rfl⟩ := hf
  have hl : (scalarTaylorJetMap (↑u⁻¹) N).comp (scalarTaylorJetMap (↑u) N) = LinearMap.id := by
    rw [← scalarTaylorJetMap_mul,Units.inv_mul,scalarTaylorJetMap_one]
  have hr : (scalarTaylorJetMap (↑u) N).comp (scalarTaylorJetMap (↑u⁻¹) N) = LinearMap.id := by
    rw [← scalarTaylorJetMap_mul,Units.mul_inv,scalarTaylorJetMap_one]
  have hli : Function.LeftInverse (scalarTaylorJetMap (↑u⁻¹) N) (scalarTaylorJetMap (↑u) N) := by
    intro v
    exact congrArg (fun f : (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ) => f v) hl
  have hri : Function.RightInverse (scalarTaylorJetMap (↑u⁻¹) N) (scalarTaylorJetMap (↑u) N) := by
    intro v
    exact congrArg (fun f : (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ) => f v) hr
  exact ⟨hli.injective,hri.surjective⟩

end NLS.ComplexAnalysis
