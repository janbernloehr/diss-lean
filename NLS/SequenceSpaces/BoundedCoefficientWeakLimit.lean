import NLS.SequenceSpaces.ConjugateCotangent
import NLS.SequenceSpaces.UniformDualCoefficientLimits

/-! # Bounded coefficient limits under arbitrary bounded operators -/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- At a finite exponent above one, a bounded coefficient-null family
converges to zero under every continuous linear functional. -/
theorem tendsto_functional_of_bounded_coefficient_null
    (hp : p ≠ ⊤) (hp1 : 1 < p) {α : Type*} {l : Filter α}
    (x : α → Coeff p) (hx : Bornology.IsBounded (range x))
    (hc : ∀ n : ℤ, Tendsto (fun k => x k n) l (𝓝 0)) (L : Coeff p →L[ℂ] ℂ) :
    Tendsto (fun k => L (x k)) l (𝓝 0) := by
  let : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩
  have hq : p.conjExponent ≠ ⊤ :=
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p.conjExponent p).mpr hp1).ne
  let a := conjugateCotangent (q := p.conjExponent) hp hq L
  have ha : dualPairing a = L := dualPairing_conjugateCotangent hp hq L
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [eventually_small_dualPairing_of_bounded_coefficientwise hq x hx hc a ε hε] with k hk
  simpa only [ha,dist_zero_right] using hk a (fun _ => le_rfl)

/-- Bounded operators preserve coefficient-null convergence of bounded
families at every finite source exponent above one. -/
theorem tendsto_operator_coordinates_of_bounded_coefficient_null
    (hp : p ≠ ⊤) (hp1 : 1 < p) {α : Type*} {l : Filter α}
    (x : α → Coeff p) (hx : Bornology.IsBounded (range x))
    (hc : ∀ n : ℤ, Tendsto (fun k => x k n) l (𝓝 0)) (T : Coeff p →L[ℂ] Coeff q) (n : ℤ) :
    Tendsto (fun k => T (x k) n) l (𝓝 0) :=
  tendsto_functional_of_bounded_coefficient_null hp hp1 x hx hc
    ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) q n).comp T)

end NLS.Coeff
