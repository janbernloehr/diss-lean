import NLS.ZakharovShabat.FreeSpectralProducts
import NLS.SequenceSpaces.SobolevEmbedding
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Order.Filter.AtTopBot.Interval

/-!
# Convergent relative products for displaced spectral sequences

Away from the free lattice, the free resolvent followed by Sobolev embedding
makes the relative displacements absolutely summable at every finite Banach
exponent. The relative products therefore converge without an ordering choice.
-/

noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A displaced spectral sequence divided by the nonzero free denominator is absolutely summable. -/
theorem summable_norm_spectralRelativeDisplacement (hp : p ≠ ⊤) (ξ : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p) (z : ℂ) (hz : z ∉ freeLattice) :
    Summable (fun n : ℤ => ‖(ξ n-(Real.pi : ℂ)*n)/(z-(Real.pi : ℂ)*n)‖) := by
  let a : Coeff p := ⟨_, hξ⟩
  let b := WeightedCoeff.sobolevToL1CLM p hp (scalarFreeResolvent z hz a)
  have h := b.property.summable (by norm_num : 0 < (1 : ℝ≥0∞).toReal)
  simpa only [b, WeightedCoeff.sobolevToL1CLM_apply, scalarFreeResolvent_apply,
    ENNReal.toReal_one, Real.rpow_one] using h

/-- One normalized perturbed eigenvalue, relative to the free eigenvalue at the same signed index. -/
def spectralRelativeFactor (ξ : ℤ → ℂ) (z : ℂ) (n : ℤ) : ℂ :=
  (ξ n-z)/((Real.pi : ℂ)*n-z)

/-- Exact expansion about one; the sign reflects the `z-L` resolvent convention. -/
theorem spectralRelativeFactor_eq (ξ : ℤ → ℂ) (z : ℂ) (hz : z ∉ freeLattice) (n : ℤ) :
    spectralRelativeFactor ξ z n = 1 + -((ξ n-(Real.pi : ℂ)*n)/(z-(Real.pi : ℂ)*n)) := by
  have hd := free_denominator_ne_zero hz n
  unfold spectralRelativeFactor
  rw [show (Real.pi : ℂ)*n-z = -(z-(Real.pi : ℂ)*n) by ring]
  field_simp
  ring

/-- The relative product for a single displaced sequence converges unconditionally. -/
theorem multipliable_spectralRelativeFactor (hp : p ≠ ⊤) (ξ : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p) (z : ℂ) (hz : z ∉ freeLattice) :
    Multipliable (spectralRelativeFactor ξ z) := by
  rw [show spectralRelativeFactor ξ z = (fun n => 1 + -((ξ n-(Real.pi : ℂ)*n)/(z-(Real.pi : ℂ)*n)))
    from funext (spectralRelativeFactor_eq ξ z hz)]
  apply multipliable_one_add_of_summable
  simpa only [norm_neg] using summable_norm_spectralRelativeDisplacement hp ξ hξ z hz

/-- The relative product for both roots at each signed index. -/
def spectralRelativePairProduct (ξ η : ℤ → ℂ) (z : ℂ) : ℂ :=
  ∏' n : ℤ, (spectralRelativeFactor ξ z n * spectralRelativeFactor η z n)

theorem multipliable_spectralRelativePair (hp : p ≠ ⊤) (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p) (z : ℂ) (hz : z ∉ freeLattice) :
    Multipliable (fun n => spectralRelativeFactor ξ z n * spectralRelativeFactor η z n) :=
  (multipliable_spectralRelativeFactor hp ξ hξ z hz).mul (multipliable_spectralRelativeFactor hp η hη z hz)

/-- The symmetric cutoffs have the same value as the unconditional relative product. -/
theorem tendsto_spectralRelativePairProduct (hp : p ≠ ⊤) (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p) (z : ℂ) (hz : z ∉ freeLattice) :
    Tendsto (fun N : ℕ => ∏ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      (spectralRelativeFactor ξ z n * spectralRelativeFactor η z n)) atTop
      (𝓝 (spectralRelativePairProduct ξ η z)) :=
  (multipliable_spectralRelativePair hp ξ η hξ hη z hz).hasProd.comp Finset.tendsto_Icc_neg

/-- Relative factors are nonzero exactly when the corresponding spectral value differs from the parameter. -/
theorem spectralRelativeFactor_ne_zero_iff (ξ : ℤ → ℂ) (z : ℂ) (hz : z ∉ freeLattice) (n : ℤ) :
    spectralRelativeFactor ξ z n ≠ 0 ↔ ξ n ≠ z := by
  have hd : (Real.pi : ℂ)*n-z ≠ 0 := by
    simpa only [sub_ne_zero] using (sub_ne_zero.mp (free_denominator_ne_zero hz n)).symm
  simp [spectralRelativeFactor, hd, sub_ne_zero]

/-- Absolute relative convergence rules out spurious product zeros. -/
theorem spectralRelativePairProduct_ne_zero (hp : p ≠ ⊤) (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p) (z : ℂ) (hz : z ∉ freeLattice)
    (hroot : ∀ n : ℤ, ξ n ≠ z ∧ η n ≠ z) : spectralRelativePairProduct ξ η z ≠ 0 := by
  have single (α : ℤ → ℂ) (hα : Memℓp (fun n => α n-(Real.pi : ℂ)*n) p)
      (hn : ∀ n, α n ≠ z) : (∏' n, spectralRelativeFactor α z n) ≠ 0 := by
    rw [show spectralRelativeFactor α z = (fun n => 1 + -((α n-(Real.pi : ℂ)*n)/(z-(Real.pi : ℂ)*n)))
      from funext (spectralRelativeFactor_eq α z hz)]
    apply tprod_one_add_ne_zero_of_summable
    · intro n
      rw [← spectralRelativeFactor_eq α z hz]
      exact (spectralRelativeFactor_ne_zero_iff α z hz n).mpr (hn n)
    · simpa only [norm_neg] using summable_norm_spectralRelativeDisplacement hp α hα z hz
  rw [spectralRelativePairProduct, (multipliable_spectralRelativeFactor hp ξ hξ z hz).tprod_mul
    (multipliable_spectralRelativeFactor hp η hη z hz)]
  exact mul_ne_zero (single ξ hξ (fun n => (hroot n).1)) (single η hη (fun n => (hroot n).2))

/-- A selected root makes all sufficiently large symmetric products vanish. -/
theorem spectralRelativePairProduct_eq_zero_of_root (hp : p ≠ ⊤) (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p) (z : ℂ) (hz : z ∉ freeLattice)
    (n : ℤ) (hn : ξ n = z ∨ η n = z) : spectralRelativePairProduct ξ η z = 0 := by
  have he : ∀ᶠ N : ℕ in atTop, (∏ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      (spectralRelativeFactor ξ z k * spectralRelativeFactor η z k)) = 0 := by
    refine eventually_atTop.mpr ⟨n.natAbs, fun N hN => ?_⟩
    apply Finset.prod_eq_zero (show n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) from by
      simp only [Finset.mem_Icc]; constructor <;> omega)
    rcases hn with hn | hn <;> simp [spectralRelativeFactor, hn]
  exact tendsto_nhds_unique (tendsto_spectralRelativePairProduct hp ξ η hξ hη z hz)
    (tendsto_const_nhds.congr' (Filter.Eventually.mono he (fun _ h => h.symm)))

/-- The relative product has exactly the selected zeros, with no additional limiting zeros. -/
theorem spectralRelativePairProduct_eq_zero_iff (hp : p ≠ ⊤) (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p) (z : ℂ) (hz : z ∉ freeLattice) :
    spectralRelativePairProduct ξ η z = 0 ↔ ∃ n : ℤ, ξ n = z ∨ η n = z := by
  constructor
  · intro he
    by_contra hn
    push Not at hn
    exact spectralRelativePairProduct_ne_zero hp ξ η hξ hη z hz hn he
  · rintro ⟨n, hn⟩
    exact spectralRelativePairProduct_eq_zero_of_root hp ξ η hξ hη z hz n hn

end NLS.ZakharovShabat
