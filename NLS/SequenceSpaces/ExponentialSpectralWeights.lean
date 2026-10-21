import NLS.SequenceSpaces.LinearSpectralWeight
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

noncomputable section
set_option autoImplicit false
open Set
namespace NLS.SpectralWeight

/-- Exponentiating a nonnegative, increasing, subadditive radial profile
constructs an actual weight in the dissertation's class M. -/
def expProfile (g : ℝ → ℝ) (hg : ∀ x ≥ 0, 0 ≤ g x)
    (hm : MonotoneOn g (Ici 0))
    (ha : ∀ x ≥ 0, ∀ y ≥ 0, g (x+y) ≤ g x+g y) : SpectralWeight where
  value n := Real.exp (g |(n:ℝ)|)
  positive _ := Real.exp_pos _
  one_le n := Real.one_le_exp_iff.mpr (hg _ (abs_nonneg _))
  neg_eq n := by simp
  add_le m n := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    exact (hm (by change 0 ≤ |((m+n:ℤ):ℝ)|; positivity)
      (by change 0 ≤ |(m:ℝ)|+|(n:ℝ)|; positivity)
      (by simpa only [Int.cast_add] using abs_add_le (m:ℝ) (n:ℝ))).trans
      (ha _ (abs_nonneg _) _ (abs_nonneg _))
  monotone_nat m n h := by
    apply Real.exp_le_exp.mpr
    simp only [Int.cast_natCast,Nat.abs_cast]
    exact hm (by change 0 ≤ (m:ℝ); positivity)
      (by change 0 ≤ (n:ℝ); positivity) (by exact_mod_cast h)

@[simp] theorem expProfile_apply (g : ℝ → ℝ) (hg : ∀ x ≥ 0, 0 ≤ g x)
    (hm : MonotoneOn g (Ici 0))
    (ha : ∀ x ≥ 0, ∀ y ≥ 0, g (x+y) ≤ g x+g y) (n : ℤ) :
    expProfile g hg hm ha n = Real.exp (g |(n:ℝ)|) := rfl

/-- Gevrey exponential weights, including the Abel endpoint sigma=1. -/
def stretchedExponential (a σ : ℝ) (ha : 0 ≤ a) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    SpectralWeight :=
  expProfile (fun x => a*x^σ) (fun x hx => mul_nonneg ha (Real.rpow_nonneg hx _))
    (fun x hx y hy hxy => mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx hxy hσ) ha)
    (fun x hx y hy => by
      simpa only [mul_add] using mul_le_mul_of_nonneg_left
        (Real.rpow_add_le_add_rpow hx hy hσ hσ1) ha)

@[simp] theorem stretchedExponential_apply (a σ : ℝ)
    (ha : 0 ≤ a) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (n : ℤ) :
    stretchedExponential a σ ha hσ hσ1 n = Real.exp (a*|(n:ℝ)|^σ) := rfl

/-- The source Abel weight, with its exact pi-scaled Sobolev factor. -/
def abel (s a : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) : SpectralWeight :=
  (piSobolev s hs).mul (stretchedExponential a 1 ha zero_le_one le_rfl)

@[simp] theorem abel_apply (s a : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (n : ℤ) :
    abel s a hs ha n = (1+|(n:ℝ)*Real.pi|)^s*Real.exp (a*|(n:ℝ)|) := by
  simp only [abel,mul_apply,piSobolev_apply,stretchedExponential_apply,Real.rpow_one]

/-- The source Gevrey weight uses the unscaled bracket, exactly as printed. -/
def gevrey (s a σ : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    SpectralWeight := (sobolev s hs).mul (stretchedExponential a σ ha hσ hσ1)

@[simp] theorem gevrey_apply (s a σ : ℝ)
    (hs : 0 ≤ s) (ha : 0 ≤ a) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (n : ℤ) :
    gevrey s a σ hs ha hσ hσ1 n =
      (1+|(n:ℝ)|)^s*Real.exp (a*|(n:ℝ)|^σ) := by
  simp only [gevrey,mul_apply,sobolev_apply,Weight.sobolev_apply,stretchedExponential_apply]

/-- Multiplication preserves an existing exact linear factor. -/
theorem HasLinearFactor.mul_right {w : SpectralWeight} (hw : w.HasLinearFactor)
    (v : SpectralWeight) : (w.mul v).HasLinearFactor := by
  obtain ⟨u,hu⟩ := hw
  exact ⟨u.mul v,fun n => by simp only [mul_apply,hu]; ring⟩

theorem hasLinearFactor_abel (s a : ℝ) (hs : 1 ≤ s) (ha : 0 ≤ a) :
    (abel s a (zero_le_one.trans hs) ha).HasLinearFactor :=
  (hasLinearFactor_piSobolev s hs).mul_right _

theorem hasLinearFactor_gevrey (s a σ : ℝ)
    (hs : 1 ≤ s) (ha : 0 ≤ a) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    (gevrey s a σ (zero_le_one.trans hs) ha hσ hσ1).HasLinearFactor :=
  (hasLinearFactor_sobolev s hs).mul_right _

end NLS.SpectralWeight
