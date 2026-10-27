import NLS.ZakharovShabat.AKNSIntervalOperator
import Mathlib.Analysis.Calculus.Deriv.Star

/-! # Conjugation and real complexification on the original AKNS domains -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set
namespace NLS.Fourier

/-- Conjugation preserves full interval H1 regularity, with the actual derivative. -/
theorem HasIntervalH1Regularity.conj {f : ℝ → ℂ} (hf : HasIntervalH1Regularity f) :
    HasIntervalH1Regularity (fun x => star (f x)) := by
  refine ⟨FunctionalAnalysis.absolutelyContinuousOnInterval_clm hf.1
    Complex.conjCLE.toContinuousLinearMap,?_⟩
  simpa only [deriv.star',Pi.star_def] using hf.2.star

end NLS.Fourier
namespace NLS.ZakharovShabat

/-- Both printed endpoint domains are closed under complex conjugation. -/
theorem HasAKNSIntervalDomain.conj {b : BoundaryCondition} {g : ℝ → ℂ × ℂ}
    (hg : HasAKNSIntervalDomain b g) : HasAKNSIntervalDomain b (fun x => star (g x)) := by
  refine ⟨hg.fst_regular.conj,hg.snd_regular.conj,?_,?_⟩
  · cases b <;> simpa [aknsBoundaryValue] using congrArg (fun z : ℂ => star z) hg.left
  · cases b <;> simpa [aknsBoundaryValue] using congrArg (fun z : ℂ => star z) hg.right

/-- Linear combinations stay in the same full classical endpoint domain. -/
theorem HasAKNSIntervalDomain.linearCombination {b : BoundaryCondition} {f g : ℝ → ℂ × ℂ}
    (hf : HasAKNSIntervalDomain b f) (hg : HasAKNSIntervalDomain b g) (a c : ℂ) :
    HasAKNSIntervalDomain b (fun x => a • f x+c • g x) := by
  refine ⟨hf.fst_regular.linearCombination hg.fst_regular a c,
    hf.snd_regular.linearCombination hg.snd_regular a c,?_,?_⟩
  · cases b <;> simpa [aknsBoundaryValue,smul_eq_mul] using
      congrArg₂ (fun x y : ℂ => a*x+c*y) hf.left hg.left
  · cases b <;> simpa [aknsBoundaryValue,smul_eq_mul] using
      congrArg₂ (fun x y : ℂ => a*x+c*y) hf.right hg.right

/-- The AKNS expression is defined over the reals: conjugating all data conjugates its value. -/
theorem aknsAction_star (q p : ℂ) (u v : ℂ × ℂ) :
    aknsAction (star q) (star p) (star u) (star v) = star (aknsAction q p u v) := by
  ext <;> simp [aknsAction]

/-- Actual derivatives commute with conjugation, including the full physical expression. -/
theorem aknsPhysicalOperator_star (q p : ℝ → ℂ) (g : ℝ → ℂ × ℂ) :
    aknsPhysicalOperator (fun x => star (q x)) (fun x => star (p x)) (fun x => star (g x)) =
      fun x => star (aknsPhysicalOperator q p g x) := by
  funext x
  change aknsAction (star (q x)) (star (p x)) (star (g x))
    (deriv (fun t => star ((g t).1)) x,deriv (fun t => star ((g t).2)) x) = _
  rw [deriv.star,deriv.star]
  simpa only [Prod.star_def,aknsPhysicalOperator] using
    aknsAction_star (q x) (p x) (g x) (deriv (fun t => (g t).1) x,deriv (fun t => (g t).2) x)

/-- For almost-everywhere real potentials the actual operator commutes with conjugation. -/
theorem aknsPhysicalOperator_star_of_real (q p : ℝ → ℂ)
    (hq : ∀ᵐ x ∂volume.restrict (Ioc 0 1), (q x).im = 0)
    (hp : ∀ᵐ x ∂volume.restrict (Ioc 0 1), (p x).im = 0) (g : ℝ → ℂ × ℂ) :
    aknsPhysicalOperator q p (fun x => star (g x))
      =ᵐ[volume.restrict (Ioc 0 1)] (fun x => star (aknsPhysicalOperator q p g x)) := by
  have he := aknsPhysicalOperator_star q p g
  filter_upwards [hq,hp] with x hx hy
  have hqx : star (q x) = q x := by apply Complex.ext <;> simp [hx]
  have hpx : star (p x) = p x := by apply Complex.ext <;> simp [hy]
  have h := congrFun he x
  simpa only [aknsPhysicalOperator,hqx,hpx] using h

/-- Real-valued functions are mapped to real-valued functions by the real AKNS expression. -/
theorem aknsPhysicalOperator_real (q p : ℝ → ℝ) (g : ℝ → ℝ × ℝ) (x : ℝ) :
    star (aknsPhysicalOperator (fun t => (q t : ℂ)) (fun t => (p t : ℂ))
      (fun t => (((g t).1 : ℂ), ((g t).2 : ℂ))) x) =
    aknsPhysicalOperator (fun t => (q t : ℂ)) (fun t => (p t : ℂ))
      (fun t => (((g t).1 : ℂ), ((g t).2 : ℂ))) x := by
  have h := congrFun (aknsPhysicalOperator_star (fun t => (q t : ℂ))
    (fun t => (p t : ℂ)) (fun t => (((g t).1 : ℂ), ((g t).2 : ℂ)))) x
  simpa [Prod.star_def] using h.symm

end NLS.ZakharovShabat
