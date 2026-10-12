import NLS.Fourier.IntervalContinuousUniqueness
import NLS.ZakharovShabat.L2SourceG7Gradients

/-! # Uniqueness of continuous physical source gradients

The full Hilbert source cotangent determines the physical curve pointwise,
including both endpoints. A selected representative is therefore independent
of every construction choice whenever a continuous representative exists.
-/
noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- A common signed Fourier vector determines the physical gradient on [0,1]. -/
theorem L2RootGradientFourierRealizes.eqOn {q : ℝ≥0∞} {g h : ℝ → ℂ × ℂ} {a : CoeffPair q}
    (hg : Continuous g) (hh : Continuous h) (hga : L2RootGradientFourierRealizes g a)
    (hha : L2RootGradientFourierRealizes h a) : EqOn g h (Icc 0 1) := by
  have h₁ := eqOn_Icc_of_intervalFourierCoefficient_eq (by norm_num : (0 : ℝ) < 1)
    (fun s => (g s).1) (fun s => (h s).1) hg.fst hh.fst (fun n => by
      simpa only [neg_neg] using (hga (-n)).1.symm.trans (hha (-n)).1)
  have h₂ := eqOn_Icc_of_intervalFourierCoefficient_eq (by norm_num : (0 : ℝ) < 1)
    (fun s => (g s).2) (fun s => (h s).2) hg.snd hh.snd (fun n => (hga n).2.symm.trans (hha n).2)
  intro s hs
  exact Prod.ext (h₁ hs) (h₂ hs)

/-- An actual source cotangent is represented by an unconjugated physical integral. -/
def SourcePhysicalGradientRepresents (L : CoeffPair 2 →L[ℂ] ℂ) (g : Curve (ℂ × ℂ)) : Prop :=
  ∀ h : CoeffPair 2, L h = ∫ s in (0 : ℝ)..1,
    (extend g s).1*(physicalBase (periodOnePotential h) s).1+
    (extend g s).2*(physicalBase (periodOnePotential h) s).2

/-- Uniqueness is equality of continuous curves, not merely almost-everywhere equality. -/
theorem SourcePhysicalGradientRepresents.unique {L : CoeffPair 2 →L[ℂ] ℂ} {g h : Curve (ℂ × ℂ)}
    (hg : SourcePhysicalGradientRepresents L g) (hh : SourcePhysicalGradientRepresents L h) : g = h := by
  have hcoeff (k : ℤ) :
      intervalFourierCoefficient 1 (fun s => (extend g s).1) k =
        intervalFourierCoefficient 1 (fun s => (extend h s).1) k ∧
      intervalFourierCoefficient 1 (fun s => (extend g s).2) k =
        intervalFourierCoefficient 1 (fun s => (extend h s).2) k := by
    have h₁ := (hg (CoeffPair.ofFinsupp (Finsupp.single (-k) 1,0))).symm.trans
      (hh (CoeffPair.ofFinsupp (Finsupp.single (-k) 1,0)))
    have h₂ := (hg (CoeffPair.ofFinsupp (0,Finsupp.single (-k) 1))).symm.trans
      (hh (CoeffPair.ofFinsupp (0,Finsupp.single (-k) 1)))
    rw [source_physical_gradient_pairing_single_fst,source_physical_gradient_pairing_single_fst,neg_neg] at h₁
    rw [source_physical_gradient_pairing_single_snd,source_physical_gradient_pairing_single_snd,neg_neg] at h₂
    have hc (f : ℝ → ℂ) : intervalFourierCoefficient 1 f k = unitFourierCoefficient f k := by
      rw [intervalFourierCoefficient_eq_fourierCoeffOn (by norm_num),unitFourierCoefficient_eq_fourierCoeffOn]
    exact ⟨by simpa only [hc] using h₁,by simpa only [hc] using h₂⟩
  have h₁ := eqOn_Icc_of_intervalFourierCoefficient_eq (by norm_num : (0 : ℝ) < 1)
    (fun s => (extend g s).1) (fun s => (extend h s).1)
    (continuous_extend g).fst (continuous_extend h).fst (fun k => (hcoeff k).1)
  have h₂ := eqOn_Icc_of_intervalFourierCoefficient_eq (by norm_num : (0 : ℝ) < 1)
    (fun s => (extend g s).2) (fun s => (extend h s).2)
    (continuous_extend g).snd (continuous_extend h).snd (fun k => (hcoeff k).2)
  apply ContinuousMap.ext
  intro s
  simpa only [extend_coe] using Prod.ext (h₁ s.property) (h₂ s.property)

/-- Select the unique continuous physical representative when one exists.
Outside that domain this total definition returns zero; no representation
identity is asserted there. -/
def sourcePhysicalGradientCurve (L : CoeffPair 2 →L[ℂ] ℂ) : Curve (ℂ × ℂ) :=
  by
    classical
    exact if h : ∃ g, SourcePhysicalGradientRepresents L g then h.choose else 0

/-- Every constructed physical representative equals the selected curve. -/
theorem sourcePhysicalGradientCurve_eq_of_represents {L : CoeffPair 2 →L[ℂ] ℂ}
    {g : Curve (ℂ × ℂ)} (hg : SourcePhysicalGradientRepresents L g) :
    sourcePhysicalGradientCurve L = g := by
  classical
  have hex : ∃ g, SourcePhysicalGradientRepresents L g := ⟨g,hg⟩
  rw [sourcePhysicalGradientCurve,dif_pos hex]
  exact hex.choose_spec.unique hg

theorem sourcePhysicalGradientCurve_represents {L : CoeffPair 2 →L[ℂ] ℂ}
    (hL : ∃ g, SourcePhysicalGradientRepresents L g) :
    SourcePhysicalGradientRepresents L (sourcePhysicalGradientCurve L) := by
  obtain ⟨g,hg⟩ := hL
  rw [sourcePhysicalGradientCurve_eq_of_represents hg]
  exact hg

end NLS.ZakharovShabat
