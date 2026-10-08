import NLS.SequenceSpaces.HolderEmbedding
import NLS.SequenceSpaces.SpectralConvolution
import NLS.SequenceSpaces.SobolevHomogeneous
import NLS.ZakharovShabat.SourceHigherSobolevEmbedding
import Mathlib.Analysis.Analytic.Constructions

/-! # Sobolev operations for the physical Riccati hierarchy

Period-one differentiation loses one order. One additional Hilbert order
supplies weighted absolute summability, making the cubic recurrence a
continuous analytic map into the required lower Sobolev space.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat

abbrev ScalarSobolev (s : ℕ) := WeightedCoeff (Weight.sobolev (s : ℝ)) 2

/-- Forget higher regularity without changing any Fourier coefficient. -/
def hierarchySobolevInclusion (s t : ℕ) (h : t ≤ s) : ScalarSobolev s →L[ℂ] ScalarSobolev t :=
  WeightedCoeff.sobolevInclusion (by exact_mod_cast h)

@[simp] theorem hierarchySobolevInclusion_apply (s t : ℕ) (h : t ≤ s)
    (a : ScalarSobolev s) (n : ℤ) : (hierarchySobolevInclusion s t h a).val n = a.val n :=
  WeightedCoeff.sobolevInclusion_apply _ _ _

/-- The period-one derivative, allowing additional unused source regularity. -/
def hierarchySobolevDerivative (s t : ℕ) (h : t+1 ≤ s) : ScalarSobolev s →L[ℂ] ScalarSobolev t :=
  (2 : ℂ) • ((WeightedCoeff.sobolevDerivative (t : ℝ)).comp
    (WeightedCoeff.sobolevInclusion (show (t : ℝ)+1 ≤ (s : ℝ) by exact_mod_cast h)))

@[simp] theorem hierarchySobolevDerivative_apply (s t : ℕ) (h : t+1 ≤ s)
    (a : ScalarSobolev s) (n : ℤ) :
    (hierarchySobolevDerivative s t h a).val n = 2*Complex.I*(Real.pi:ℂ)*n*a.val n := by
  change (2:ℂ) * (Complex.I*(Real.pi:ℂ)*n*(WeightedCoeff.sobolevInclusion _ a).val n) = _
  rw [WeightedCoeff.sobolevInclusion_apply]
  ring

/-- One extra Sobolev order gives weighted ℓ¹ coefficients continuously. -/
def hierarchySobolevToL1 (s t : ℕ) (h : t+1 ≤ s) :
    ScalarSobolev s →L[ℂ] WeightedCoeff (SpectralWeight.sobolev (t : ℝ) (Nat.cast_nonneg t)).toWeight 1 :=
  (WeightedCoeff.inclusionCLM _ _ (by intro n; simp)).comp
    (WeightedCoeff.sobolevHolderInclusion (p := 2) (r := 2) (q := 1) (s : ℝ) (t : ℝ)
      (by simp) (by
        have hh : (t : ℝ)+1 ≤ (s : ℝ) := by exact_mod_cast h
        norm_num only [ENNReal.toReal_ofNat]
        linarith))

@[simp] theorem hierarchySobolevToL1_apply (s t : ℕ) (h : t+1 ≤ s)
    (a : ScalarSobolev s) (n : ℤ) : (hierarchySobolevToL1 s t h a).val n = a.val n := by
  simp only [hierarchySobolevToL1,ContinuousLinearMap.comp_apply,
    WeightedCoeff.inclusionCLM_apply,WeightedCoeff.sobolevHolderInclusion_apply]

/-- Weighted absolute summability includes continuously into the Hilbert space. -/
def hierarchySobolevFromL1 (t : ℕ) :
    WeightedCoeff (SpectralWeight.sobolev (t : ℝ) (Nat.cast_nonneg t)).toWeight 1 →L[ℂ] ScalarSobolev t :=
  (WeightedCoeff.exponentInclusion _ (by norm_num : (1:ℝ≥0∞) ≤ 2)).comp
    (WeightedCoeff.inclusionCLM _ _ (by intro n; simp))

@[simp] theorem hierarchySobolevFromL1_apply (t : ℕ)
    (a : WeightedCoeff (SpectralWeight.sobolev (t : ℝ) (Nat.cast_nonneg t)).toWeight 1) (n : ℤ) :
    (hierarchySobolevFromL1 t a).val n = a.val n := by
  simp only [hierarchySobolevFromL1,ContinuousLinearMap.comp_apply,
    WeightedCoeff.exponentInclusion_apply,WeightedCoeff.inclusionCLM_apply]

/-- The physical triple product, realized by the two actual Fourier convolutions. -/
def hierarchySobolevTriple (t : ℕ) (a b c : ScalarSobolev (t+1)) : ScalarSobolev t :=
  let w := SpectralWeight.sobolev (t : ℝ) (Nat.cast_nonneg t)
  let L := hierarchySobolevToL1 (t+1) t le_rfl
  hierarchySobolevFromL1 t (w.convolution (L a) (w.convolution (L b) (L c)))

@[simp] theorem hierarchySobolevTriple_apply (t : ℕ) (a b c : ScalarSobolev (t+1)) (n : ℤ) :
    (hierarchySobolevTriple t a b c).val n =
      ∑' j : ℤ, a.val (n-j) * ∑' k : ℤ, b.val (j-k)*c.val k := by
  simp only [hierarchySobolevTriple,hierarchySobolevFromL1_apply,SpectralWeight.convolution_apply,
    hierarchySobolevToL1_apply]

/-- The cubic recurrence preserves analytic dependence on any complex Banach parameter. -/
theorem analyticAt_hierarchySobolevTriple
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (t : ℕ) {f g h : E → ScalarSobolev (t+1)} {x : E}
    (hf : AnalyticAt ℂ f x) (hg : AnalyticAt ℂ g x) (hh : AnalyticAt ℂ h x) :
    AnalyticAt ℂ (fun y => hierarchySobolevTriple t (f y) (g y) (h y)) x := by
  let w := SpectralWeight.sobolev (t : ℝ) (Nat.cast_nonneg t)
  let L := hierarchySobolevToL1 (t+1) t le_rfl
  have hf' := (L.analyticAt (f x)).comp hf
  have hg' := (L.analyticAt (g x)).comp hg
  have hh' := (L.analyticAt (h x)).comp hh
  have hgh := ((w.convolutionCLM (p := 1)).analyticAt_bilinear (L (g x),L (h x))).comp
    (f := fun y => (L (g y),L (h y))) (hg'.prod hh')
  have hprod := ((w.convolutionCLM (p := 1)).analyticAt_bilinear
    (L (f x),w.convolution (L (g x)) (L (h x)))).comp
      (f := fun y => (L (f y),w.convolution (L (g y)) (L (h y)))) (hf'.prod hgh)
  exact ((hierarchySobolevFromL1 t).analyticAt _).comp hprod

end NLS.ZakharovShabat
