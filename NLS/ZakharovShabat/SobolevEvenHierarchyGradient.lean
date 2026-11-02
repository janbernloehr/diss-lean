import NLS.ZakharovShabat.SobolevEvenHamiltonian
import NLS.ZakharovShabat.SobolevSourceCotangent
import NLS.ZakharovShabat.SobolevSmoothFirstVariation

/-! # Actual weak gradients of the sharp even Hamiltonians -/
noncomputable section
open NLS.Fourier
open scoped ContDiff
namespace NLS.ZakharovShabat

def sobolevEvenHierarchyGradient (m : ℕ) (hm : 1 ≤ m) (ab : SobolevSource m) :
    NegativeScalarSobolev m × NegativeScalarSobolev m :=
  hierarchyWeakGradient m (sobolevEvenHamiltonian m hm) ab

theorem analyticAt_sobolevEvenHierarchyGradient (m : ℕ) (hm : 1 ≤ m) (ab : SobolevSource m) :
    AnalyticAt ℂ (sobolevEvenHierarchyGradient m hm) ab :=
  analyticAt_hierarchyWeakGradient m _ ab (analyticAt_sobolevEvenHamiltonian m hm ab)

theorem sobolevEvenHierarchyGradient_represents (m : ℕ) (hm : 1 ≤ m) (ab h : SobolevSource m) :
    WeightedCoeff.sobolevBilinearPairing (m : ℝ) h.1 (sobolevEvenHierarchyGradient m hm ab).1 +
      WeightedCoeff.sobolevBilinearPairing (m : ℝ) h.2 (sobolevEvenHierarchyGradient m hm ab).2 =
        fderiv ℂ (sobolevEvenHamiltonian m hm) ab h :=
  hierarchyWeakGradient_represents m _ ab h

private theorem fderiv_even_smooth_direction (m : ℕ) (hm : 1 ≤ m)
    (ab cd : SobolevSource m) (a b h l : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hh : ContDiff ℝ ∞ h) (hl : ContDiff ℝ ∞ l)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (hph : Function.Periodic h 1) (hpl : Function.Periodic l 1)
    (hac : ∀ j, ab.1.val j = periodOneCoefficient a j)
    (hbc : ∀ j, ab.2.val j = periodOneCoefficient b j)
    (hhc : ∀ j, cd.1.val j = periodOneCoefficient h j)
    (hlc : ∀ j, cd.2.val j = periodOneCoefficient l j) :
    fderiv ℂ (sobolevEvenHamiltonian m hm) ab cd =
      ∫ x in (0 : ℝ)..1, h x*(classicalNLSHierarchyGradient a b (2*m) x).1 +
        l x*(classicalNLSHierarchyGradient a b (2*m) x).2 :=
  fderiv_sobolevSource_eq_smooth_variation m _ (fun v w => classicalNLSHamiltonian v w (2*m))
    ab cd a b h l (analyticAt_sobolevEvenHamiltonian m hm ab)
    (fun ef v w hv hw hpv hpw hvc hwc => sobolevEvenHamiltonian_eq_classical m hm ef v w
      hv hw hpv hpw hvc hwc) ha hb hh hl hpa hpb hph hpl hac hbc hhc hlc _
    (hasDerivAt_classicalNLSHamiltonian a b h l ha hb hh hl hpa hpb hph hpl (2*m))

/-- On arbitrary smooth representatives, the sharp gradient has the actual
period-one Fourier integrals of the certified physical NLS gradient. -/
theorem sobolevEvenHierarchyGradient_eq_classical (m : ℕ) (hm : 1 ≤ m)
    (ab : SobolevSource m) (a b : ℝ → ℂ) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (hac : ∀ j, ab.1.val j = periodOneCoefficient a j)
    (hbc : ∀ j, ab.2.val j = periodOneCoefficient b j) (n : ℤ) :
    ((sobolevEvenHierarchyGradient m hm ab).1.val n, (sobolevEvenHierarchyGradient m hm ab).2.val n) =
      (periodOneCoefficient (fun x => (classicalNLSHierarchyGradient a b (2*m) x).1) n,
        periodOneCoefficient (fun x => (classicalNLSHierarchyGradient a b (2*m) x).2) n) := by
  have hz (j : ℤ) : (0 : ℂ) = periodOneCoefficient (fun _ : ℝ => (0 : ℂ)) j := by
    rw [periodOneCoefficient, ← unitFourierCoefficient_eq_fourierCoeffOn]
    simp [unitFourierCoefficient]
  apply Prod.ext
  · apply hierarchyFieldCotangent_eq_classical
    intro h f hf hpf hc
    change fderiv ℂ (sobolevEvenHamiltonian m hm) ab (h,0) = _
    have he := fderiv_even_smooth_direction m hm ab (h,0) a b f (fun _ => 0)
      ha hb hf contDiff_const hpa hpb hpf (fun _ => rfl) hac hbc hc hz
    simpa only [zero_mul, add_zero] using he
  · apply hierarchyFieldCotangent_eq_classical
    intro h f hf hpf hc
    change fderiv ℂ (sobolevEvenHamiltonian m hm) ab (0,h) = _
    have he := fderiv_even_smooth_direction m hm ab (0,h) a b (fun _ => 0) f
      ha hb contDiff_const hf hpa hpb (fun _ => rfl) hpf hac hbc hz hc
    simpa only [zero_mul, zero_add] using he

end NLS.ZakharovShabat
