import NLS.ZakharovShabat.ResonantCenterCollapse
import NLS.ZakharovShabat.ResonantRoots
import NLS.ZakharovShabat.UnweightedResonantDeterminant

/-!
# Actual diagonal centers and the spectral closing criterion

One open convex source neighborhood constructs all distant diagonal
centers. Each center solves the actual diagonal equation uniquely in
the full strip, has a nonzero residual derivative, and is real for a
source with either reality sign. If both off-diagonal coefficients
vanish there, the original periodic spectrum in that strip consists
of the center, and its determinant order is exactly two.

This supplies a closing criterion for finite-gap approximation. It
does not yet construct sources satisfying the simultaneous tail
equations, or assert finite-gap density.
-/

noncomputable section
open Set Metric
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The center selected by the actual resonant diagonal whenever a
refined-disc solution exists; the free center is the total fallback. -/
def weightedResonantDiagonalCenter (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) : ℂ :=
  if h : ∃ z ∈ refinedResonantDisk n,
      z = (Real.pi : ℂ)*n+weightedResonantAExtension hp w φ n z then
    Classical.choose h
  else (Real.pi : ℂ)*n

/-- The named actual center has the unique-solution and sharp
displacement properties under the distant-strip diagonal bounds. -/
theorem weightedResonantDiagonalCenter_spec (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ)
    (ha : AnalyticOnNhd ℂ (weightedResonantAExtension hp w φ n) (resonantStrip n))
    (hb : ∀ z ∈ resonantStrip n, ‖weightedResonantAExtension hp w φ n z‖ ≤ Real.pi/32) :
    let ζ := weightedResonantDiagonalCenter hp w φ n;
    ζ ∈ refinedResonantDisk n ∧ ‖ζ-(Real.pi : ℂ)*n‖ ≤ Real.pi/32 ∧
      ζ = (Real.pi : ℂ)*n+weightedResonantAExtension hp w φ n ζ ∧
      ∀ z ∈ resonantStrip n,
        z = (Real.pi : ℂ)*n+weightedResonantAExtension hp w φ n z → z = ζ := by
  obtain ⟨ζ,hζ,hsmall,hfix,hunique⟩ :=
    exists_unique_resonantDiagonalCenter n _ ha hb
  have hex : ∃ z ∈ refinedResonantDisk n,
      z = (Real.pi : ℂ)*n+weightedResonantAExtension hp w φ n z := ⟨ζ,hζ,hfix⟩
  have hchosen := Classical.choose_spec hex
  have heq : weightedResonantDiagonalCenter hp w φ n = ζ := by
    rw [weightedResonantDiagonalCenter,dif_pos hex]
    exact hunique _ (refinedResonantDisk_subset_strip n hchosen.1) hchosen.2
  simpa only [heq] using And.intro hζ (And.intro hsmall (And.intro hfix hunique))

/-- All actual distant centers and the closing criterion share one
open convex neighborhood. A closed strip contains one spectral point
of exact determinant order two when its two tail equations vanish. -/
theorem exists_uniform_weightedResonantDiagonalCenters
    (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ n : ℤ, N ≤ n.natAbs →
        let ζ := weightedResonantDiagonalCenter hp w ψ n;
        (ζ ∈ refinedResonantDisk n ∧ ‖ζ-(Real.pi : ℂ)*n‖ ≤ Real.pi/32 ∧
          ζ = (Real.pi : ℂ)*n+weightedResonantAExtension hp w ψ n ζ ∧
          ∀ z ∈ resonantStrip n,
            z = (Real.pi : ℂ)*n+weightedResonantAExtension hp w ψ n z → z = ζ) ∧
        deriv (fun z => z-(Real.pi : ℂ)*n-weightedResonantAExtension hp w ψ n z) ζ ≠ 0 ∧
        (∀ ε : ℂ, ε*ε = 1 → HasRealitySign w ε ψ → ζ.im = 0) ∧
        (weightedResonantBPlusExtension hp w ψ n ζ = 0 →
          weightedResonantBMinusExtension hp w ψ n ζ = 0 →
          (∀ z ∈ resonantStrip n, z ∈ periodicSpectrum hp (weightedBaseToPair w ψ) ↔ z = ζ) ∧
          ∀ z ∈ resonantStrip n,
            analyticOrderNatAt (resonantDeterminantExtension hp w ψ n) z =
              if z = ζ then 2 else 0) := by
  obtain ⟨N₁,hN₁,U₁,ho₁,hc₁,hφ₁,h0₁,h₁⟩ :=
    exists_uniform_resonantDeterminant_control hp hp1 w φ
  obtain ⟨N₂,_,U₂,ho₂,hc₂,hφ₂,h0₂,h₂⟩ :=
    exists_uniform_weightedDeterminant_spectral_iff hp w φ
  obtain ⟨N₃,_,U₃,ho₃,hc₃,hφ₃,h0₃,h₃⟩ := exists_uniform_resonantRoots hp hp1 w φ
  refine ⟨max N₁ (max N₂ N₃),hN₁.trans (le_max_left _ _),U₁ ∩ (U₂ ∩ U₃),
    ho₁.inter (ho₂.inter ho₃),hc₁.inter (hc₂.inter hc₃),⟨hφ₁,hφ₂,hφ₃⟩,⟨h0₁,h0₂,h0₃⟩,?_⟩
  intro ψ hψ n hn
  have hdom (z : ℂ) (hz : z ∈ resonantStrip n) :
      (ψ,z) ∈ weightedCorrectionDomain hp w n := (h₁ n (by omega)).1 ⟨hψ.1,hz⟩
  have hbound (z : ℂ) (hz : z ∈ resonantStrip n) := (h₁ n (by omega)).2 ψ hψ.1 z hz
  have hsmall (z : ℂ) (hz : z ∈ resonantStrip n) :
      ‖weightedPotentialSquareInShift hp w ψ n z hz‖ < 1 :=
    (hbound z hz).1.trans_lt (by norm_num)
  have ha : AnalyticOnNhd ℂ (weightedResonantAExtension hp w ψ n) (resonantStrip n) := by
    intro z hz
    exact (analyticAt_weightedResonantAExtension hp w n (ψ,z) (hdom z hz)).comp
      (analyticAt_const.prod analyticAt_id)
  have hb : AnalyticOnNhd ℂ (weightedResonantBPlusExtension hp w ψ n) (resonantStrip n) := by
    intro z hz
    exact (analyticAt_weightedResonantBPlusExtension hp w n (ψ,z) (hdom z hz)).comp
      (analyticAt_const.prod analyticAt_id)
  have hd : AnalyticOnNhd ℂ (weightedResonantBMinusExtension hp w ψ n) (resonantStrip n) := by
    intro z hz
    exact (analyticAt_weightedResonantBMinusExtension hp w n (ψ,z) (hdom z hz)).comp
      (analyticAt_const.prod analyticAt_id)
  have hdata := weightedResonantDiagonalCenter_spec hp w ψ n ha (fun z hz => (hbound z hz).2.1)
  let ζ := weightedResonantDiagonalCenter hp w ψ n
  refine ⟨hdata,deriv_resonantDiagonalResidual_ne_zero n _ ha
    (fun z hz => (hbound z hz).2.1) ζ hdata.1,?_,?_⟩
  · intro ε hε hreal
    refine resonantDiagonalCenter_im_eq_zero n _ ha (fun z hz => (hbound z hz).2.1)
      ?_ ζ (refinedResonantDisk_subset_strip n hdata.1) hdata.2.2.1
    intro z hz
    rw [weightedResonantAExtension_eq hp w ψ n _ (conj_mem_resonantStrip hz)
      (hsmall _ (conj_mem_resonantStrip hz)),weightedResonantAExtension_eq hp w ψ n z hz (hsmall z hz)]
    exact weightedResonantA_conj hp w ε hε ψ hreal n z hz (hsmall z hz)
      (hsmall _ (conj_mem_resonantStrip hz))
  · intro hbzero hdzero
    have hcollapse (z : ℂ) (hz : z ∈ resonantStrip n) :
        resonantDeterminantExtension hp w ψ n z = 0 ↔ z = ζ :=
      resonant_quadratic_zero_iff_eq_diagonalCenter n _ _ _ ha hb hd
        (fun z hz => ⟨(hbound z hz).2.1,(hbound z hz).2.2.2,(hbound z hz).2.2.1⟩)
        ζ hdata.1 hdata.2.2.1 hbzero hdzero z hz
    refine ⟨fun z hz => (h₂ ψ hψ.2.1 n (by omega) z hz).trans (hcollapse z hz),?_⟩
    obtain ⟨x,hx,y,hy,hxzero,hyzero,_,horder,_,_,_⟩ := h₃ ψ hψ.2.2 n (by omega)
    have hxζ := (hcollapse x (refinedResonantDisk_subset_strip n hx)).mp hxzero
    have hyζ := (hcollapse y (refinedResonantDisk_subset_strip n hy)).mp hyzero
    intro z hz
    rw [horder z hz,hxζ,hyζ]
    by_cases heq : z = weightedResonantDiagonalCenter hp w ψ n <;> simp [heq,ζ]

end NLS.ZakharovShabat
