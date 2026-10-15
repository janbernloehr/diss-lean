import NLS.ZakharovShabat.SourceBirkhoffOriginalMap
import NLS.ZakharovShabat.SourceBirkhoffDenseRange
import NLS.ZakharovShabat.SourceBirkhoffLemma15_3

/-!
# Section 14's map with its original actions and angles

The same normalized root family supplies the literal rectangular formula,
a complex analytic sequence map, and exact indexed-action radii. The
existing canonical and real inverse results apply to this very map.
Compatibility on complex intersections of different exponent domains is
not asserted by this interface.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Provenance and exact scalar evaluations for the original Section 14 map. -/
structure SourceSection14OriginalData (hp : p ≠ ⊤) (hp1 : 1 < p)
    (W₀ W V : Set (CoeffPair p)) (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n) : Prop where
  previous : SourceLemma12_12Data hp hp1 W₀ W s
  complex : SourceBirkhoffMapComplexData hp hp1 W W V s
  indexed_action_radius : ∀ ψ ∈ V, ∀ n : ℤ,
    ((sourceBirkhoffMap hp hp1 s ψ).1 n)^2 + ((sourceBirkhoffMap hp hp1 s ψ).2 n)^2 =
      2*sourceIndexedAction hp hp1 n ψ

namespace SourceSection14OriginalData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W V : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Equation (3.1) for the actual sequence coordinates and original theta. -/
theorem rectangular_formula (D : SourceSection14OriginalData hp hp1 W₀ W V s)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0) :
    let a := sourceNormalizedActionRoot hp hp1 n ψ *
      canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n / (Real.sqrt 2 : ℂ)
    (sourceBirkhoffMap hp hp1 s ψ).1 n = a*Complex.cos (sourceAngularOriginalTheta hp hp1 n s ψ) ∧
      (sourceBirkhoffMap hp hp1 s ψ).2 n = a*Complex.sin (sourceAngularOriginalTheta hp hp1 n s ψ) := by
  rw [(D.complex.coordinates ψ hψ n).1,(D.complex.coordinates ψ hψ n).2]
  exact D.previous.birkhoffXY_original_formula ψ (D.complex.source_subset hψ) n hgap

/-- Theorem 14.1(iii), including regular Fourier witnesses below exponent two. -/
theorem canonical (D : SourceSection14OriginalData hp hp1 W₀ W V s)
    (φ : realTypeSourceSubmodule p) :
    ∃ X Y : ℤ → RegularSourceCotangent p,
      (∀ n, (X n).toCotangent = fderiv ℂ (fun ψ => (sourceBirkhoffMap hp hp1 s ψ).1 n) φ.val ∧
        (Y n).toCotangent = fderiv ℂ (fun ψ => (sourceBirkhoffMap hp hp1 s ψ).2 n) φ.val) ∧
      ∀ n m, (X n).bivector (X m) = 0 ∧
        (X n).bivector (Y m) = -(if n = m then 1 else 0) ∧ (Y n).bivector (Y m) = 0 :=
  D.complex.lemma15_3 φ

/-- The real map is analytic, injective, locally analytically invertible, and has open dense image. -/
theorem real_geometry (D : SourceSection14OriginalData hp hp1 W₀ W V s) :
    AnalyticOnNhd ℝ (sourceRealBirkhoffMap hp hp1 s) univ ∧
    Function.Injective (sourceRealBirkhoffMap hp hp1 s) ∧
    IsOpen (range (sourceRealBirkhoffMap hp hp1 s)) ∧ Dense (range (sourceRealBirkhoffMap hp hp1 s)) ∧
    ∀ φ : realTypeSourceSubmodule p,
      ∃ g : (RealCoeff p × RealCoeff p) → realTypeSourceSubmodule p,
        AnalyticAt ℝ g (sourceRealBirkhoffMap hp hp1 s φ) ∧
        g (sourceRealBirkhoffMap hp hp1 s φ) = φ ∧
        (∀ᶠ ψ in 𝓝 φ, g (sourceRealBirkhoffMap hp hp1 s ψ) = ψ) ∧
        (∀ᶠ z in 𝓝 (sourceRealBirkhoffMap hp hp1 s φ), sourceRealBirkhoffMap hp hp1 s (g z) = z) := by
  refine ⟨D.complex.real_map_analytic,D.complex.proposition17_2,
    D.complex.real_map_open_dense_range.1,D.complex.real_map_open_dense_range.2,?_⟩
  intro φ
  obtain ⟨g,ha,hg,hl,hr,_⟩ := D.complex.proposition17_1 φ
  exact ⟨g,ha,hg,hl,hr⟩

/-- Theorem 14.1(v), with the surjectivity range restricted to p ≤ 2. -/
theorem global_inverse (D : SourceSection14OriginalData hp hp1 W₀ W V s) (hp2 : p ≤ 2) :
    ∃ e : realTypeSourceSubmodule p ≃ₜ (RealCoeff p × RealCoeff p),
      (∀ φ, e φ = sourceRealBirkhoffMap hp hp1 s φ) ∧
      AnalyticOnNhd ℝ (fun φ => e φ) univ ∧ AnalyticOnNhd ℝ (fun y => e.symm y) univ :=
  ⟨D.complex.realHomeomorph hp2,fun _ => rfl,D.complex.real_map_analytic,
    D.complex.realHomeomorph_symm_analytic hp2⟩

end SourceSection14OriginalData

/-- Construct the sequence map from the original source family for every finite p > 1. -/
theorem sourceSection14_original (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ W V : Set (CoeffPair p), ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
      SourceSection14OriginalData hp hp1 W₀ W V s := by
  obtain ⟨W₀,_,_,_,W,_,_,_,s,H⟩ := sourceLemma12_12 hp hp1
  obtain ⟨V,D,hI⟩ := H.exists_original_birkhoff_map
  exact ⟨W₀,W,V,s,H,D,hI⟩

end NLS.ZakharovShabat
