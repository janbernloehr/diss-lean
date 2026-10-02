import NLS.ZakharovShabat.SourceBirkhoffCanonicalAllExponents
import NLS.ZakharovShabat.SourceBirkhoffTheorem15_2

/-! # Lemma 15.3 for the sequence-valued Birkhoff map

The coordinates of the actual map of Theorem 15.2 have regular full
complex derivatives at every real source, including closed gaps. Their
physical Poisson pairings are canonical at every finite exponent above
one. The mixed bracket is the absolutely convergent Fourier sum with
frequency reversal and factor `-i`.
-/

noncomputable section
open Set Complex Filter Topology NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- Exact scalar evaluation holds on a neighborhood, so it also
identifies the derivatives of the actual sequence coordinates. -/
theorem fderiv_coordinates
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (n : ℤ)
    (φ : CoeffPair p) (hφ : φ ∈ W) :
    fderiv ℂ (fun ψ => (sourceBirkhoffMap hp hp1 s ψ).1 n) φ = fderiv ℂ (sourceBirkhoffX hp hp1 n s) φ ∧
    fderiv ℂ (fun ψ => (sourceBirkhoffMap hp hp1 s ψ).2 n) φ = fderiv ℂ (sourceBirkhoffY hp hp1 n s) φ := by
  have hx : (fun ψ => (sourceBirkhoffMap hp hp1 s ψ).1 n) =ᶠ[𝓝 φ] sourceBirkhoffX hp hp1 n s := by
    filter_upwards [D.source_open.mem_nhds hφ] with ψ hψ
    exact (D.coordinates ψ hψ n).1
  have hy : (fun ψ => (sourceBirkhoffMap hp hp1 s ψ).2 n) =ᶠ[𝓝 φ] sourceBirkhoffY hp hp1 n s := by
    filter_upwards [D.source_open.mem_nhds hφ] with ψ hψ
    exact (D.coordinates ψ hψ n).2
  exact ⟨hx.fderiv_eq,hy.fderiv_eq⟩

/-- All three canonical identities for the actual map, with verified
square-summable Fourier coefficients for every full coordinate derivative. -/
theorem lemma15_3
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (φ : realTypeSourceSubmodule p) :
    ∃ X Y : ℤ → RegularSourceCotangent p,
      (∀ n, (X n).toCotangent = fderiv ℂ (fun ψ => (sourceBirkhoffMap hp hp1 s ψ).1 n) φ.val ∧
        (Y n).toCotangent = fderiv ℂ (fun ψ => (sourceBirkhoffMap hp hp1 s ψ).2 n) φ.val) ∧
      ∀ n m, (X n).bivector (X m) = 0 ∧
        (X n).bivector (Y m) = -(if n = m then 1 else 0) ∧ (Y n).bivector (Y m) = 0 := by
  obtain ⟨X,Y,hder,hbracket⟩ := D.angular.exists_birkhoff_regular_canonical
    W D.source_open D.source_subset D.real_subset φ
  refine ⟨X,Y,?_,hbracket⟩
  intro n
  have h := D.fderiv_coordinates n φ.val (D.real_subset φ.property)
  exact ⟨(hder n).1.trans h.1.symm,(hder n).2.trans h.2.symm⟩

/-- The mixed identity is the literal absolutely convergent physical
Fourier bracket, also below two and at closed gaps. -/
theorem mixed_fourier_canonical
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (n m : ℤ) (φ : realTypeSourceSubmodule p) :
    let L := fderiv ℂ (fun ψ => (sourceBirkhoffMap hp hp1 s ψ).1 n) φ.val
    let M := fderiv ℂ (fun ψ => (sourceBirkhoffMap hp hp1 s ψ).2 m) φ.val
    Summable (fun j : ℤ => ‖L (CoeffPair.inlCLM (lp.single p j 1)) *
      M (CoeffPair.inrCLM (lp.single p (-j) 1)) -
      L (CoeffPair.inrCLM (lp.single p j 1)) * M (CoeffPair.inlCLM (lp.single p (-j) 1))‖) ∧
    -I * ∑' j : ℤ, (L (CoeffPair.inlCLM (lp.single p j 1)) *
      M (CoeffPair.inrCLM (lp.single p (-j) 1)) -
      L (CoeffPair.inrCLM (lp.single p j 1)) * M (CoeffPair.inlCLM (lp.single p (-j) 1))) =
        -(if n = m then 1 else 0) := by
  dsimp only
  obtain ⟨X,Y,hder,hbracket⟩ := D.lemma15_3 φ
  have hs := (X n).summable_norm (Y m)
  have heq := (X n).bivector_eq_tsum (Y m)
  rw [(hder n).1,(hder m).2] at hs heq
  exact ⟨hs,heq.symm.trans (hbracket n m).2.1⟩

/-- Above exponent two these identities are precisely the existing
source brackets of the coordinate functions of the sequence map. -/
theorem sourceBracket_canonical
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (n m : ℤ) (φ : realTypeSourceSubmodule p) :
    sourceBracket h2p (fun ψ => (sourceBirkhoffMap hp hp1 s ψ).1 n)
      (fun ψ => (sourceBirkhoffMap hp hp1 s ψ).1 m) φ.val = 0 ∧
    sourceBracket h2p (fun ψ => (sourceBirkhoffMap hp hp1 s ψ).1 n)
      (fun ψ => (sourceBirkhoffMap hp hp1 s ψ).2 m) φ.val = -(if n = m then 1 else 0) ∧
    sourceBracket h2p (fun ψ => (sourceBirkhoffMap hp hp1 s ψ).2 n)
      (fun ψ => (sourceBirkhoffMap hp hp1 s ψ).2 m) φ.val = 0 := by
  obtain ⟨X,Y,hder,hbracket⟩ := D.lemma15_3 φ
  have heq (L M : RegularSourceCotangent p) :
      L.bivector M = sourceBivector h2p L.toCotangent M.toCotangent :=
    RegularSourceCotangent.bivector_congr (L' := RegularSourceCotangent.ofCotangent h2p L.toCotangent)
      (M' := RegularSourceCotangent.ofCotangent h2p M.toCotangent) rfl rfl
  have h := hbracket n m
  rw [heq,heq,heq,(hder n).1,(hder m).1,(hder n).2,(hder m).2] at h
  exact h

end SourceBirkhoffMapComplexData

/-- The constructed real analytic Birkhoff map and its complex extension
satisfy Lemma 15.3 for every real source, with no supplied bracket premises. -/
theorem exists_sourceBirkhoffMap_theorem15_2_lemma15_3 (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ B W : Set (CoeffPair p), ∃ s : (k : ℤ) → CoeffPair p → DeletedCoeff p k,
      SourceBirkhoffMapComplexData hp hp1 W₀ B W s ∧
      AnalyticOnNhd ℝ (sourceRealBirkhoffMap hp hp1 s) univ ∧
      ∀ φ : realTypeSourceSubmodule p, ∃ X Y : ℤ → RegularSourceCotangent p,
        (∀ n, (X n).toCotangent = fderiv ℂ (fun ψ => (sourceBirkhoffMap hp hp1 s ψ).1 n) φ.val ∧
          (Y n).toCotangent = fderiv ℂ (fun ψ => (sourceBirkhoffMap hp hp1 s ψ).2 n) φ.val) ∧
        ∀ n m, (X n).bivector (X m) = 0 ∧
          (X n).bivector (Y m) = -(if n = m then 1 else 0) ∧ (Y n).bivector (Y m) = 0 := by
  obtain ⟨W₀,B,W,s,D⟩ := exists_sourceBirkhoffMap_complex_analytic hp hp1
  exact ⟨W₀,B,W,s,D,D.real_map_analytic,D.lemma15_3⟩

end NLS.ZakharovShabat
