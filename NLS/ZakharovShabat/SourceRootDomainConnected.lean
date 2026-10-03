import NLS.ZakharovShabat.SourceRealBandCoverage

/-! # Connectedness of the real-source spectral cut complement

Each band strip joins both half-planes. The resulting connected
regions share the upper half-plane and exhaust the root domain.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The complement of all periodic cuts of a real source is connected,
including when some or all gaps have collapsed. -/
theorem isConnected_sourceCanonicalRootDomain_of_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) :
    IsConnected (sourceCanonicalRootDomain hp hp1 φ) := by
  let U := sourceAbelianHalfPlane true
  let L := sourceAbelianHalfPlane false
  let S := sourceRealBandStrip hp hp1 φ
  have hU : IsPreconnected U := (convex_sourceAbelianHalfPlane true).isPreconnected
  have hL : IsPreconnected L := (convex_sourceAbelianHalfPlane false).isPreconnected
  have hS (n : ℤ) : IsPreconnected (S n) := (convex_sourceRealBandStrip hp hp1 φ n).isPreconnected
  have hE (n : ℤ) : IsPreconnected ((U ∪ S n) ∪ L) := by
    obtain ⟨x,hx⟩ := exists_between (canonicalPeriodicRight_re_lt_next_left hp hp1
      (periodOnePotential φ) (periodOnePotential_mem φ) (isRealType_periodOnePotential φ hφ) n)
    have hxU : (x : ℂ)+I ∈ U := by simp [U,sourceAbelianHalfPlane]
    have hxS : (x : ℂ)+I ∈ S n := by simpa [S,sourceRealBandStrip,sourceRealBand] using hx
    have hxL : (x : ℂ)-I ∈ L := by simp [L,sourceAbelianHalfPlane]
    have hxS' : (x : ℂ)-I ∈ S n := by simpa [S,sourceRealBandStrip,sourceRealBand] using hx
    exact (hU.union _ hxU hxS (hS n)).union _ (Or.inr hxS') hxL hL
  have hI : I ∈ U := by simp [U,sourceAbelianHalfPlane]
  have he : (⋃ n : ℤ, (U ∪ S n) ∪ L) = sourceCanonicalRootDomain hp hp1 φ := by
    rw [sourceCanonicalRootDomain_eq_halfPlanes_union_bandStrips hp hp1 φ hφ]
    ext z
    simp only [mem_iUnion,mem_union,U,L,S]
    constructor
    · rintro ⟨n,(hu | hs) | hl⟩
      · exact Or.inl (Or.inl hu)
      · exact Or.inr ⟨n,hs⟩
      · exact Or.inl (Or.inr hl)
    · rintro ((hu | hl) | ⟨n,hs⟩)
      · exact ⟨0,Or.inl (Or.inl hu)⟩
      · exact ⟨0,Or.inr hl⟩
      · exact ⟨n,Or.inl (Or.inr hs)⟩
  rw [← he]
  exact ⟨⟨I,mem_iUnion.mpr ⟨0,Or.inl (Or.inl hI)⟩⟩,
    isPreconnected_iUnion ⟨I,mem_iInter.mpr (fun _ => Or.inl (Or.inl hI))⟩ hE⟩

end NLS.ZakharovShabat
