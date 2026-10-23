import NLS.ZakharovShabat.SourceAngularEtaRemainderSpectralData
import NLS.ZakharovShabat.SourceBirkhoffCoordinateExponent
import NLS.ZakharovShabat.SourceBirkhoffProposition17_2

/-! # Signed Dirichlet data determine a source within its actual isospectral set

The normalized eta remainder and beta correction recover the actual
rectangular Birkhoff coordinates. Global Birkhoff injectivity then proves
uniqueness of the real source from its periodic spectrum and signed
Dirichlet data at every finite exponent above one. No existence for
arbitrary prescribed signed data is asserted here.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace SourceAngularEtaLocalCommonDomainData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B V₀ C : Set (CoeffPair p)}
  {s t : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- Independent actual annular constructions give the same normalized
eta remainder at isospectral sources with equal selected root and sign. -/
theorem etaRemainder_eq_of_isospectral_root_sign
    (D : SourceAngularEtaLocalCommonDomainData hp hp1 W₀ B s)
    (E : SourceAngularEtaLocalCommonDomainData hp hp1 V₀ C t)
    (W V : Set (CoeffPair p)) (hW : IsOpen W) (hV : IsOpen V)
    (hWB : W ⊆ B) (hVC : V ⊆ C)
    (φ ψ : realTypeSourceSubmodule p) (h : ψ ∈ sourceIsospectralSet hp φ)
    (hψ : ψ.val ∈ W) (hφ : φ.val ∈ V) (n : ℤ)
    (hμ : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ.val n =
      canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val n)
    (hσ : sourceDirichletSign hp hp1 ψ n = sourceDirichletSign hp hp1 φ n) :
    sourceAngularEtaRemainder hp hp1 n s ψ.val = sourceAngularEtaRemainder hp hp1 n t φ.val := by
  obtain ⟨O,A,c,T,r,R,z₀,ρ,hψA,hrρ,hρR,H⟩ := D.exists_real_joint_annulus_chart W hW hWB ψ hψ n
  obtain ⟨O',A',c',T',r',R',z₀',ρ',hφA,hrρ',hρR',H'⟩ :=
    E.exists_real_joint_annulus_chart V hV hVC φ hφ n
  rw [H.etaRemainder_eq_cauchyCandidate ρ hrρ hρR ψ.val hψA,
    H'.etaRemainder_eq_cauchyCandidate ρ' hrρ' hρR' φ.val hφA]
  exact H.etaRemainderCauchyCandidate_isospectral H' φ ψ h hψA hφA
    (D.psi.toSourcePsiIsolatingComplexExtension.candidate_real_isospectral_agreement
      E.psi.toSourcePsiIsolatingComplexExtension φ ψ h n) hμ hσ ρ hrρ hρR ρ' hrρ' hρR'

end SourceAngularEtaLocalCommonDomainData

/-- On an open gap the action factorization identifies the principal
normalized action root at any two actual isospectral real sources. -/
theorem sourceNormalizedActionRoot_eq_of_isospectral_open_gap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ ψ : realTypeSourceSubmodule p)
    (h : ψ ∈ sourceIsospectralSet hp φ) (n : ℤ)
    (hg : sourcePeriodicGapDisplacement hp hp1 φ.val n ≠ 0) :
    sourceNormalizedActionRoot hp hp1 n ψ.val = sourceNormalizedActionRoot hp hp1 n φ.val := by
  have he := canonicalPeriodicEndpoints_eq_of_spectral_data hp hp1
    (periodOnePotential ψ.val) (periodOnePotential φ.val)
    (periodOnePotential_mem _) (periodOnePotential_mem _) h.1 h.2
  have hgap : sourcePeriodicGapDisplacement hp hp1 ψ.val n =
      sourcePeriodicGapDisplacement hp hp1 φ.val n := by
    simp only [sourcePeriodicGapDisplacement_apply,canonicalPeriodicGap,he.1,he.2]
  obtain ⟨U,_,hU,_,hF⟩ := exists_local_sourceNormalizedAction_analytic_factor hp hp1 ψ.val ψ.property n
  obtain ⟨V,_,hV,_,hG⟩ := exists_local_sourceNormalizedAction_analytic_factor hp hp1 φ.val φ.property n
  have hI : sourceComplexAction hp hp1 n ψ.val = sourceComplexAction hp hp1 n φ.val := by
    rw [sourceComplexAction_eq_sourceRealAction hp hp1 n ψ.val ψ.property,
      sourceComplexAction_eq_sourceRealAction hp hp1 n φ.val φ.property]
    exact sourceRealAction_eq_of_isospectral hp hp1 φ ψ h n
  rw [hF ψ.val hU,hG φ.val hV,hgap] at hI
  have hf := mul_left_cancel₀ (pow_ne_zero 2 hg) hI
  simp only [sourceNormalizedActionRoot,hf]

namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- Signed Dirichlet data identify every actual rectangular coordinate,
with closed gaps handled by their proved zero coordinates. -/
theorem birkhoffXY_eq_of_isospectral_roots_signs
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (φ ψ : realTypeSourceSubmodule p) (h : ψ ∈ sourceIsospectralSet hp φ)
    (hμ : ∀ m, canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ.val m =
      canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m)
    (hσ : ∀ m, sourceDirichletSign hp hp1 ψ m = sourceDirichletSign hp hp1 φ m) (n : ℤ) :
    sourceBirkhoffX hp hp1 n s ψ.val = sourceBirkhoffX hp hp1 n s φ.val ∧
      sourceBirkhoffY hp hp1 n s ψ.val = sourceBirkhoffY hp hp1 n s φ.val := by
  have he := canonicalPeriodicEndpoints_eq_of_spectral_data hp hp1
    (periodOnePotential ψ.val) (periodOnePotential φ.val)
    (periodOnePotential_mem _) (periodOnePotential_mem _) h.1 h.2
  have hgap : sourcePeriodicGapDisplacement hp hp1 ψ.val n =
      sourcePeriodicGapDisplacement hp hp1 φ.val n := by
    simp only [sourcePeriodicGapDisplacement_apply,canonicalPeriodicGap,he.1,he.2]
  by_cases hg : sourcePeriodicGapDisplacement hp hp1 φ.val n = 0
  · have hψ := D.real_closed_gap_zero ψ.val (D.real_subset ψ.property) ψ.property n (hgap.trans hg)
    have hφ := D.real_closed_gap_zero φ.val (D.real_subset φ.property) φ.property n hg
    rw [(D.coordinates ψ.val (D.real_subset ψ.property) n).1,
      (D.coordinates ψ.val (D.real_subset ψ.property) n).2] at hψ
    rw [(D.coordinates φ.val (D.real_subset φ.property) n).1,
      (D.coordinates φ.val (D.real_subset φ.property) n).2] at hφ
    exact ⟨hψ.1.trans hφ.1.symm,hψ.2.trans hφ.2.symm⟩
  · have hrem := D.angular.etaRemainder_eq_of_isospectral_root_sign D.angular W W
      D.source_open D.source_open D.source_subset D.source_subset φ ψ h
      (D.real_subset ψ.property) (D.real_subset φ.property) n (hμ n) (hσ n)
    have hβ := D.angular.psi.toSourcePsiIsolatingComplexExtension.betaCorrection_eq_of_isospectral_roots_signs
      D.angular.psi.toSourcePsiIsolatingComplexExtension φ ψ h n hμ hσ
    have ha := sourceDirichletTerminal_eq_of_isospectral_root_sign hp hp1 φ ψ h n (hμ n) (hσ n)
    have hsin : sourceDirichletEtaSineNumerator hp hp1 n ψ.val =
        sourceDirichletEtaSineNumerator hp hp1 n φ.val := by
      dsimp only [sourceDirichletEtaSineNumerator]
      rw [ha,sourceStandardRootOmittedProduct_eq_of_isospectral hp hp1 φ ψ h,hμ n]
    have hτ : canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ.val) (periodOnePotential_mem ψ.val) n =
        canonicalPeriodicMidpoint hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n := by
      simp only [canonicalPeriodicMidpoint,he.1,he.2]
    have hw (sign : ℂ) : sourceBirkhoffWeightedCoordinate hp hp1 n s sign ψ.val =
        sourceBirkhoffWeightedCoordinate hp hp1 n s sign φ.val := by
      simp only [sourceBirkhoffWeightedCoordinate,sourceGapWeightedEtaCoordinate,
        sourceNormalizedActionRoot_eq_of_isospectral_open_gap hp hp1 φ ψ h n hg,
        hrem,hβ,hμ,hsin,hτ]
    exact ⟨by simp only [sourceBirkhoffX,hw],by simp only [sourceBirkhoffY,hw]⟩

end SourceBirkhoffMapComplexData

/-- Equal actual periodic spectra, Dirichlet roots and signs determine the real source.
No finite-gap, Hilbert-regularity, or prescribed inverse-map premise is used. -/
theorem source_eq_of_isospectral_dirichlet_roots_signs
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ ψ : realTypeSourceSubmodule p)
    (h : ψ ∈ sourceIsospectralSet hp φ)
    (hμ : ∀ m, canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ.val m =
      canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m)
    (hσ : ∀ m, sourceDirichletSign hp hp1 ψ m = sourceDirichletSign hp hp1 φ m) : ψ = φ := by
  obtain ⟨W₀,B,W,s,D⟩ := exists_sourceBirkhoffMap_complex_analytic hp hp1
  apply D.proposition17_2
  have hc n := D.birkhoffXY_eq_of_isospectral_roots_signs φ ψ h hμ hσ n
  have hd n := D.coordinates ψ.val (D.real_subset ψ.property) n
  have he n := D.coordinates φ.val (D.real_subset φ.property) n
  apply Prod.ext <;> ext n
  · change ((sourceBirkhoffMap hp hp1 s ψ.val).1 n).re = _
    rw [(hd n).1]
    exact congrArg Complex.re ((hc n).1.trans (he n).1.symm)
  · change ((sourceBirkhoffMap hp hp1 s ψ.val).2 n).re = _
    rw [(hd n).2]
    exact congrArg Complex.re ((hc n).2.trans (he n).2.symm)

/-- The literal Dirichlet eigenvalues paired with their actual anti-discriminant signs. -/
def sourceSignedDirichletData (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) : ℤ → ℂ × SignType :=
  fun n => (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val n,sourceDirichletSign hp hp1 φ n)

/-- The actual signed Dirichlet data separate every pair of points in an isospectral set. -/
theorem sourceSignedDirichletData_injOn_isospectralSet
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p) :
    Set.InjOn (sourceSignedDirichletData hp hp1) (sourceIsospectralSet hp φ) := by
  intro ψ hψ χ hχ he
  have h : ψ ∈ sourceIsospectralSet hp χ :=
    ⟨hψ.1.trans hχ.1.symm,fun z => (hψ.2 z).trans (hχ.2 z).symm⟩
  exact source_eq_of_isospectral_dirichlet_roots_signs hp hp1 χ ψ h
    (fun n => congrArg Prod.fst (congrFun he n))
    (fun n => congrArg Prod.snd (congrFun he n))

end NLS.ZakharovShabat
