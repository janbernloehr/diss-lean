import NLS.ZakharovShabat.SourceDirichletDiscriminantKernel
import NLS.ZakharovShabat.SourceAngularThetaRealCotangent
import NLS.ZakharovShabat.SourceAngularThetaThetaDiscriminantStationarity
import NLS.ZakharovShabat.SourceRealTypeProjection
import NLS.ZakharovShabat.SourceCanonicalRootGapIsolation

/-! # Actual indexed Dirichlet spectral vector fields

At each source, evaluate the actual fixed-parameter discriminant
cotangent at its own moving Dirichlet coordinate, then apply the actual
source Poisson operator. This gives an isospectral vector field, real
on the real source form and analytic near every real source. The filled
kernel shows that only its own Dirichlet terminal data move. The actual
angle/angle bracket is stationary in every such direction.
-/

noncomputable section
open Set Complex Filter Topology NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The discriminant source cotangent is taken with its spectral argument
fixed, then evaluated at the actual moving indexed Dirichlet root. -/
def sourceDirichletSpectralVector
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (n : ℤ) (φ : CoeffPair p) : CoeffPair p :=
  sourceHamiltonianDirection h2p (sourceDiscriminantCotangent hp
    (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n) φ)

/-- The indexed field is isospectral at every complex source. -/
theorem sourceDirichletSpectralVector_isospectral
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (n : ℤ) (φ : CoeffPair p) :
    SourceIsospectralDirection hp φ (sourceDirichletSpectralVector hp hp1 h2p n φ) :=
  sourceHamiltonianVector_discriminant_isospectral hp hp1 h2p φ
    (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n)

/-- The actual indexed field is analytic near each real source. -/
theorem analyticAt_sourceDirichletSpectralVector_of_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (n : ℤ) (φ : realTypeSourceLocus p) :
    AnalyticAt ℂ (sourceDirichletSpectralVector hp hp1 h2p n) φ.val := by
  exact ((sourceHamiltonianDirection h2p).analyticAt _).comp
    ((analyticOnNhd_sourceDiscriminantCotangent_joint hp hp1
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val n,φ.val) (mem_univ _)).comp
      (f := fun ψ : CoeffPair p => (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n,ψ))
      ((analyticAt_canonicalPeriodOneBoundaryRoots_of_realType hp hp1 .dirichlet φ.val φ.property n).prod
        analyticAt_id))

/-- Reality of the actual discriminant cotangent makes the field real type. -/
theorem sourceDirichletSpectralVector_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (n : ℤ) (φ : realTypeSourceLocus p) :
    IsRealType (CoeffPair.toMax p (sourceDirichletSpectralVector hp hp1 h2p n φ.val)) := by
  let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val n
  have hμ : (μ.re:ℂ) = μ := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im,μ] using
        (canonicalPeriodOneBoundaryRoots_im_eq_zero hp hp1 .dirichlet φ.val φ.property n).symm
  change IsRealType (CoeffPair.toMax p (sourceHamiltonianDirection h2p (sourceDiscriminantCotangent hp μ φ.val)))
  rw [← hμ]
  exact (isSourceRealCotangent_sourceDiscriminantCotangent hp hp1 φ μ.re).hamiltonianDirection_realType h2p

/-- Exactly the selected Dirichlet root moves under the actual indexed
field; its velocity is minus half its full terminal anti-discriminant. -/
theorem fderiv_dirichletRoot_sourceDirichletSpectralVector
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (n m : ℤ) (φ : realTypeSourceLocus p) :
    (fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) φ.val)
      (sourceDirichletSpectralVector hp hp1 h2p n φ.val) =
      if m = n then -sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m φ.val/2 else 0 := by
  classical
  have he := sourceBracket_dirichletRoot_discriminant_eq_kernel hp hp1 h2p m φ.val φ.property
    (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val n)
  rw [← fderiv_apply_sourceHamiltonianVector] at he
  change (fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) φ.val)
    (sourceDirichletSpectralVector hp hp1 h2p n φ.val) = _ at he
  by_cases hmn : m = n
  · subst m
    rw [if_pos rfl,he,sourceDirichletDiscriminantKernel_at_root hp hp1 n φ.val φ.property]
    ring
  · rw [if_neg hmn,he,sourceDirichletDiscriminantKernel_at_other_root hp hp1 φ m n hmn,mul_zero]

/-- All other moving terminal anti-discriminants are fixed as well;
the selected one has the actual spectral-curve velocity at every terminal. -/
theorem fderiv_dirichletTerminalAnti_sourceDirichletSpectralVector
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (n m : ℤ) (φ : realTypeSourceLocus p) :
    (fderiv ℂ (sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m) φ.val)
      (sourceDirichletSpectralVector hp hp1 h2p n φ.val) =
      if m = n then
        let μ := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m;
        -canonicalDiscriminant hp (periodOnePotential φ.val) μ*
          deriv (canonicalDiscriminant hp (periodOnePotential φ.val)) μ/2
      else 0 := by
  classical
  have he := sourceBracket_dirichletTerminalAnti_discriminant_eq_kernel hp hp1 h2p m φ.val φ.property
    (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val n)
  dsimp only at he
  rw [← fderiv_apply_sourceHamiltonianVector] at he
  change (fderiv ℂ (sourceBoundaryTerminalAntiDiscriminant hp hp1 .dirichlet m) φ.val)
    (sourceDirichletSpectralVector hp hp1 h2p n φ.val) = _ at he
  by_cases hmn : m = n
  · subst m
    rw [if_pos rfl,he,sourceDirichletDiscriminantKernel_at_root hp hp1 n φ.val φ.property]
    ring
  · rw [if_neg hmn,he,sourceDirichletDiscriminantKernel_at_other_root hp hp1 φ m n hmn,mul_zero]

/-- The same actual field with the complete real-type Banach subspace
as both domain and codomain. The projection fixes its actual values. -/
def sourceRealDirichletSpectralVector
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p) (n : ℤ) :
    realTypeSourceSubmodule p → realTypeSourceSubmodule p := fun φ =>
  sourceRealTypeProjection hp (sourceDirichletSpectralVector hp hp1 h2p n φ.val)

@[simp] theorem sourceRealDirichletSpectralVector_val
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (n : ℤ) (φ : realTypeSourceSubmodule p) :
    (sourceRealDirichletSpectralVector hp hp1 h2p n φ : CoeffPair p) =
      sourceDirichletSpectralVector hp hp1 h2p n φ.val :=
  sourceRealTypeProjection_val_of_realType hp _
    (sourceDirichletSpectralVector_realType hp hp1 h2p n ⟨φ.val,φ.property⟩)

/-- The actual real indexed field is continuously differentiable everywhere. -/
theorem contDiff_sourceRealDirichletSpectralVector
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p) (n : ℤ) :
    ContDiff ℝ 1 (sourceRealDirichletSpectralVector hp hp1 h2p n) := by
  apply contDiff_iff_contDiffAt.mpr
  intro φ
  have hX : ContDiffAt ℝ 1 (sourceDirichletSpectralVector hp hp1 h2p n) φ.val :=
    (analyticAt_sourceDirichletSpectralVector_of_realType hp hp1 h2p n ⟨φ.val,φ.property⟩).contDiffAt.restrict_scalars ℝ
  exact (sourceRealTypeProjection hp).contDiff.contDiffAt.comp φ
    (hX.comp φ (realTypeSourceSubmodule p).subtypeL.contDiff.contDiffAt)

/-- The actual normalized numerator never vanishes at its own Dirichlet
terminal: all retained roots lie in disjoint other periodic gaps. -/
theorem SourcePsiIsolatingComplexExtension.numerator_at_own_dirichletRoot_ne_zero
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ : Set (CoeffPair p)}
    {s : (j : ℤ) → CoeffPair p → DeletedCoeff p j}
    (hs : SourcePsiIsolatingComplexExtension hp hp1 W₀ s)
    (n : ℤ) (φ : realTypeSourceLocus p) :
    sourcePsiCandidate n (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val n,
      (s n φ.val : Coeff p)) ≠ 0 := by
  intro hz
  obtain ⟨j,hjn,hj⟩ := (sourcePsiCandidate_eq_zero_iff_retained_root hp hp1 n _ _).mp hz
  rw [hs.real_agreement n φ] at hj
  have hσ := sourcePsiGapRoot_mem_periodicSegment hp hp1 n j hjn φ
  rw [hj] at hσ
  have hμ := canonicalPeriodOneBoundaryRoots_mem_sourcePeriodicSegment_of_realType hp hp1
    .dirichlet φ.val φ.property n
  obtain ⟨A,_,_,hreal,hdisjoint⟩ := exists_global_source_disjoint_periodicSegments hp hp1
  exact Set.disjoint_left.mp (hdisjoint φ.val (hreal φ.property) j n hjn) hσ hμ

namespace SourceAngularThetaCommonDomainData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (j : ℤ) → CoeffPair p → DeletedCoeff p j}

/-- Every actual angle cotangent has its proved normalized numerator
velocity under each actual indexed spectral field. -/
theorem thetaDifferential_sourceDirichletSpectralVector
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (n m : ℤ) (φ : realTypeSourceLocus p)
    (hm : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m ≠ 0) :
    (sourceAngularThetaDifferential hp hp1 m s φ.val)
      (sourceDirichletSpectralVector hp hp1 h2p n φ.val) =
      -sourcePsiCandidate m (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val n,
        (s m φ.val : Coeff p))/2 := by
  rw [sourceDirichletSpectralVector,apply_sourceHamiltonianDirection]
  exact D.thetaDiscriminant_eq h2p m φ hm _

/-- Each actual indexed spectral field fixes the actual angle/angle
bracket wherever both selected angle gaps are open. -/
theorem fderiv_thetaTheta_sourceDirichletSpectralVector_eq_zero
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (k n m : ℤ) (φ : realTypeSourceLocus p)
    (hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (hm : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m ≠ 0) :
    (fderiv ℂ (sourceAngularThetaThetaBracket hp hp1 h2p n m s) φ.val)
      (sourceDirichletSpectralVector hp hp1 h2p k φ.val) = 0 := by
  rw [sourceDirichletSpectralVector,apply_sourceHamiltonianDirection]
  exact D.thetaThetaDiscriminant_eq_zero h2p n m φ hn hm _

/-- An indexed spectral vector is nonzero whenever its own selected
angle gap is open. Thus its constructed integral curve is nonstationary
at the initial source used for angle transport. -/
theorem sourceDirichletSpectralVector_ne_zero_of_open_gap
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (n : ℤ) (φ : realTypeSourceLocus p)
    (hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0) :
    sourceDirichletSpectralVector hp hp1 h2p n φ.val ≠ 0 := by
  intro hx
  have he := D.thetaDifferential_sourceDirichletSpectralVector h2p n n φ hn
  rw [hx,map_zero] at he
  apply D.psi.toSourcePsiIsolatingComplexExtension.numerator_at_own_dirichletRoot_ne_zero n φ
  linear_combination 2*he

end SourceAngularThetaCommonDomainData
end NLS.ZakharovShabat
