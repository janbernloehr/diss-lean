import NLS.Articles.KdVPseudomeasures.OriginalDirichletUniformSimplicity
import NLS.KdV.SingularDirichletRieszL2

/-! The original Section 2.5 Dirichlet projection, with the LITERAL source
circle |z-n^2*pi^2|=n, full original distribution and ordinary interval L2.
Circle validity/isolation and quantitative C.4 estimates remain explicit
conditions; the projection and all operator identities are actual constructions. -/
noncomputable section
open Set Metric
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.Fourier NLS.ZakharovShabat

/-- The source's actual Dirichlet projection Pi_(n,q), on ordinary physical L2. -/
def originalDirichletRieszProjection (q : OriginalComplexHminusOnePotential) (n : ℕ+) :
    IntervalL2 →L[ℂ] IntervalL2 :=
  singularDirichletL2RieszProjection q.val (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)

/-- The IDENTICAL source contour projection on the full original native dual. -/
def originalDirichletBaseRieszProjection (q : OriginalComplexHminusOnePotential) (n : ℕ+) :
    UnitDirichletHminus →L[ℂ] UnitDirichletHminus :=
  singularDirichletRieszProjection q.val (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)

/-- On its actual source resolvent circle, Pi_(n,q) is a genuine bounded
idempotent in the ordinary physical L2 operator norm. -/
theorem isIdempotentElem_originalDirichletRieszProjection
    (q : OriginalComplexHminusOnePotential) (n : ℕ+)
    (hc : sphere (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ) ⊆ singularDirichletResolventSet q.val) :
    IsIdempotentElem (originalDirichletRieszProjection q n) :=
  isIdempotentElem_singularDirichletL2RieszProjection q.val _ _
    (by exact_mod_cast n.property) hc

/-- For an actual simple isolated original label, the source projection has
EXACTLY its normalized native eigenfunction line as its full physical L2 range. -/
theorem exists_originalDirichletRiesz_normalized_generator
    (q : OriginalComplexHminusOnePotential) (n : ℕ+)
    (hc : sphere (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ) ⊆ singularDirichletResolventSet q.val)
    (hl : originalComplexDirichletLabels q n ∈ ball (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ))
    (honly : ∀ z ∈ ball (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ),
      z ∈ singularDirichletSpectrum q.val → z = originalComplexDirichletLabels q n)
    (hm : singularDirichletAlgebraicMultiplicity q.val (originalComplexDirichletLabels q n) = 1) :
    ∃ g : UnitDirichletH1,
      singularDirichletOperator q.val g =
        originalComplexDirichletLabels q n • singularDirichletDomainInclusion g ∧
      ‖unitDirichletL2Inclusion g‖ = 1 ∧
      (∫ x in (0:ℝ)..1, ‖unitDirichletRepresentative g x‖^2) = 1 ∧
      (originalDirichletRieszProjection q n).range =
        Submodule.span ℂ {unitDirichletL2Inclusion g} := by
  obtain ⟨g,hg,hn,hi⟩ := exists_normalized_originalComplexDirichlet_eigenfunction q n
  have hg0 : g ≠ 0 := by
    intro he
    rw [he,map_zero,norm_zero] at hn
    norm_num at hn
  exact ⟨g,hg,hn,hi,singularDirichletL2RieszProjection_range_eq_span q.val _ _
    (by exact_mod_cast n.property) hc _ hl honly hm g hg0 hg⟩

/-- The source scalar amplitude is the ACTUAL physical L2 projection
coefficient. Commutation with the full native expression gives its exact
projected residual factor nu*(mu_n-lambda), the operator step in (31).
The source overlap lower bound (32) is not assumed or claimed here. -/
theorem exists_originalDirichletRiesz_projected_residual_amplitude
    (q : OriginalComplexHminusOnePotential) (n : ℕ+)
    (hc : sphere (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ) ⊆ singularDirichletResolventSet q.val)
    (hl : originalComplexDirichletLabels q n ∈ ball (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ))
    (honly : ∀ z ∈ ball (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ),
      z ∈ singularDirichletSpectrum q.val → z = originalComplexDirichletLabels q n)
    (hm : singularDirichletAlgebraicMultiplicity q.val (originalComplexDirichletLabels q n) = 1)
    (g : UnitDirichletH1)
    (hg : singularDirichletOperator q.val g =
      originalComplexDirichletLabels q n • singularDirichletDomainInclusion g)
    (hn : ‖unitDirichletL2Inclusion g‖ = 1) (G : UnitDirichletH1) (lambda : ℂ) :
    ∃ nu : ℂ,
      originalDirichletRieszProjection q n (unitDirichletL2Inclusion G) = nu • unitDirichletL2Inclusion g ∧
      originalDirichletBaseRieszProjection q n
        (singularDirichletOperator q.val G-lambda • singularDirichletDomainInclusion G) =
          (nu*(originalComplexDirichletLabels q n-lambda)) • singularDirichletDomainInclusion g ∧
      ‖nu‖ ≤ ‖originalDirichletRieszProjection q n‖*‖unitDirichletL2Inclusion G‖ := by
  have hr : (0:ℝ) < (n:ℝ) := by exact_mod_cast n.property
  obtain ⟨nu,hnu,hbound⟩ := exists_singularDirichletL2Riesz_amplitude_bound q.val _ _ hr hc
    _ hl honly hm g hg hn (unitDirichletL2Inclusion G)
  have hproj : singularDirichletDomainRieszProjection q.val (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ) G = nu • g := by
    apply unitDirichletL2Inclusion_injective
    rw [← singularDirichletL2RieszProjection_domain,map_smul]
    exact hnu
  exact ⟨nu,hnu,singularDirichletRiesz_projected_residual q.val _ _ hr.le hc
    lambda (originalComplexDirichletLabels q n) nu G g hg hproj,hbound⟩

end NLS.Articles.KdVPseudomeasures
