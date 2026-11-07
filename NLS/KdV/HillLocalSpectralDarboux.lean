import NLS.KdV.HillNormingGardnerCommutation
import NLS.KdV.HillLocalLogNormingGardner

/-! The full local separated spectral Gardner matrix, including all
closed periodic gaps. These are the actual Dirichlet energies and
locally normalized logarithms of their actual multipliers, not the
article's Abelian angles or signed Birkhoff coordinates. -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.KdV

theorem hillHminus_localLogNormings_Gardner_commute (n m : ℕ+) (a b q : PeriodOneHminusOne)
    (ha : a ∈ hillHminusCanonicalDirichletDomain) (hb : b ∈ hillHminusCanonicalDirichletDomain)
    (hq : q ∈ hillHminusCanonicalDirichletDomain)
    (hn : hillHminusDirichletNorming n q/hillHminusDirichletNorming n a ∈ slitPlane)
    (hm : hillHminusDirichletNorming m q/hillHminusDirichletNorming m b ∈ slitPlane) :
    NLS.Poisson.hminusGardnerBracket (hillHminusLocalLogNorming n a) (hillHminusLocalLogNorming m b) q=0 := by
  change NLS.Poisson.gardnerCotangentBivector (fderiv ℂ (hillHminusLocalLogNorming n a) q)
    (fderiv ℂ (hillHminusLocalLogNorming m b) q)=0
  rw [fderiv_hillHminusLocalLogNorming n a q ha hq hn,fderiv_hillHminusLocalLogNorming m b q hb hq hm]
  have hz : NLS.Poisson.gardnerCotangentBivector (fderiv ℂ (hillHminusDirichletNorming n) q)
      (fderiv ℂ (hillHminusDirichletNorming m) q)=0 := hillHminusNormings_Gardner_commute n m q hq
  simp only [map_smul,smul_apply,hz,smul_zero]

theorem hillHminus_local_spectral_Gardner_matrix (n m : ℕ+) (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusCanonicalDirichletDomain) :
    NLS.Poisson.hminusGardnerBracket (hillHminusCanonicalDirichlet n) (hillHminusCanonicalDirichlet m) q=0 ∧
      NLS.Poisson.hminusGardnerBracket (hillHminusCanonicalDirichlet n) (hillHminusLocalLogNorming m q) q=
        (if n=m then 1 else 0) ∧
      NLS.Poisson.hminusGardnerBracket (hillHminusLocalLogNorming n q) (hillHminusLocalLogNorming m q) q=0 := by
  refine ⟨hillHminusCanonicalDirichlets_Gardner_commute n m q hq,
    hillHminus_Dirichlet_localLogNorming_Gardner_at_base n m q hq,?_⟩
  apply hillHminus_localLogNormings_Gardner_commute n m q q q hq hq hq
  · simp [hillHminusDirichletNorming_ne_zero n q hq]
  · simp [hillHminusDirichletNorming_ne_zero m q hq]

end NLS.KdV
