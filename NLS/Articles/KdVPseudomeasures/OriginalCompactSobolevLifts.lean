import NLS.Articles.KdVPseudomeasures.OriginalIsospectralMiura
import NLS.Articles.KdVPseudomeasures.OriginalMiuraGapComparison
import NLS.KdV.HminusOneMiuraSobolevCompactness

/-!
# Compact stronger Miura lifts covering the entire original isospectral set

A single actual original gap hypothesis supplies a compact stronger Sobolev
realization of all real lifts in one Dirac isospectral set. That family covers
every original H-minus-one isospectral potential at one common physical shift.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Original gaps at order -a give a compact lift cover at every order
1-b with a<b≤1. Both the original isospectral set and the entire original
Miura distribution are retained, with one common shift for all members. -/
theorem exists_originalIsospectral_compact_sobolev_lift_cover
    (q : OriginalHminusOnePotential) (hp : p ≠ ⊤) (hp2 : 2 ≤ p)
    (a b : ℝ) (hab : a < b) (hb : b ≤ 1)
    (hgap : Memℓp (fun n : ℤ => (Weight.sobolev (-a) n:ℂ)*originalCanonicalGapValues q n) p) :
    ∃ c : ℝ, 0 < c ∧ ∃ u₀ : PeriodOneRealL2,
      let K := hillMiuraRealSource ⁻¹'
        sourceIsospectralSet (by norm_num) (hillMiuraRealSource u₀)
      ∃ F : K → Coeff p, Continuous F ∧
        (∀ v n, F v n = (Weight.sobolev (1-b) n:ℂ)*v.val.val n) ∧
        IsCompact (range F) ∧
        ∀ v ∈ originalIsospectralSet q, ∃ u : K,
          periodOneMiura u.val.val = originalPeriodOneCoefficients v+
            periodOneL2Inclusion (lp.single 2 0 ((c:ℂ)^2)) := by
  obtain ⟨c,hc,_,u₀,hu₀,_,_,hlift⟩ :=
    exists_originalIsospectral_lifts_in_one_dirac_isospectral_set q 0
  have himage : periodOneMiura u₀.val = originalPeriodOneCoefficients q+
      periodOneL2Inclusion (lp.single 2 0 ((c^2:ℝ):ℂ)) := by
    simpa only [ofReal_pow] using hu₀
  have hD := memlp_miuraDiracGap_of_original_gap q u₀ (c^2) (-a) himage hgap
  have hD' : Memℓp (fun n : ℤ => (Weight.sobolev (1-a) n:ℂ)*
      (hillMiuraDiracRight u₀.val n-hillMiuraDiracLeft u₀.val n)) p := by
    simpa only [show -a+1 = 1-a by ring] using hD
  obtain ⟨F,hF,hFc,hcompact⟩ := exists_compact_sobolev_miura_isospectral_lifts hp hp2 u₀
    (1-a) (1-b) (by linarith only [hb]) (by linarith only [hab]) hD'
  refine ⟨c,hc,u₀,F,hF,hFc,hcompact,?_⟩
  intro v hv
  obtain ⟨u,_,himage,hiso⟩ := hlift v hv
  exact ⟨⟨u,hiso⟩,himage⟩

end NLS.Articles.KdVPseudomeasures
