import NLS.Articles.KdVPseudomeasures.PeriodicFreeModeLowerBound
import NLS.Articles.KdVPseudomeasures.PeriodicEigenResidual
import NLS.Articles.KdVPseudomeasures.PeriodicSpectralRegularity
import NLS.KdV.HillEndpointEtaBound

/-! Full source Lemma 2.13: actual canonical eta/gamma identity AND its
quantitative bound with constant 16 on original endpoint norm balls. -/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- The source constant SIXTEEN holds for EVERY normalized native pair
satisfying the actual canonical eta equation, hence for ANY source orthonormal
spectral basis, including coincident roots and associated vectors. ONE cutoff
precedes the entire original complex endpoint norm ball. -/
theorem exists_uniform_sourcePeriodicEta_bound (r : ℝ) (hr : AdmissiblePredualOrder r)
    (R : ℝ) (Nmin : ℕ) :
    ∃ N : ℕ, 2 ≤ N ∧ Nmin ≤ N ∧ ∀ q : FourierLebesgueSpace (2:ℝ) (-r) ⊤, ‖q‖ ≤ R →
      ∀ n : ℕ+, N ≤ (n:ℕ) → ∀ f phi : FourierLebesgueSpace (2:ℝ) 1 2,
        ‖singularHillL2DomainInclusion f‖=1 → ‖singularHillL2DomainInclusion phi‖=1 →
        singularHillOperator (sourceComplexHminusOne r hr q) f=
          sourceHillComplexLabels r hr q (2*(n:ℕ)) • singularHillDomainInclusion f →
        ∀ eta : ℂ,
          singularHillOperator (sourceComplexHminusOne r hr q) phi-
              sourceHillComplexLabels r hr q (2*(n:ℕ)) • singularHillDomainInclusion phi =
            -(sourceHillComplexLabels r hr q (2*(n:ℕ))-sourceHillComplexLabels r hr q (2*(n:ℕ)-1)) •
                singularHillDomainInclusion phi+eta • singularHillDomainInclusion f →
          ‖eta‖ ≤ 16*(‖sourceHillComplexLabels r hr q (2*(n:ℕ))-sourceHillComplexLabels r hr q (2*(n:ℕ)-1)‖+
            ‖endpointUpperCoupling r hr.1 hr.2 (n:ℕ) (sourceEndpointCoefficients r q,sourceHillComplexLabels r hr q (2*(n:ℕ)))‖+
            ‖endpointLowerCoupling r hr.1 hr.2 (n:ℕ) (sourceEndpointCoefficients r q,sourceHillComplexLabels r hr q (2*(n:ℕ)))‖) := by
  obtain ⟨NF,hNF,hmin,hfree⟩ := exists_uniform_sourcePeriodicRange_freeMode_lower r hr R Nmin
  obtain ⟨NL,_,hlabels⟩ := source_uniform_canonical_complex_labels r hr R
  obtain ⟨NK,_,hcut⟩ := exists_endpointHill_cutoff r hr.2 (8*R)
  let N := max NF (max NL NK)
  refine ⟨N,by dsimp [N];omega,by dsimp [N];omega,?_⟩
  intro q hq n hn f phi hfn hpn hf eta heta
  have hnF : NF ≤ (n:ℕ) := by dsimp [N] at hn;omega
  have hnL : NL ≤ (n:ℕ) := by dsimp [N] at hn;omega
  have hnK : NK ≤ (n:ℕ) := by dsimp [N] at hn;omega
  obtain ⟨pair,_,hu⟩ := (hlabels q hq).high_pair (n:ℕ) hnL
  have hz : sourceHillComplexLabels r hr q (2*(n:ℕ)) ∈ reducedHillStrip (n:ℕ) := by
    rw [hu]
    exact pair.right_mem
  have hqscaled := mul_le_mul_of_nonneg_left hq
    (show 0 ≤ endpointHillConstant r*(n:ℝ)^(r-1/2) by positivity [endpointHillConstant_pos r hr.2])
  have hcutn := hcut (n:ℕ) hnK
  have hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖sourceEndpointCoefficients r q‖ ≤ 1/16 := by
    rw [norm_sourceEndpointCoefficients]
    nlinarith
  have hF := sourcePeriodicEigenvector_mem_range r hr q n pair _ hz f hf
  have hlower := hfree q hq n hnF _ hF
  exact norm_endpointEta_le_sixteen r hr.1 hr.2 (n:ℕ) n.property _ hz (sourceEndpointCoefficients r q) hs f phi hfn hpn
    (by rwa [sourceEndpointCoefficients_HminusOne_complex r hr q]) hlower _ eta
    (by rwa [sourceEndpointCoefficients_HminusOne_complex r hr q])

/-- Source Lemma 2.13, with the ACTUAL canonical labels, the ACTUAL full
physical spectral range and an ACTUAL normalized orthonormal basis. BOTH
basis vectors have IDENTICAL original F-ell^(s+2,infinity) distributions.
The eta equation AND original constant-16 bound are proved together, with
ONE original endpoint norm-ball cutoff above ANY supplied prior cutoff. -/
theorem sourceLemma2_13 (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) (Nmin : ℕ) :
    ∃ N : ℕ, 2 ≤ N ∧ Nmin ≤ N ∧ ∀ q : FourierLebesgueSpace (2:ℝ) (-r) ⊤, ‖q‖ ≤ R →
      ∀ n : ℕ+, N ≤ (n:ℕ) →
        ∃ f phi : FourierLebesgueSpace (2:ℝ) 1 2, ∃ eta : ℂ,
          singularHillOperator (sourceComplexHminusOne r hr q) f=
            sourceHillComplexLabels r hr q (2*(n:ℕ)) • singularHillDomainInclusion f ∧
          ‖singularHillL2DomainInclusion f‖=1 ∧ ‖singularHillL2DomainInclusion phi‖=1 ∧
          (∃ b : OrthonormalBasis (Fin 2) ℂ (singularHillL2RieszProjection
              (sourceComplexHminusOne r hr q) (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)).range,
            (b 0).val=singularHillL2DomainInclusion f ∧ (b 1).val=singularHillL2DomainInclusion phi) ∧
          (∃ u v : FourierLebesgueSpace (2:ℝ) (-r+2) ⊤, u.val=f.val ∧ v.val=phi.val) ∧
          singularHillOperator (sourceComplexHminusOne r hr q) phi-
              sourceHillComplexLabels r hr q (2*(n:ℕ)) • singularHillDomainInclusion phi =
            -(sourceHillComplexLabels r hr q (2*(n:ℕ))-sourceHillComplexLabels r hr q (2*(n:ℕ)-1)) •
              singularHillDomainInclusion phi+eta • singularHillDomainInclusion f ∧
          ‖eta‖ ≤ 16*(‖sourceHillComplexLabels r hr q (2*(n:ℕ))-sourceHillComplexLabels r hr q (2*(n:ℕ)-1)‖+
            ‖endpointUpperCoupling r hr.1 hr.2 (n:ℕ) (sourceEndpointCoefficients r q,sourceHillComplexLabels r hr q (2*(n:ℕ)))‖+
            ‖endpointLowerCoupling r hr.1 hr.2 (n:ℕ) (sourceEndpointCoefficients r q,sourceHillComplexLabels r hr q (2*(n:ℕ)))‖) := by
  obtain ⟨NI,_,hidentity⟩ := exists_uniform_sourcePeriodicEigenResidual r hr R
  obtain ⟨NC,_,hcircles⟩ := exists_uniform_sourcePeriodicCircle_rank_two r hr R
  obtain ⟨N,hN,hmin,hbound⟩ := exists_uniform_sourcePeriodicEta_bound r hr R (max Nmin (max NI NC))
  refine ⟨N,hN,by omega,?_⟩
  intro q hq n hn
  have hnI : NI ≤ (n:ℕ) := by omega
  have hnC : NC ≤ (n:ℕ) := by omega
  obtain ⟨f,phi,eta,hf,hfn,hpn,hbasis,heta⟩ := hidentity q hq n hnI
  have hetaBound := hbound q hq n hn f phi hfn hpn hf eta heta
  obtain ⟨b,hb0,hb1⟩ := hbasis
  have hc := (hcircles q hq n hnC).1
  have hpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast n.property
  obtain ⟨u,hu⟩ := sourcePeriodicH1Vector_regular r hr q _ _ hpos hc f
    (by rw [← hb0];exact (b 0).property)
  obtain ⟨v,hv⟩ := sourcePeriodicH1Vector_regular r hr q _ _ hpos hc phi
    (by rw [← hb1];exact (b 1).property)
  exact ⟨f,phi,eta,hf,hfn,hpn,⟨b,hb0,hb1⟩,⟨u,v,hu,hv⟩,heta,hetaBound⟩

end NLS.Articles.KdVPseudomeasures
