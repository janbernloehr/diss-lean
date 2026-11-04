import NLS.KdV.HillAnglePairGapZeroSequence
import NLS.KdV.HillPsiFrequencySourceVariation
import NLS.ZakharovShabat.SourceOddPsiVariationInterpolation

/-! The actual entire angle-pair discriminant variation vanishes.
Native Jacobi, actual odd numerator derivatives, a full odd gap-zero
sequence and verified interpolation uniqueness supply every premise.
The zero value of the angle/angle bracket itself remains separate. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.KdV.HillPhysicalOnIndexPhaseChart
variable {P Q : HillProductEquationPatch} {n m : ℕ+}

theorem completePhasePairFrequencyVariation_eq_root_variations
    (C : HillPhysicalOnIndexPhaseChart P n) (D : HillPhysicalOnIndexPhaseChart Q m)
    (q : PeriodOneHminusOne) (hqC : q ∈ C.source) (hqD : q ∈ D.source)
    (hr : IsRealPeriodOneHminusOne q) (z : ℂ) :
    let u := NLS.Poisson.gardnerHamiltonianVector C.completePhase q
    let v := NLS.Poisson.gardnerHamiltonianVector D.completePhase q
    4*C.completePhasePairFrequencyVariation D q z =
      (sourcePsiCandidateVariation ((n:ℕ):ℤ) (P.nativePsiRootMap n q:Coeff 2)
        (P.nativePsiRootDirection n q v:Coeff 2) z-
       sourcePsiCandidateVariation ((n:ℕ):ℤ) (P.nativePsiRootMap n q:Coeff 2)
        (P.nativePsiRootDirection n q v:Coeff 2) (-z))-
      (sourcePsiCandidateVariation ((m:ℕ):ℤ) (P.nativePsiRootMap m q:Coeff 2)
        (P.nativePsiRootDirection m q u:Coeff 2) z-
       sourcePsiCandidateVariation ((m:ℕ):ℤ) (P.nativePsiRootMap m q:Coeff 2)
        (P.nativePsiRootDirection m q u:Coeff 2) (-z)) := by
  let u := NLS.Poisson.gardnerHamiltonianVector C.completePhase q
  let v := NLS.Poisson.gardnerHamiltonianVector D.completePhase q
  obtain ⟨r,hrpos,_,_,hvar⟩ := C.exists_local_completePhasePair_discriminant_variation D q hqC hqD hr
  have he := hvar (z^2-(P.parent.parent.miuraBall.actionBall.shift:ℂ)) q (mem_ball_self hrpos)
  rw [NLS.Poisson.hminusGardnerBracket_antisymm C.completePhase,
    NLS.Poisson.hminusGardnerBracket_antisymm D.completePhase,
    ← NLS.Poisson.fderiv_apply_gardnerHamiltonianVector,
    ← NLS.Poisson.fderiv_apply_gardnerHamiltonianVector] at he
  have hn := P.fderiv_canonicalPsi_frequency_identity n q (C.subset hqC).1 v z
  have hm := P.fderiv_canonicalPsi_frequency_identity m q (C.subset hqC).1 u z
  dsimp only [completePhasePairFrequencyVariation,u,v] at hn hm ⊢
  linear_combination 2*z*he+hn-hm

theorem completePhasePairFrequencyVariation_eq_zero_of_real
    (C : HillPhysicalOnIndexPhaseChart P n) (D : HillPhysicalOnIndexPhaseChart Q m)
    (q : PeriodOneHminusOne) (hqC : q ∈ C.source) (hqD : q ∈ D.source)
    (hr : IsRealPeriodOneHminusOne q) : C.completePhasePairFrequencyVariation D q=0 := by
  obtain ⟨ρ,hρneg,hρ0,hρlp,hρ⟩ :=
    C.exists_completePhasePairFrequencyVariation_odd_gapZero_sequence D q hqC hqD hr
  let φ : realTypeSourceLocus 2 := ⟨P.sourcePsi q,P.sourcePsi_real q (C.subset hqC).1 hr⟩
  let u := NLS.Poisson.gardnerHamiltonianVector C.completePhase q
  let v := NLS.Poisson.gardnerHamiltonianVector D.completePhase q
  let hn := P.nativePsiRootDirection n q v
  let hm := P.nativePsiRootDirection m q u
  have hzero (j : ℤ) :
      (sourcePsiCandidateVariation ((n:ℕ):ℤ) (P.nativePsiRootMap n q:Coeff 2) (hn:Coeff 2) (ρ j)-
       sourcePsiCandidateVariation ((n:ℕ):ℤ) (P.nativePsiRootMap n q:Coeff 2) (hn:Coeff 2) (-ρ j))-
      (sourcePsiCandidateVariation ((m:ℕ):ℤ) (P.nativePsiRootMap m q:Coeff 2) (hm:Coeff 2) (ρ j)-
       sourcePsiCandidateVariation ((m:ℕ):ℤ) (P.nativePsiRootMap m q:Coeff 2) (hm:Coeff 2) (-ρ j))=0 := by
    have he := C.completePhasePairFrequencyVariation_eq_root_variations D q hqC hqD hr (ρ j)
    rw [(hρ j).2,mul_zero] at he
    exact he.symm
  have hall := source_oddPsiVariation_sub_eq_zero_of_balanced_gapZero_sequence (by norm_num) (by norm_num)
    φ ρ hρlp hρ0 hρneg (fun j => (hρ j).1) ((n:ℕ):ℤ) ((m:ℕ):ℤ)
    (P.nativePsiRootMap n q:Coeff 2) (hn:Coeff 2) (P.nativePsiRootMap m q:Coeff 2) (hm:Coeff 2)
    hn.property hm.property hzero
  funext z
  have he := C.completePhasePairFrequencyVariation_eq_root_variations D q hqC hqD hr z
  have he0 : 4*C.completePhasePairFrequencyVariation D q z=0 := he.trans (congrFun hall z)
  exact (mul_eq_zero.mp he0).resolve_left (by norm_num)

theorem completePhasePairDiscriminantBracket_eq_zero_of_real
    (C : HillPhysicalOnIndexPhaseChart P n) (D : HillPhysicalOnIndexPhaseChart Q m)
    (q : PeriodOneHminusOne) (hqC : q ∈ C.source) (hqD : q ∈ D.source)
    (hr : IsRealPeriodOneHminusOne q) (E : ℂ) :
    C.completePhasePairDiscriminantBracket D q E=0 := by
  let c : ℂ := P.parent.parent.miuraBall.actionBall.shift
  have hF := C.completePhasePairFrequencyVariation_eq_zero_of_real D q hqC hqD hr
  have he := Continuous.ext_on (s := ({-c}:Set ℂ)ᶜ) (dense_compl_singleton (-c))
    (C.analytic_completePhasePairDiscriminantBracket_energy D q).continuous (continuous_const : Continuous (fun _ : ℂ => (0:ℂ))) (fun x hx => ?_)
  · exact congrFun he E
  · have hxc : x+c ≠ 0 := by intro hz; apply hx; exact mem_singleton_iff.mpr (by linear_combination hz)
    let z := Complex.sqrt (x+c)
    have hz : z^2=x+c := complex_sqrt_sq _
    have hzne : z ≠ 0 := by intro he; rw [he,zero_pow (by decide : (2:ℕ) ≠ 0)] at hz; exact hxc hz.symm
    have hs : z^2-c=x := by rw [hz]; ring
    have ht := congrFun hF z
    change z*C.completePhasePairDiscriminantBracket D q (z^2-c)=0 at ht
    rw [hs] at ht
    exact (mul_eq_zero.mp ht).resolve_left hzne

theorem completePhasePair_Hamiltonian_isospectral_of_real
    (C : HillPhysicalOnIndexPhaseChart P n) (D : HillPhysicalOnIndexPhaseChart Q m)
    (q : PeriodOneHminusOne) (hqC : q ∈ C.source) (hqD : q ∈ D.source)
    (hr : IsRealPeriodOneHminusOne q) (E : ℂ) :
    hillHminusDiscriminantCotangent E q
      (NLS.Poisson.gardnerHamiltonianVector (C.completePhasePairBracket D) q)=0 := by
  change (fderiv ℂ (fun p => hillHminusDiscriminant p E) q) _=0
  rw [NLS.Poisson.fderiv_apply_gardnerHamiltonianVector,NLS.Poisson.hminusGardnerBracket_antisymm]
  change -C.completePhasePairDiscriminantBracket D q E=0
  rw [C.completePhasePairDiscriminantBracket_eq_zero_of_real D q hqC hqD hr E,neg_zero]

theorem exists_local_completePhasePair_discriminant_stationary
    (C : HillPhysicalOnIndexPhaseChart P n) (D : HillPhysicalOnIndexPhaseChart Q m)
    (q : PeriodOneHminusOne) (hqC : q ∈ C.source) (hqD : q ∈ D.source)
    (hr : IsRealPeriodOneHminusOne q) :
    ∃ r : ℝ, 0 < r ∧ ball q r ⊆ (C.source ∩ D.source) ∩ hillHminusOffIndexAnalyticDomain ∧
      AnalyticOnNhd ℂ (C.completePhasePairBracket D) (ball q r) ∧
      ∀ E : ℂ, ∀ p ∈ ball q r, C.completePhasePairDiscriminantBracket D p E=0 := by
  obtain ⟨r,hrpos,hsub,hpair,_⟩ := C.exists_local_completePhasePair_action_stationary D q hqC hqD hr
  refine ⟨r,hrpos,hsub,hpair,?_⟩
  intro E
  apply analytic_eqOn_of_real_periodOneHminus (ball q r) isOpen_ball
    (convex_ball q r).isPreconnected ⟨q,mem_ball_self hrpos,hr⟩ _ _
    (NLS.Poisson.analyticOnNhd_hminusGardnerBracket _ _ hpair
      ((analyticOnNhd_hillHminusDiscriminant_source E).mono (subset_univ _))) analyticOnNhd_const
  intro p hp hpr
  exact C.completePhasePairDiscriminantBracket_eq_zero_of_real D p (hsub hp).1.1 (hsub hp).1.2 hpr E

end NLS.KdV.HillPhysicalOnIndexPhaseChart
