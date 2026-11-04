import NLS.KdV.HillWeightedDirichletExterior
import NLS.KdV.HillDirichletAnalyticLabels
import NLS.KdV.HillFreeDirichlet

/-! # Excluding the lower exterior of the actual Dirichlet spectrum -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV

/-- One negative-energy cutoff excludes actual Dirichlet zeros for
an entire bounded complex L2 potential family. -/
theorem exists_hillL2Dirichlet_negative_cutoff (B : ℝ) :
    ∃ L : ℝ, ∀ q : Coeff 2, ‖q‖≤B → ∀ x : ℝ, x≤L → hillL2DirichletCharacteristic q x≠0 := by
  obtain ⟨C,_hC,hcut⟩ := exists_hillL2Dirichlet_exterior_lower_bound (by positivity : 0<Real.pi/4)
  obtain ⟨R,hR,hbound⟩ := hcut B
  let T := max R (Real.pi/4)
  refine ⟨-T^2,?_⟩
  intro q hq x hx
  have hT : 0<T := hR.trans_le (le_max_left _ _)
  have hnx : 0≤-x := by nlinarith [sq_nonneg T]
  let t := Real.sqrt (-x)
  have ht0 : 0≤t := Real.sqrt_nonneg _
  have ht2 : t^2=-x := Real.sq_sqrt hnx
  have ht : T≤t := by nlinarith
  let z : ℂ := I*(t : ℂ)
  have hz : z^2=(x : ℂ) := by
    dsimp only [z]
    rw [mul_pow,I_sq,← ofReal_pow,ht2]
    push_cast
    ring
  have hn : ‖z‖=t := by
    simp only [z,norm_mul,norm_I,one_mul,norm_real,Real.norm_of_nonneg ht0]
  have hsep (m : ℤ) : Real.pi/4≤‖z-(Real.pi : ℂ)*m‖ := by
    have hi : |(z-(Real.pi : ℂ)*m).im|=t := by
      simp [z,abs_of_nonneg ht0]
    calc
      Real.pi/4≤T := le_max_right _ _
      _ ≤ t := ht
      _ = |(z-(Real.pi : ℂ)*m).im| := hi.symm
      _ ≤ _ := abs_im_le_norm _
  have hb := (hbound q hq z (by rw [hn];exact (le_max_left _ _).trans ht) hsep).1
  rwa [hz] at hb

/-- Actual real Dirichlet roots have a locally uniform lower bound in
the original complex L2 potential topology. -/
theorem exists_hillL2Dirichlet_local_uniform_lower_bound (q : Coeff 2) :
    ∃ U : Set (Coeff 2), IsOpen U ∧ q∈U ∧ ∃ L : ℝ, ∀ p∈U, ∀ x : ℝ,
      hillL2DirichletCharacteristic p x=0 → L<x := by
  obtain ⟨L,hL⟩ := exists_hillL2Dirichlet_negative_cutoff (‖q‖+1)
  refine ⟨ball q 1,isOpen_ball,mem_ball_self (by norm_num),L,?_⟩
  intro p hp x hz
  have hn : ‖p‖≤‖q‖+1 := by
    have hh := norm_le_norm_sub_add p q
    have hdist : ‖p-q‖<1 := by simpa only [mem_ball,dist_eq_norm] using hp
    linarith
  exact lt_of_not_ge (fun hx => hL p hn x hx hz)

/-- The actual free characteristic has no nonpositive energy zero,
including the filled value at energy zero. -/
theorem hillL2Dirichlet_free_ne_zero_of_nonpos (x : ℝ) (hx : x≤0) :
    hillL2DirichletCharacteristic 0 x≠0 := by
  by_cases hx0 : x=0
  · subst x
    rw [ofReal_zero,hillL2DirichletCharacteristic_free_zero]
    norm_num
  have hxn : (x : ℂ)≠0 := ofReal_ne_zero.mpr hx0
  have hs : Complex.sqrt (x : ℂ)≠0 := by
    intro h
    have he := complex_sqrt_sq (x : ℂ)
    rw [h,zero_pow (by norm_num : (2 : ℕ)≠0)] at he
    exact hxn he.symm
  have he : hillL2DirichletCharacteristic 0 x=sin (Complex.sqrt (x : ℂ))/Complex.sqrt (x : ℂ) := by
    simpa only [complex_sqrt_sq] using hillL2DirichletCharacteristic_free_sq (Complex.sqrt (x : ℂ)) hs
  rw [he]
  apply div_ne_zero _ hs
  intro hsin
  obtain ⟨k,hk⟩ := Complex.sin_eq_zero_iff.mp hsin
  have hsq := complex_sqrt_sq (x : ℂ)
  rw [hk] at hsq
  have hreal : ((k : ℝ)*Real.pi)^2=x := by exact_mod_cast hsq
  have hxpos : 0≤x := by rw [← hreal];exact sq_nonneg _
  exact hx0 (le_antisymm hx hxpos)

/-- Lower-exterior Dirichlet roots are stable under continuation and
closed under limits for every real period-one L2 family. -/
theorem isClopen_hillDirichlet_lower_root_family
    {T : Type*} [TopologicalSpace T]
    (Q : T → WeightedCoeff SpectralWeight.one.toWeight 2) (hQ : Continuous Q)
    (hq : ∀ t, SpectralWeight.one.toCoeff (Q t)∈Coeff.paritySubspace 0)
    (hr : ∀ t, IsRealHillPotential (SpectralWeight.one.toCoeff (Q t))) :
    IsClopen {t : T | ∃ x : ℝ, x≤hillRealLabels (Q t) (hq t) (hr t) 0 ∧
      hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff (Q t)) x=0} := by
  let P : T → Coeff 2 := fun t => SpectralWeight.one.toCoeff (Q t)
  have hP : Continuous P := SpectralWeight.one.toCoeff.continuous.comp hQ
  let b : T → ℝ := fun t => hillRealLabels (Q t) (hq t) (hr t) 0
  let A : Set T := {t | ∃ x : ℝ, x≤b t ∧ hillL2DirichletCharacteristic (P t) x=0}
  have hb : Continuous b := continuous_hillRealLabels_family Q hQ hq hr 0
  have hF : Continuous (fun t : T × ℝ => hillL2DirichletCharacteristic (P t.1) t.2) := by
    have hc : Continuous (fun t : ℂ × Coeff 2 => hillL2DirichletCharacteristic t.2 t.1) :=
      analyticOnNhd_hillL2DirichletCharacteristic_joint.continuous
    exact Continuous.comp (g := fun t : ℂ × Coeff 2 => hillL2DirichletCharacteristic t.2 t.1)
      (f := fun t : T × ℝ => ((t.2 : ℂ),P t.1)) hc
      ((Complex.continuous_ofReal.comp continuous_snd).prodMk (hP.comp continuous_fst))
  constructor
  · change IsClosed A
    rw [← isOpen_compl_iff]
    apply isOpen_iff_mem_nhds.mpr
    intro t0 ht0
    obtain ⟨U,hU,hqU,L,hlower⟩ := exists_hillL2Dirichlet_local_uniform_lower_bound (P t0)
    let K : Set T := {t | ∃ x∈Icc L (max L (b t)), hillL2DirichletCharacteristic (P t) x=0}
    have hK : IsClosed K := isClosed_exists_zero_in_variable_Icc _ (fun _ => L) (fun t => max L (b t))
      hF continuous_const (continuous_const.max hb) (fun _ => le_max_left _ _)
    have hlocal (t : T) (ht : P t∈U) : t∈A ↔ t∈K := by
      constructor
      · rintro ⟨x,hx,hz⟩
        exact ⟨x,⟨(hlower (P t) ht x hz).le,hx.trans (le_max_right _ _)⟩,hz⟩
      · rintro ⟨x,hx,hz⟩
        have hl := hlower (P t) ht x hz
        have hx' : x≤b t := by
          rcases le_max_iff.mp hx.2 with h | h
          · exact False.elim (not_le_of_gt hl h)
          · exact h
        exact ⟨x,hx',hz⟩
    have htK : t0∉K := fun h => ht0 ((hlocal t0 hqU).mpr h)
    have hN := ((hU.preimage hP).inter hK.isOpen_compl).mem_nhds ⟨hqU,htK⟩
    apply Filter.mem_of_superset hN
    intro t ht hA
    exact ht.2 ((hlocal t ht.1).mp hA)
  · change IsOpen A
    apply isOpen_iff_mem_nhds.mpr
    rintro t0 ⟨x,hx,hz⟩
    obtain ⟨a,ha,hax,he⟩ := exists_hillL2Dirichlet_analytic_real_root_branch (P t0) (hr t0) x hz
    have hbranch : ∀ᶠ t in 𝓝 t0, hillL2DirichletCharacteristic (P t) (a (P t))=0 ∧ (a (P t)).im=0 := by
      filter_upwards [hP.continuousAt.tendsto.eventually he] with t ht
      exact ⟨ht.1,ht.2 (hr t)⟩
    have hac : ContinuousAt (fun t => (a (P t)).re) t0 :=
      Complex.continuous_re.continuousAt.comp (ha.continuousAt.comp hP.continuousAt)
    have htop : (a (P t0)).re<hillRealLabels (Q t0) (hq t0) (hr t0) 1 := by
      rw [hax,ofReal_re]
      exact lt_of_le_of_lt hx (hillRealLabels_band_strict (Q t0) (hq t0) (hr t0) 0)
    have hcollar : ∀ᶠ t in 𝓝 t0, (a (P t)).re<hillRealLabels (Q t) (hq t) (hr t) 1 :=
      hac.eventually_lt (continuous_hillRealLabels_family Q hQ hq hr 1).continuousAt htop
    filter_upwards [hbranch,hcollar] with t ht hlt
    have heq : ((a (P t)).re : ℂ)=a (P t) := by apply Complex.ext <;> simp [ht.2]
    have hzero : hillL2DirichletCharacteristic (P t) ((a (P t)).re)=0 := by rw [heq];exact ht.1
    refine ⟨(a (P t)).re,?_,hzero⟩
    by_contra! hbad
    exact hillL2DirichletCharacteristic_ne_zero_on_open_band (Q t) (hq t) (hr t) 0 _ ⟨hbad,hlt⟩ hzero

/-- The actual Dirichlet characteristic never vanishes at or below the
lowest periodic energy. The real scalar homotopy includes ground equality. -/
theorem hillL2DirichletCharacteristic_ne_zero_at_or_below_lowest
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (x : ℝ)
    (hx : x≤hillRealLabels q hq hr 0) :
    hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) x≠0 := by
  intro hz
  let Q : ℝ → WeightedCoeff SpectralWeight.one.toWeight 2 := fun t => (t : ℂ) • q
  have hQ : Continuous Q := Complex.continuous_ofReal.smul continuous_const
  have hQp (t : ℝ) : SpectralWeight.one.toCoeff (Q t)∈Coeff.paritySubspace 0 := by
    rw [map_smul]
    exact (Coeff.paritySubspace 0).smul_mem _ hq
  have hQr (t : ℝ) : IsRealHillPotential (SpectralWeight.one.toCoeff (Q t)) := by
    rw [map_smul]
    intro k
    simp only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,map_mul,conj_ofReal,hr k]
  have hc := isClopen_hillDirichlet_lower_root_family Q hQ hQp hQr
  have h1 : (1 : ℝ)∈{t : ℝ | ∃ a : ℝ, a≤hillRealLabels (Q t) (hQp t) (hQr t) 0 ∧
      hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff (Q t)) a=0} := by
    simpa only [Q,ofReal_one,one_smul,mem_ofPred_eq] using
      (show ∃ a : ℝ, a≤hillRealLabels q hq hr 0 ∧ hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) a=0 from ⟨x,hx,hz⟩)
  have hall := hc.eq_univ ⟨1,h1⟩
  have h0 : (0 : ℝ)∈{t : ℝ | ∃ a : ℝ, a≤hillRealLabels (Q t) (hQp t) (hQr t) 0 ∧
      hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff (Q t)) a=0} := by rw [hall];trivial
  obtain ⟨a,ha,haz⟩ := h0
  have hQ0 : Q 0=0 := by simp [Q]
  simp only [Q,ofReal_zero,zero_smul,hillRealLabels_zero] at ha
  have han : a≤0 := by simpa [freeHillValue] using ha
  rw [hQ0,map_zero] at haz
  exact hillL2Dirichlet_free_ne_zero_of_nonpos a han haz

end NLS.KdV
