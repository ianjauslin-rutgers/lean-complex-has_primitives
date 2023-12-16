import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.Complex.CauchyIntegral

import Mathlib.Tactic.LibrarySearch

open Complex Topology

set_option autoImplicit false

-- From V. Beffara https://github.com/vbeffara/RMT4
def hasPrimitives (U : Set ℂ) : Prop :=
  ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U → ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ Set.EqOn (deriv g) f U

/-- The wedge integral from z to w of a function f -/
noncomputable def WedgeInt (z w : ℂ) (f : ℂ → ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) + I • (∫ y : ℝ in z.im..w.im, f (re w + y * I))

/-- For small h, the rectangle stays inside the disc -/
theorem rectangle_in_disc {c : ℂ} {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : z ∈ Metric.ball c r) :
    ∀ᶠ h in 𝓝 0, z + h.re ∈ Metric.ball c r ∧ z + h.im * I ∈ Metric.ball c r ∧ z + h ∈ Metric.ball c r := by
  have : 0 < (r - dist z c) / 2 := by sorry
  filter_upwards [Metric.ball_mem_nhds 0 this]
  sorry



-- /-- Moreira's theorem -/
-- theorem moreiras_theorem {c : ℂ} {r : ℝ} (hr : 0 < r) {f : ℂ → ℂ}
--     (hf : ContinuousOn f (Metric.ball c r)) (hf₂ : ∀ z w, z ∈ Metric.ball c r → w ∈ Metric.ball c r → (z.re + w.im * I) ∈ Metric.ball c r → (w.re + z.im * I) ∈ Metric.ball c r →
--     ∫ x : ℝ in z.re..w.re, f (x + z.im * I) - ∫ x : ℝ in z.im..w.im, f (w.re + y * I) = 0) :
--      + I • ∫ y : ℝ in z.im..w.im, f (w.re + y * I) -
theorem Complex.mem_ball_iff_normSq (c z : ℂ) (r : ℝ) (hr : 0 ≤ r) :
    z ∈ Metric.ball c r ↔ normSq (z-c) < r^2 := by
  rw [mem_ball_iff_norm, normSq_eq_abs, norm_eq_abs, sq_lt_sq, abs_abs, abs_eq_self.mpr hr]



/-- diff of wedges -/
lemma diff_of_wedges {c : ℂ} {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : z ∈ Metric.ball c r)
    {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball c r)) :
    ∀ᶠ h in 𝓝 0,
      WedgeInt c (z+h) f - WedgeInt c z f = WedgeInt z (z+h) f := by
  --simp only [Metric.mem_ball] at hz
  have : 0 < (r - dist z c) / 2 := by sorry
  filter_upwards [Metric.ball_mem_nhds 0 this]
  intro h hh
--  simp only [Metric.mem_ball, dist_zero_right, norm_eq_abs] at hh
  simp only [WedgeInt] --, add_re, ofReal_add, add_im, smul_eq_mul]
  set intI := ∫ x : ℝ in c.re..(z + h).re, f (x + c.im * I)
  set intII := I • ∫ y : ℝ in c.im..(z + h).im, f ((z+h).re + y * I)
  set intIII := ∫ x : ℝ in c.re..z.re, f (x + c.im * I)
  set intIV := I • ∫ y : ℝ in c.im..z.im, f (z.re + y * I)
  set intV := ∫ x : ℝ in z.re..(z + h).re, f (x + z.im * I)
  set intVI := I • ∫ y : ℝ in z.im..(z + h).im, f ((z+h).re + y * I)
  let intVII := ∫ x : ℝ in z.re..(z+h).re, f (x + c.im * I)
  let intVIII := I • ∫ y : ℝ in c.im..z.im, f ((z+h).re + y * I)
  have integrHoriz : ∀ a₁ a₂ b : ℝ, a₁ + b * I ∈ Metric.ball c r → a₂ + b * I ∈ Metric.ball c r →
    IntervalIntegrable (fun x => f (x + b * I)) MeasureTheory.volume a₁ a₂
  · intro a₁ a₂ b ha₁ ha₂
    apply ContinuousOn.intervalIntegrable
    convert @ContinuousOn.comp ℝ ℂ ℂ _ _ _ f (fun x => (x : ℂ) + b * I) (Set.uIcc a₁ a₂)
      ((fun (x : ℝ) => (x : ℂ) + b * I) '' (Set.uIcc a₁ a₂)) ?_ ?_ ?_
    · convert hf.continuousOn
      sorry -- need to prove that this is a subset of the domain
    · apply Continuous.continuousOn
      exact Continuous.comp (continuous_add_right _) continuous_ofReal
    · exact Set.mapsTo_image _ _
  have integrVert : ∀ a b₁ b₂ : ℝ, a + b₁ * I ∈ Metric.ball c r → a + b₂ * I ∈ Metric.ball c r →
    IntervalIntegrable (fun y => f (a + y * I)) MeasureTheory.volume b₁ b₂
  · intro a b₁ b₂ ha hb
    apply ContinuousOn.intervalIntegrable
    convert @ContinuousOn.comp ℝ ℂ ℂ _ _ _ f (fun y => (a : ℂ) + y * I) (Set.uIcc b₁ b₂)
      ((fun (y : ℝ) => (a : ℂ) + y * I) '' (Set.uIcc b₁ b₂)) ?_ ?_ ?_
    · convert hf.continuousOn
      sorry -- need to prove that this is a subset of the domain
    · apply Continuous.continuousOn
      refine Continuous.comp (continuous_add_left _) ?_
      refine Continuous.comp (continuous_mul_right _) continuous_ofReal
    · exact Set.mapsTo_image _ _
  have intIdecomp : intI = intIII + intVII  := by
    rw [intervalIntegral.integral_add_adjacent_intervals] <;> apply integrHoriz
    · simp only [re_add_im, Metric.mem_ball, dist_self, hr]
    · sorry -- point in ball
    · sorry -- point in ball
    · sorry -- point in ball
  have intIIdecomp : intII = intVIII + intVI := by
    rw [← smul_add, intervalIntegral.integral_add_adjacent_intervals] <;> apply integrVert
    · sorry
    · sorry
    · sorry
    · sorry
  have rectZero : intVIII = - intVII + intV + intIV := by
    rw [← sub_eq_zero]
    have : intVII - intV + intVIII - intIV = 0 := by
      convert integral_boundary_rect_eq_zero_of_differentiable_on_off_countable f (z.re + c.im * I) ((z+h).re + z.im * I) ∅ ?_ ?_ ?_ using 4
      · simp
      · congr! 1 <;> simp
      · congr! 1 <;> simp
      · simp
      · simp
      · simp
      · simp
      · sorry -- ContinuousOn
      · intro x hx
        sorry -- differentiable
    rw [← this]
    ring

  rw [intIdecomp]
  rw [intIIdecomp]
  rw [rectZero]
  ring


#exit
    · apply ContinuousOn.intervalIntegrable
      convert @ContinuousOn.comp ℝ ℂ ℂ _ _ _ f (fun x => (x : ℂ) + c.im * I) (Set.uIcc c.re z.re)
        ((fun (x : ℝ) => (x : ℂ) + c.im * I) '' (Set.uIcc c.re z.re)) ?_ ?_ ?_
      · convert @DifferentiableOn.continuousOn ℂ _ ℂ _ _ ℂ _ _ f _ _
        apply hf.mono
        intro x hx
        simp only [ge_iff_le, Set.mem_image] at hx
        obtain ⟨x₁, hx₁, hx₁'⟩ := hx
        rw [Set.mem_uIcc] at hx₁
        rw [Complex.mem_ball_iff_normSq hr] at hz
        rw [Complex.mem_ball_iff_normSq hr]
        apply lt_of_le_of_lt ?_ hz
        rw [← hx₁']
        rw [Complex.normSq_apply]
        rw [Complex.normSq_apply]
        simp only [sub_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
          sub_self, add_zero, sub_im, add_im, mul_im, zero_add]
        cases hx₁ <;>calc
        _ ≤ (z.re - c.re) * (z.re - c.re) := by nlinarith
        _ ≤ _ := by
          simp only [le_add_iff_nonneg_right, gt_iff_lt, sub_pos]
          exact mul_self_nonneg (z.im - c.im)
      · apply Continuous.continuousOn
        exact Continuous.comp (continuous_add_right _) continuous_ofReal
      · exact Set.mapsTo_image _ _
    sorry--integrable






lemma wedgeInt_of_const (z w c : ℂ) :
    WedgeInt z w (fun x => c) = c*(w-z) := by
  simp only [WedgeInt, intervalIntegral.integral_const, real_smul, ofReal_sub, smul_eq_mul]
  ext <;>
  simp only [add_re, mul_re, sub_re, ofReal_re, sub_im, ofReal_im, sub_self, zero_mul,
sub_zero, I_re, I_im, mul_im, add_zero, one_mul, zero_sub, add_im,
zero_add]
   <;> ring

example (hyp: ∀ᶠ h in (𝓝 0), h=2) : ∀ᶠ h in (𝓝 0), h^2=4 := by
  filter_upwards [hyp]
  intro a hw
  rw [hw]
  ring



lemma deriv_of_linint {f: ℝ → ℂ} {a: ℝ} {U : Set ℝ} (hU: IsOpen U) (hUa: a∈ U) (hf: ContinuousOn f U) :
    Asymptotics.IsLittleO (𝓝 0) (fun h ↦ ((∫ x in a..a+h, f x) - h*(f a))) (fun h ↦ h) := by
  sorry

lemma deriv_of_horv_0 {f:ℝ →ℂ}
    (hfC: ContinuousAt f 0) (hfM: StronglyMeasurableAtFilter f (nhds 0))
    (c : ℝ) (hc: 0<c):
    ∀ᶠ (h : ℝ) in 𝓝 0, ‖(∫ (x : ℝ) in (0:ℝ)..h, f x) - h * f 0‖ ≤ c/3 * ‖h‖ := by

  have integrable : IntervalIntegrable (fun x:ℝ => f x-f 0) Real.measureSpace.volume 0 0 := by
    simp
  have continuous : ContinuousAt (fun x => f x - f 0) 0 := by
    sorry
  have measurable : StronglyMeasurableAtFilter (fun x => f x - f 0) (nhds 0) := by
    sorry

  have diff := intervalIntegral.integral_hasDerivAt_right integrable measurable continuous
  rw [hasDerivAt_iff_isLittleO] at diff
  simp only [intervalIntegral.integral_same, sub_zero, re_add_im, sub_self, real_smul, ofReal_sub, mul_zero] at diff
  rw [Asymptotics.isLittleO_iff] at diff
  have : 0 < c/3 := div_pos hc zero_lt_three
  have := diff this

  -- condition on h
  rw [Filter.eventually_iff] at this
  filter_upwards [this]
  intro h h_diff

  simp only [ofReal_zero, add_zero, re_add_im, sub_self, mul_zero, sub_zero, norm_eq_abs, Real.norm_eq_abs] at h_diff

  -- write f as f-f(z₀)+f(z₀)
  have : ∫ x in (0:ℝ)..h, f x = ∫ x in (0:ℝ)..h, ((f x-f 0) + f 0) := by ring_nf
  have : ∫ x in (0:ℝ)..h, f x = (∫ x in (0:ℝ)..h, (f x-f 0)) + h*f 0 := by
    sorry
  rw [this]
  simp only [add_sub_cancel, norm_eq_abs, Real.norm_eq_abs, ge_iff_le]
  exact h_diff


lemma deriv_of_horv (a:ℝ) {f:ℝ →ℂ}
    (hfC: ContinuousAt f a) (hfM: StronglyMeasurableAtFilter f (nhds a))
    (c : ℝ) (hc: 0<c):
    ∀ᶠ (h : ℝ) in 𝓝 0, ‖(∫ (x : ℝ) in a..a+h, f x) - h * f a‖ ≤ c/3 * ‖h‖ := by
  have continuous : ContinuousAt (fun x => f (a+x)) 0 := by
    sorry
  have measurable : StronglyMeasurableAtFilter (fun x => f (a+x)) (nhds 0) := by
    sorry
  have := deriv_of_horv_0 continuous measurable c hc
  --have : Complex.abs (∫ (x : ℝ) in (0:ℝ)..h, f (a+x) - f a) ≤ c/3 * |h| := by
  --  sorry
  simp_rw [intervalIntegral.integral_comp_add_left (fun x:ℝ => f x) a] at this
  simp only [add_zero, sub_self, mul_zero, sub_zero] at this
  exact this

lemma deriv_of_wedgeInt {f: ℂ → ℂ} {U : Set ℂ} {hU: IsOpen U} (hf: ContinuousOn f U)
    {z₀ : ℂ} (hz₀ : z₀∈U) :
    Asymptotics.IsLittleO (𝓝 0) (fun h:ℂ ↦ ((WedgeInt z₀ (z₀+h) f) - h*(f z₀))) (fun h ↦ h) := by

  simp [WedgeInt]
  -- turn littleO into bigO
  rw [Asymptotics.isLittleO_iff]
  intro c hc

  -- get ball around z₀
  obtain ⟨ε,hε,B⟩ := (Metric.isOpen_iff.mp hU) z₀ hz₀

  -- restate goal, splitting real and imaginary parts of h
  have : ∀ᶠ (hre : ℝ) in 𝓝 0, ∀ᶠ(him : ℝ) in 𝓝 0,
  ‖((∫ (x : ℝ) in z₀.re..z₀.re + hre, f (↑x + ↑z₀.im * I)) +
          I * ∫ (y : ℝ) in z₀.im..z₀.im + him, f (↑z₀.re + ↑hre + ↑y * I)) -
        (hre+him*I) * f z₀‖ ≤
    c * ‖hre+him*I‖ := by

    -- apply fundamental theorem of calculus to horizontal part
    have continuous_h : ContinuousAt (fun x:ℝ => f (x + z₀.im*I)) z₀.re := by
      sorry
    have stronglymeasurable_h : StronglyMeasurableAtFilter (fun x:ℝ => f (x + z₀.im*I)) (nhds z₀.re) := by
      sorry
    have horizontal := deriv_of_horv z₀.re  continuous_h stronglymeasurable_h c hc

    -- condition on h.re
    rw [Filter.eventually_iff] at horizontal
    filter_upwards [Metric.ball_mem_nhds 0 hε,horizontal]
    intro hre hre_eps hre_diff

    -- apply fundamental theorem of calculus to vertical part
    have continuous_v : ContinuousAt (fun y:ℝ => f (z₀.re + hre + y*I)) z₀.im := by
      sorry
    have stronglymeasurable_v : StronglyMeasurableAtFilter (fun y:ℝ => f (z₀.re + hre + y*I)) (nhds z₀.im) := by
      sorry
    have vertical := deriv_of_horv z₀.im  continuous_v stronglymeasurable_v c hc

    -- condition on h.im
    rw [Filter.eventually_iff] at vertical
    filter_upwards [Metric.ball_mem_nhds 0 hε,vertical]
    intro him him_eps him_diff

    have : ‖((∫ (x : ℝ) in z₀.re..z₀.re + hre, f (↑x + ↑z₀.im * I)) +
        I * ∫ (y : ℝ) in z₀.im..z₀.im + him, f (↑z₀.re + ↑hre + ↑y * I)) -
        (↑hre + ↑him * I) * f z₀‖ ≤
        ‖(∫ (x : ℝ) in z₀.re..z₀.re + hre, f (↑x + ↑z₀.im * I)) - hre * f z₀‖ +
        ‖(∫ (y : ℝ) in z₀.im..z₀.im + him, f (↑z₀.re + ↑hre + ↑y * I) - ↑him * f (z₀+hre))‖
        + ‖I* (f (z₀+hre) - f z₀)‖ := by
      -- norm_add_le
      sorry

    suffices hsp : ‖(∫ (x : ℝ) in z₀.re..z₀.re + hre, f (↑x + ↑z₀.im * I)) - hre * f z₀‖ +
        ‖(∫ (y : ℝ) in z₀.im..z₀.im + him, f (↑z₀.re + ↑hre + ↑y * I) - ↑him * f (z₀+hre))‖
        + ‖I* (f (z₀+hre) - f z₀)‖ ≤ c*‖hre + him*I‖

    · exact le_trans this hsp
    · sorry


--  -- write f as f-f(z₀)+f(z₀)
--  have : ∀ h:ℂ, ∫ x in z₀.re..z₀.re + h.re, f (x + z₀.im * I) = ∫ x in z₀.re..z₀.re + h.re, ((f (x + z₀.im * I)-f z₀) + f z₀) := by
--    intro h
--    ring_nf
--  have : ∀ h:ℂ, ∫ x in z₀.re..z₀.re + h.re, f (x + z₀.im * I) = (∫ x in z₀.re..z₀.re + h.re, (f (x + z₀.im * I)-f z₀)) + h.re*f z₀ := by
--    intro h
--    sorry
--  conv =>
--    lhs
--    intro h
--    rw [this]
--
--  -- write f as f-f(z₀)+f(z₀)
--  have : ∀ h:ℂ, ∫ y in z₀.im..z₀.im + h.im, f (z₀.re + h.re + y * I) = ∫ y in z₀.im..z₀.im + h.im, (f (z₀.re + h.re + y * I) -f z₀) + f z₀ := by
--    intro h
--    ring_nf
--  have : ∀ h:ℂ, ∫ y in z₀.im..z₀.im + h.im, f (z₀.re + h.re + y * I) = (∫ y in z₀.im..z₀.im + h.im, f (z₀.re + h.re + y * I) -f z₀) + h.im * f z₀ := by
--    intro h
--    sorry
--  conv =>
--    lhs
--    intro h
--    rw [this]
--
--  -- why doesn't this work??
----  conv =>
----    lhs
----    intro h
----    pattern h * f z₀
----    rw [(Complex.re_add_im h).symm]
----  ring_nf
--  have : ∀ h : ℂ, h*f z₀ = (h.re+h.im*I)*f z₀ := by
--    intro h
--    simp
--  conv =>
--    lhs
--    intro h
--    rw [this h]
--
--  -- why doesn't ring do this on its own?!?!?!?!
--  have : ∀ h:ℂ, (∫ (x : ℝ) in z₀.re..z₀.re + h.re, f (↑x + ↑z₀.im * I) - f z₀) + ↑h.re * f z₀ +
--        I * ((∫ (y : ℝ) in z₀.im..z₀.im + h.im, f (↑z₀.re + ↑h.re + ↑y * I) - f z₀) + ↑h.im * f z₀) -
--      (↑h.re + ↑h.im * I) * f z₀ = (∫ (x : ℝ) in z₀.re..z₀.re + h.re, f (↑x + ↑z₀.im * I) - f z₀) +
--        I * ((∫ (y : ℝ) in z₀.im..z₀.im + h.im, f (↑z₀.re + ↑h.re + ↑y * I) - f z₀)) := by
--    intro h
--    ring
--  conv =>
--    lhs
--    intro h
--    rw [this h]
--
--  -- apply fundamental theorem of calculus to each part of the integral
--  have continuous_h : ContinuousAt (fun x:ℝ => f (x + z₀.im*I)-f z₀) z₀.re := by
--    sorry
--  have integrable_h : IntervalIntegrable (fun x:ℝ => f (x + z₀.im*I)-f z₀) Real.measureSpace.volume z₀.re z₀.re := by
--    sorry
--  have stronglymeasureable_h : StronglyMeasurableAtFilter (fun x:ℝ => f (x + z₀.im*I)-f z₀) (nhds z₀.re) := by
--    sorry
--
--  have diff_h := intervalIntegral.integral_hasDerivAt_right integrable_h stronglymeasureable_h continuous_h
--  rw [hasDerivAt_iff_isLittleO] at diff_h
--  simp only [intervalIntegral.integral_same, sub_zero, re_add_im, sub_self, real_smul, ofReal_sub, mul_zero] at diff_h




  -- apply fundamental theorem of calculus to each part of the integral
  have horint : Asymptotics.IsLittleO (𝓝 0) (fun h:ℂ ↦ ∫ x in z₀.re..z₀.re + h.re, (f (x + z₀.im * I) - f z₀)) (fun h => h) := by
    have integrable : IntervalIntegrable (fun x:ℝ => f (x + z₀.im*I)-f z₀) z₀.re z₀.re+h.re
  have verint : Asymptotics.IsLittleO (𝓝 0) (fun h:ℂ ↦ ∫ y in z₀.im..z₀.im + h.im, (f (z₀.re + h.re + y * I) - f z₀)) (fun h => h) := by
    sorry
  have verint' : Asymptotics.IsLittleO (𝓝 0) (fun h:ℂ ↦ I*∫ y in z₀.im..z₀.im + h.im, (f (z₀.re + h.re + y * I) - f z₀)) (fun h => h) :=
    Asymptotics.IsLittleO.const_mul_left verint I

  exact Asymptotics.IsLittleO.add horint verint'

  --have : Asymptotics.IsLittleO (𝓝 0) (fun h ↦ f (z₀+h) - f z₀) (fun h ↦ (1:ℂ)) := by
  --  have := ContinuousOn.continuousAt hf (IsOpen.mem_nhds hU hz₀)
  --  have f_tendsto := ContinuousAt.tendsto this
  --  simp only [Asymptotics.isLittleO_one_iff]
  --  rw [tendsto_sub_nhds_zero_iff]

  --  -- shift the origin of the filter
  --  -- this can probably be done better
  --  let g := fun h ↦ z₀+h
  --  have g_tendsto : Filter.Tendsto g (𝓝 0) (𝓝 z₀) := by
  --    dsimp [g]
  --    rw [tendsto_sub_nhds_zero_iff.symm]
  --    simp only [add_sub_cancel']
  --    rw [Filter.tendsto_def]
  --    intros s hs
  --    simp only [Set.preimage_id']
  --    exact hs
  --  have := Filter.Tendsto.comp f_tendsto g_tendsto
  --  rw [Function.comp] at this
  --  exact this

  --dsimp [WedgeInt]







-- trivial case: empty set
theorem hasPrimitivesOfEmpty : hasPrimitives ∅ := by
  dsimp [hasPrimitives]
  simp only [Set.eqOn_empty, and_true]
  dsimp [DifferentiableOn]
  dsimp [DifferentiableWithinAt]
  dsimp [HasFDerivWithinAt]
  dsimp [HasFDerivAtFilter]
  simp only [Set.mem_empty_iff_false, nhdsWithin_empty, map_sub, IsEmpty.forall_iff, forall_const, exists_const,
  forall_true_left]


-- To prove the main theorem, we first prove it on a disc
-- not sure what happens if U is empty
theorem hasPrimitivesOfConvex (U: Set ℂ) (hU: Convex ℝ U) : hasPrimitives U := by
  by_cases hne : U = ∅
  · convert hasPrimitivesOfEmpty

  · intros f hf_diff
    -- get z₀
    have : Nonempty U := Set.nonempty_iff_ne_empty'.mpr hne
    obtain ⟨z₀,hz₀⟩ := Set.exists_mem_of_nonempty U
    use fun z ↦ linint z₀ z f
    constructor
    · sorry

    · intro z  hz
      have : ∀ h : ℂ, z+h∈ U → linint z₀ (z+h) f - linint z₀ z f = linint z (z+h) f:= by
        intros h hinU
        refine diffOfIntegrals U hU z₀ (z+h) z ?_ hinU hz f hf_diff

        exact Subtype.mem z₀
      sorry


-- main theorem: holomorphic functions on simply connected open sets have primitives
theorem hasPrimitivesOfSimplyConnected (U : Set ℂ) (hSc : SimplyConnectedSpace U) (hO : IsOpen U) :
    hasPrimitives U := by
  sorry


#exit
theorem contDiffStraightSeg (t₁ t₂ : ℝ ) (ht : t₁ < t₂) (z₁ z₂ : ℂ) (γ : ℝ → ℂ ) : ∀ᶠ i in 𝓝 i₀, ContinuousOn (F i) (γ '' Icc t₁ t₂) := by
  refine straightSeg t₁ t₂ ht z₁ z₂
  sorry
