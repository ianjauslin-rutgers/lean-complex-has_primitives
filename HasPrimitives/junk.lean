import Mathlib

open Topology


example {f g h : ℝ → ℝ} {x : ℝ} (hfg : f =o[𝓝 x] g) (hgh : g =O[𝓝 x] h) :
  f =o[𝓝 x] h := by
  exact Asymptotics.IsLittleO.trans_isBigO hfg hgh

example {f g h : ℝ → ℝ} {x : ℝ} (hfg : f =o[𝓝 x] g) (hgh : g =O[𝓝 x] h) :
  f =o[𝓝 x] h := by
  calc
    f =o[𝓝 x] g := hfg
    _ =O[𝓝 x] h := hgh



example {z : ℂ} {f : ℝ → ℂ} (h : (fun x ↦ f (x - z.re)) =o[𝓝 z.re] (fun x ↦ x - z.re)) :
  (fun w ↦ f (w.re - z.re)) =o[𝓝 z] (fun w ↦ w - z) := by
  have zReTendsTo : Filter.Tendsto (fun (w : ℂ) ↦ w.re) (𝓝 z) (𝓝 z.re) :=
    by apply Continuous.tendsto Complex.continuous_re
  have LittleO_comp := h.comp_tendsto zReTendsTo
  refine LittleO_comp.trans_isBigO ?_
  extract_goal
  rw [Asymptotics.isBigO_iff]
  use 1
  filter_upwards
  intro w
  simp
  rw [← Complex.sub_re ]
  exact Complex.abs_re_le_abs (w - z)


/-
Note: Try to set up a trans instance for `theorem Asymptotics.IsLittleO.trans_isBigO` (should be tagged an instance of trans) (Ask on zulip, where someone can do it faster... )
-/
  #exit
  calc
    _ =o[𝓝 z] (fun w => w.re - z.re) := LittleO_comp
    _ =O[𝓝 z] _ := ?_
  rw [Asymptotics.isLittleO_iff]
  intro c c_pos
  let c₁ := c / 100
  have c₁_pos : 0 < c₁ := div_pos c_pos (by norm_num)
  filter_upwards [Metric.ball_mem_nhds z c₁_pos]
  intro w w_in_ball


#exit

  ((fun x => f (x - z.re)) ∘ fun w => w.re) =o[𝓝 z] ((fun x => x - z.re) ∘ fun w => w.re)
⊢
  sorry

#exit
  have : fun w ↦ w.re - z.re =o[𝓝 z.re] fun w ↦ w - z := by
    have : fun w ↦ w.re - z.re = fun w ↦ w - z := by
      ext
      simp
    rw [this]
    exact h
  have : fun w ↦ w - z = fun w ↦ w.re - z.re := by
    ext
    simp
  rw [this]
  exact this


#exit
(fun x' =>
    ((∫ (x : ℝ) in z.re..x', f (↑x + ↑z.im * I)) - ∫ (x : ℝ) in z.re..z.re, f (↑x + ↑z.im * I)) -
      (ContinuousLinearMap.smulRight 1 (f (↑z.re + ↑z.im * I))) (x' - z.re)) =o[𝓝 z.re]
  fun x' => x' - z.re
⊢ (fun w => (∫ (x : ℝ) in z.re..w.re, f (↑x + ↑z.im * I)) - ↑(w - z).re * f z) =o[𝓝 z] fun w => w - z


example {f g h i : ℝ → ℝ} {x : ℝ} (hfg : ∀ᶠ (y : ℝ) in 𝓝 x, f y = g y) (hgh : (g + i) =o[𝓝 x] h) :
  (f + i) =o[𝓝 x] h := by
  sorry
#exit
  have := @Filter.eventually_of_forall (hp := fun (x : ℝ) (hx : f x = g x) ↦ hx.symm)
  have := @Filter.Eventually.mp
  have := @Asymptotics.IsLittleO.congr'
  have := hgh.congr' (hfg.mp (eventually_of_forall (fun (x:ℝ) (hx : f x = g x) ↦ hx.symm))) (by rfl)



#exit

example (f : ℝ → ℝ) (x : ℝ) (h : ContinuousAt f x) :
  (fun y ↦ (∫ t in x..y, f t) - (y - x) * f x) =o[𝓝 x] (fun y ↦ y - x) := by
  sorry

example (f : ℝ → ℝ) (x : ℝ) (h : ContinuousAt f x) :
  (fun y ↦ (∫ t in x..y, f (t+(y-x))) - (y - x) * f x) =o[𝓝 x] (fun y ↦ y - x) := by
  sorry
