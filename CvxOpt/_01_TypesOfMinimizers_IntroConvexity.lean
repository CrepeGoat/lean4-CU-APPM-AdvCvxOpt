import Init.Prelude
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Topology.Defs.Basic

import CvxOpt._00_IntroToOptProblems


section main

variable
    {n : Nat}
    {D: Type*}
    {R: Type*}

-- @[deprecated "just use `x ∈ C`" (since := "2025-03-27")]
def FeasiblePoint
    (C : Set D)
    (x : D)
    : Prop := x ∈ C

example
    [LE R] {C : Set D} {x : D}
    : FeasiblePoint C x ↔ x ∈ C
    := by rfl

-- @[deprecated "just use `x ∈ ArgumentMinimumOn f C`" (since := "2025-03-27")]
def GlobalMinimizer
    [LE R]
    (f: D → R)
    (C : Set D)
    (x : D)
    : Prop := x ∈ C ∧ ∀ y ∈ C, f x ≤ f y

example
    [LE R] {f: D → R} {C : Set D} {x : D}
    : GlobalMinimizer f C x ↔ x ∈ ArgumentMinimumOn f C
    := by
    simp [GlobalMinimizer, ArgumentMinimumOn, MinimumOn, IsLeast, lowerBounds]
    intro xinC _
    constructor
    case left => exact xinC
    case right => exists x

/- Note: solutions may not exist-/
example
    : ArgumentMinimumOn (fun x : NNReal => x ^ 2) (setOf (fun x => 0 < x ∧ x < 1)) = ∅
    := by
    rw [← Set.not_nonempty_iff_eq_empty]
    simp [ArgumentMinimumOn, MinimumOn, IsLeast, lowerBounds, Set.Nonempty]
    intro x h h'
    exists (x / 2)^2, x / 2
    simp
    constructor
    case left => exact h
    case right =>

    constructor
    case left =>
        simp [div_lt_iff₀]
        apply lt_trans
        exact h'
        simp
    case right =>

    apply pow_lt_pow_left₀
    case a => simp
    case hab => simp [h]
    case ha => simp [h']

def LocalMinimizer
    [PseudoMetricSpace D] [LE R]
    (f: D → R)
    (C: Set D)
    (x : D)
    : Prop
    := (x ∈ C) ∧ ∃ ε : NNReal, ∀ y ∈ (C ∩ Metric.ball x ε), f x ≤ f y

theorem global_min_then_local_min
    [PseudoMetricSpace D] [LE R]
    {f: D → R}
    {C: Set D}
    {x : D}
    : GlobalMinimizer f C x → LocalMinimizer f C x
    := by
    simp [GlobalMinimizer, LocalMinimizer, nndist]
    intro hx hXIsMin
    constructor
    exact hx
    exists 1
    intro x2 hx2 _
    exact hXIsMin x2 hx2

def StrictLocalMinimizer
    [PseudoMetricSpace D] [LT R]
    (f: D → R)
    (C: Set D)
    (x : D)
    : Prop
    := (x ∈ C) ∧ ∃ ε : NNReal, ∀ y ∈ (C ∩ Metric.ball x ε), f x < f y

def IsolatedStrictLocalMinimizer
    [PseudoMetricSpace D] [LT R] [LE R]
    (f: D → R)
    (C: Set D)
    (x : D)
    : Prop
    :=
        StrictLocalMinimizer f C x
        ∧ ∃ ε : NNReal, ∀ y : D, (LocalMinimizer f (C ∩ Metric.ball x ε) y → y = x)

def CriticalPoint
    [RCLike R] [NormedAddCommGroup D] [InnerProductSpace R D] [CompleteSpace D]
    (f: D → R)
    (C : Set D)
    (x : D)
    : Prop
    := HasGradientWithinAt f 0 C x

theorem local_min_on_open_set_then_critical_point
    [NormedAddCommGroup D] [CompleteSpace D]
    [LE R] [RCLike R]
    [InnerProductSpace R D]
    {f: D → R}
    {C: Set D}
    {x : D}
    (hLocalMin : LocalMinimizer f C x)
    (hCIsOpen : IsOpen C)
    : CriticalPoint f C x
    := by
    simp only [CriticalPoint, HasGradientWithinAt, HasGradientAtFilter, map_zero, nhdsWithin, nhds,
        Set.mem_setOf_eq, Filter.principal]
    constructor; case isLittleOTVS =>
    simp only [ContinuousLinearMap.zero_apply, sub_zero]
    intro U hU

    simp only [LocalMinimizer, Set.mem_inter_iff, Metric.mem_ball, dist_lt_coe,
        and_imp] at hLocalMin
    simp only [IsOpen] at hCIsOpen
    unfold TopologicalSpace.IsOpen at hCIsOpen
    simp only [UniformSpace.toTopologicalSpace, PseudoMetricSpace.toUniformSpace,
        SeminormedAddCommGroup.toPseudoMetricSpace, NormedAddCommGroup.toSeminormedAddCommGroup,
        MetricSpace.toPseudoMetricSpace, NormedAddCommGroup.toMetricSpace] at hCIsOpen

    exists Metric.ball 0 (hLocalMin.right.choose)
    -- unfold fderiv

    /-
    - take a local min -> it's smaller than all other points in some open ball
    - C is open -> that ball of points are all feasible
    - for each component / dimension of xmin:
        - add ε to xmin_i -> this point is bigger -> the gradient must be non-negative
        - sub ε to xmin_i -> this point is also bigger -> the gradient must be non-positive
        -> the gradient on this component is zero
    - the overall gradient is zero
    -/
    sorry

def SaddlePoint
    [LE R] [RCLike R] [NormedAddCommGroup D] [InnerProductSpace R D] [CompleteSpace D]
    (f: D → R)
    (C : Set D)
    (x : D)
    : Prop
    := CriticalPoint f C x ∧ ¬LocalMinimizer f C x

example
    : SaddlePoint (fun x: Real => x ^ 3) Set.univ 0
    := by
    simp only [SaddlePoint, CriticalPoint, hasGradientWithinAt_univ, LocalMinimizer, Set.mem_univ,
      Set.univ_inter, Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, true_and, not_exists, not_forall,
      Classical.not_imp, not_le]
    constructor
    case left =>
        sorry
    case right =>
        sorry

theorem inf_on_compact_set_then_min
    [TopologicalSpace D] [LE R]
    {f: D → R}
    {C: Set D}
    {inf : R}
    (hinf : InfimumOn f C inf)
    (hCIsCompact : IsCompact C)
    : MinimumOn f C inf
    := by
    sorry

end main
