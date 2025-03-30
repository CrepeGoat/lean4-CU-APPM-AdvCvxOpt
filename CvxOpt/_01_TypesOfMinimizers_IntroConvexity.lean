import Init.Prelude
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Topology.Defs.Basic

import CvxOpt._00_IntroToOptProblems
import CvxOpt._01_TypesOfMinimizers_IntroConvexity_pre


section main

variable
    {n : Nat}
    {D: Type*}
    {R: Type*}

@[deprecated "just use `x ∈ C`" (since := "2025-03-27")]
def FeasiblePoint
    (C : Set D)
    (x : D)
    : Prop := x ∈ C

example
    [LE R] {C : Set D} {x : D}
    : FeasiblePoint C x ↔ x ∈ C
    := by rfl

@[deprecated "just use `x ∈ ArgumentMinimumOn f C`" (since := "2025-03-27")]
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
    -- (f: (Fin n → D) → R)
    -- (C: Set (Fin n → D))
    -- (x: Fin n → D)
    (f: D → R)
    (x : D)
    : Prop
    := gradient f x = 0

theorem local_min_and_open_then_critical_point
    [NormedAddCommGroup D] [CompleteSpace D]
    [LE R] [RCLike R]
    [InnerProductSpace R D]
    {f: D → R}
    {C: Set D}
    {x : D}
    (hLocalMin : LocalMinimizer f C x)
    (hCIsOpen : IsOpen C)
    : CriticalPoint f x
    := by
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

end main
