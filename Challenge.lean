/-
Monderer–Shapley exact-potential characterization (1996).
Authors: Arthur Freitas Ramos, David Barros Hulak,
Ruy Jose Guerra Barretto de Queiroz.
Released under Apache 2.0.
-/
module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Finset.Max

@[expose] public section

namespace Potential

abbrev Profile {I : Type*} (A : I → Type*) := ∀ i, A i
abbrev Payoff {I : Type*} (A : I → Type*) := I → Profile A → ℝ

/-- Every unilateral payoff difference is exactly the potential difference. -/
def ExactPotential {I : Type*} {A : I → Type*} [DecidableEq I]
    (u : Payoff A) (P : Profile A → ℝ) : Prop :=
  ∀ s i a, P (Function.update s i a) - P s =
    u i (Function.update s i a) - u i s

/-- The sum of deviators' payoff changes around every two-player rectangle is zero.
Degenerate choices are included; their sums vanish automatically. -/
def FourCycle {I : Type*} {A : I → Type*} [DecidableEq I]
    (u : Payoff A) : Prop :=
  ∀ (s : Profile A) (i j : I), i ≠ j → ∀ (a : A i) (b : A j),
    u i (Function.update s i a) - u i s +
    u j (Function.update (Function.update s i a) j b) - u j (Function.update s i a) +
    u i (Function.update s j b) - u i (Function.update (Function.update s i a) j b) +
    u j s - u j (Function.update s j b) = 0

/-- A finite sequence of unilateral deviations. Players may repeat and an action
may equal its current value; no artificial finiteness restriction on actions. -/
abbrev Move {I : Type*} (A : I → Type*) := Σ i, A i

def endpoint {I : Type*} {A : I → Type*} [DecidableEq I]
    (s : Profile A) (ms : List (Move A)) : Profile A :=
  ms.foldl (fun s m => Function.update s m.1 m.2) s

def pathIntegral {I : Type*} {A : I → Type*} [DecidableEq I]
    (u : Payoff A) (s : Profile A) (ms : List (Move A)) : ℝ :=
  (ms.foldl (fun p m => (p.1 + u m.1 (Function.update p.2 m.1 m.2) - u m.1 p.2,
    Function.update p.2 m.1 m.2)) (0, s)).1

def ClosedPathProperty {I : Type*} {A : I → Type*} [DecidableEq I]
    (u : Payoff A) : Prop :=
  ∀ s ms, endpoint s ms = s → pathIntegral u s ms = 0

/-- No player can improve its payoff by a unilateral deviation. -/
def PureNash {I : Type*} {A : I → Type*} [DecidableEq I]
    (u : Payoff A) (s : Profile A) : Prop :=
  ∀ i a, u i (Function.update s i a) ≤ u i s

end Potential
namespace Potential
variable {I : Type*} {A : I → Type*} [DecidableEq I]
def vertices (s : Profile A) (ms : List (Move A)) : List (Profile A) :=
  (ms.foldl (fun p m => (Function.update p.1 m.1 m.2, p.2 ++ [Function.update p.1 m.1 m.2])) (s, [s])).2
end Potential

namespace Potential
variable {I : Type*} {A : I → Type*} [DecidableEq I]
def SimpleClosedPathProperty (u : Payoff A) : Prop :=
  ∀ s ms, endpoint s ms = s → (vertices s ms).dropLast.Nodup →
    pathIntegral u s ms = 0
end Potential

namespace Potential
variable {I : Type*} {A : I → Type*} [DecidableEq I]
def SimpleFourCycleProperty (u : Payoff A) : Prop :=
  ∀ s ms, endpoint s ms = s → (vertices s ms).dropLast.Nodup → ms.length = 4 →
    pathIntegral u s ms = 0
end Potential

namespace Potential
theorem monderer_shapley_characterization {I : Type*} {A : I → Type*} [Fintype I] [DecidableEq I] [∀ i, Nonempty (A i)] (u : Payoff A) :
    ((∃ P : Profile A → ℝ, ExactPotential u P) ↔ ClosedPathProperty u) ∧
    ((∃ P : Profile A → ℝ, ExactPotential u P) ↔ SimpleClosedPathProperty u) ∧
    ((∃ P : Profile A → ℝ, ExactPotential u P) ↔ SimpleFourCycleProperty u) ∧
    ((∃ P : Profile A → ℝ, ExactPotential u P) ↔ FourCycle u) := by
  sorry

theorem fourCycle_exists_pureNash {I : Type*} {A : I → Type*} [Fintype I] [DecidableEq I] [∀ i, Nonempty (A i)] [∀ i, Fintype (A i)] (u : Payoff A)
    (hu : FourCycle u) : ∃ s : Profile A, PureNash u s := by
  sorry

theorem exactPotential_unique {I : Type*} {A : I → Type*} [DecidableEq I] [Fintype I] [∀ i, Nonempty (A i)]
    (u : Payoff A) (P Q : Profile A → ℝ)
    (hp : ExactPotential u P) (hq : ExactPotential u Q) :
    ∃ c : ℝ, ∀ s, P s = Q s + c := by
  sorry

end Potential
