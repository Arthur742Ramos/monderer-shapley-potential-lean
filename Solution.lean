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
    (s : Profile A) : List (Move A) → Profile A
  | [] => s
  | m :: ms => endpoint (Function.update s m.1 m.2) ms

def pathIntegral {I : Type*} {A : I → Type*} [DecidableEq I]
    (u : Payoff A) (s : Profile A) : List (Move A) → ℝ
  | [] => 0
  | m :: ms => u m.1 (Function.update s m.1 m.2) - u m.1 s +
      pathIntegral u (Function.update s m.1 m.2) ms

def ClosedPathProperty {I : Type*} {A : I → Type*} [DecidableEq I]
    (u : Payoff A) : Prop :=
  ∀ s ms, endpoint s ms = s → pathIntegral u s ms = 0

/-- No player can improve its payoff by a unilateral deviation. -/
def PureNash {I : Type*} {A : I → Type*} [DecidableEq I]
    (u : Payoff A) (s : Profile A) : Prop :=
  ∀ i a, u i (Function.update s i a) ≤ u i s

end Potential


namespace Potential

/-- Keep the chosen coordinates of a profile, and fix all others at a base profile. -/
def maskedProfile {I : Type*} {A : I → Type*} [DecidableEq I]
    (base : Profile A) (S : Finset I) (s : Profile A) : Profile A :=
  fun i => if i ∈ S then s i else base i

lemma maskedProfile_update_mem {I : Type*} {A : I → Type*} [DecidableEq I]
    (base s : Profile A) (S : Finset I) (j : I) (a : A j) (hj : j ∈ S) :
    maskedProfile base S (Function.update s j a) =
      Function.update (maskedProfile base S s) j a := by
  funext k
  by_cases hk : k = j
  · subst k
    simp [maskedProfile, hj]
  · simp [maskedProfile, hk]

lemma maskedProfile_update_not_mem {I : Type*} {A : I → Type*} [DecidableEq I]
    (base s : Profile A) (S : Finset I) (j : I) (a : A j) (hj : j ∉ S) :
    maskedProfile base S (Function.update s j a) = maskedProfile base S s := by
  funext k
  by_cases hk : k = j
  · subst k
    simp [maskedProfile, hj]
  · simp [maskedProfile, hk]

lemma maskedProfile_insert {I : Type*} {A : I → Type*} [DecidableEq I]
    (base s : Profile A) (S : Finset I) (i : I) :
    maskedProfile base (insert i S) s =
      Function.update (maskedProfile base S s) i (s i) := by
  funext k
  by_cases hk : k = i
  · subst k
    simp [maskedProfile]
  · simp [maskedProfile, hk]

/-- The two-player four-cycle identity constructs a potential, without any
finiteness hypothesis on the action spaces. -/
theorem fourCycle_exists_exactPotential {I : Type*} {A : I → Type*}
    [Fintype I] [DecidableEq I] [∀ i, Nonempty (A i)]
    (u : Payoff A) (h : FourCycle u) : ∃ P : Profile A → ℝ, ExactPotential u P := by
  classical
  let base : Profile A := fun i => Classical.choice (inferInstance : Nonempty (A i))
  have aux : ∀ S : Finset I, ∃ P : Profile A → ℝ,
      (∀ s j, j ∈ S → ∀ a : A j,
        P (Function.update s j a) - P s =
          u j (maskedProfile base S (Function.update s j a)) -
            u j (maskedProfile base S s)) ∧
      (∀ s j, j ∉ S → ∀ a : A j, P (Function.update s j a) = P s) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      refine ⟨fun _ => 0, ?_, ?_⟩
      · intro s j hj
        simp at hj
      · intro s j hj a
        rfl
    | @insert i S hi ih =>
      obtain ⟨P, hP, houtside⟩ := ih
      let Q : Profile A → ℝ := fun s => P s +
        u i (maskedProfile base (insert i S) s) - u i (maskedProfile base S s)
      refine ⟨Q, ?_, ?_⟩
      · intro s j hj a
        rcases Finset.mem_insert.mp hj with hji | hj
        · subst j
          dsimp only [Q]
          rw [houtside s i hi a, maskedProfile_update_not_mem base s S i a hi]
          ring
        · have hij : i ≠ j := by
            intro he
            subst j
            exact hi hj
          have hcycle := h (maskedProfile base S s) i j hij (s i) a
          have h1 := maskedProfile_insert base s S i
          have h2 := maskedProfile_update_mem base s S j a hj
          have h3 := maskedProfile_update_mem base s (insert i S) j a
            (Finset.mem_insert_of_mem hj)
          rw [← h1, ← h2, ← h3] at hcycle
          have hdiff := hP s j hj a
          dsimp only [Q]
          linarith
      · intro s j hj a
        have hjs : j ∉ S := fun hm => hj (Finset.mem_insert_of_mem hm)
        dsimp only [Q]
        rw [houtside s j hjs a,
          maskedProfile_update_not_mem base s (insert i S) j a hj,
          maskedProfile_update_not_mem base s S j a hjs]
  obtain ⟨P, hP, _⟩ := aux Finset.univ
  refine ⟨P, ?_⟩
  intro s i a
  have hm : ∀ t : Profile A, maskedProfile base Finset.univ t = t := by
    intro t
    funext j
    simp [maskedProfile]
  simpa only [hm] using hP s i (Finset.mem_univ i) a

end Potential


namespace Potential
variable {I : Type*} {A : I → Type*} [DecidableEq I]

lemma rectangle_return (s : Profile A) (i j : I) (hij : i ≠ j)
    (a : A i) (b : A j) :
    Function.update (Function.update (Function.update s i a) j b) i (s i) =
      Function.update s j b := by
  rw [Function.update_comm (Ne.symm hij), Function.update_idem, Function.update_eq_self]

/-- An exact potential makes every path integral telescope. -/
theorem exactPotential_pathIntegral (u : Payoff A) (P : Profile A → ℝ)
    (hp : ExactPotential u P) (s : Profile A) (ms : List (Move A)) :
    pathIntegral u s ms = P (endpoint s ms) - P s := by
  induction ms generalizing s with
  | nil => simp [pathIntegral, endpoint]
  | cons m ms ih =>
    simp only [pathIntegral, endpoint, ih]
    have := hp s m.1 m.2
    linarith

theorem exactPotential_closedPaths (u : Payoff A) (P : Profile A → ℝ)
    (hp : ExactPotential u P) : ClosedPathProperty u := by
  intro s ms he
  rw [exactPotential_pathIntegral u P hp, he, sub_self]

theorem exactPotential_fourCycle (u : Payoff A) (P : Profile A → ℝ)
    (hp : ExactPotential u P) : FourCycle u := by
  intro s i j hij a b
  have h1 := hp s i a
  have h2 := hp (Function.update s i a) j b
  have h3 := hp (Function.update s j b) i a
  have h4 := hp s j b
  rw [← Function.update_comm hij a b s] at h3
  linarith

/-- Closed-path vanishing gives the rectangle condition, without any finite
restriction on the action sets or any restriction on path length. -/
theorem closedPaths_fourCycle (u : Payoff A) (h : ClosedPathProperty u) : FourCycle u := by
  intro s i j hij a b
  let ms : List (Move A) := [⟨i, a⟩, ⟨j, b⟩, ⟨i, s i⟩, ⟨j, s j⟩]
  have he : endpoint s ms = s := by
    simp only [ms, endpoint]
    rw [rectangle_return s i j hij a b, Function.update_idem, Function.update_eq_self]
  have hz := h s ms he
  simp only [ms, pathIntegral] at hz
  rw [rectangle_return s i j hij a b, Function.update_idem, Function.update_eq_self] at hz
  linarith

/-- A path whose tagged deviations all actually change the chosen action. -/
def ActualPath (s : Profile A) : List (Move A) → Prop
  | [] => True
  | m :: ms => m.2 ≠ s m.1 ∧ ActualPath (Function.update s m.1 m.2) ms

def ActualClosedPathProperty (u : Payoff A) : Prop :=
  ∀ s ms, ActualPath s ms → endpoint s ms = s → pathIntegral u s ms = 0

/-- No-op moves can be removed without changing either endpoint or integral. -/
theorem remove_noop_moves (u : Payoff A) (s : Profile A) (ms : List (Move A)) :
    ∃ ns : List (Move A), ActualPath s ns ∧ endpoint s ns = endpoint s ms ∧
      pathIntegral u s ns = pathIntegral u s ms := by
  classical
  induction ms generalizing s with
  | nil => exact ⟨[], trivial, rfl, rfl⟩
  | cons m ms ih =>
    by_cases hm : m.2 = s m.1
    · have hu : Function.update s m.1 m.2 = s := by
        rw [hm, Function.update_eq_self]
      obtain ⟨ns, hn, he, hv⟩ := ih s
      refine ⟨ns, hn, ?_, ?_⟩
      · simpa only [endpoint, hu] using he
      · simpa only [pathIntegral, hu, sub_self, zero_add] using hv
    · obtain ⟨ns, hn, he, hv⟩ := ih (Function.update s m.1 m.2)
      exact ⟨m :: ns, ⟨hm, hn⟩, he, congrArg
        (fun z => u m.1 (Function.update s m.1 m.2) - u m.1 s + z) hv⟩

theorem closedPaths_iff_actualClosedPaths (u : Payoff A) :
    ClosedPathProperty u ↔ ActualClosedPathProperty u := by
  constructor
  · intro h s ms _ he
    exact h s ms he
  · intro h s ms he
    obtain ⟨ns, hn, he', hv⟩ := remove_noop_moves u s ms
    rw [← hv]
    exact h s ns hn (he'.trans he)

/-- Visiting the listed players once gives the target coordinates on that list. -/
lemma endpoint_setMoves (base target : Profile A) (is : List I) (j : I) :
    endpoint base (is.map (fun i => (⟨i, target i⟩ : Move A))) j =
      if j ∈ is then target j else base j := by
  induction is generalizing base with
  | nil => simp [endpoint]
  | cons i is ih =>
    simp only [List.map_cons, endpoint, ih, List.mem_cons]
    by_cases hji : j = i
    · subst j
      simp
    · simp [hji]

lemma endpoint_all_setMoves [Fintype I] (base target : Profile A) :
    endpoint base (Finset.univ.toList.map (fun i => (⟨i, target i⟩ : Move A))) = target := by
  funext j
  simp [endpoint_setMoves]

/-- All exact potentials differ by a constant, even with infinite action sets. -/
theorem exactPotential_unique [Fintype I] [∀ i, Nonempty (A i)]
    (u : Payoff A) (P Q : Profile A → ℝ)
    (hp : ExactPotential u P) (hq : ExactPotential u Q) :
    ∃ c : ℝ, ∀ s, P s = Q s + c := by
  classical
  let base : Profile A := fun i => Classical.choice (inferInstance : Nonempty (A i))
  refine ⟨P base - Q base, ?_⟩
  intro s
  let ms := Finset.univ.toList.map (fun i => (⟨i, s i⟩ : Move A))
  have he : endpoint base ms = s := endpoint_all_setMoves base s
  have hp' := exactPotential_pathIntegral u P hp base ms
  have hq' := exactPotential_pathIntegral u Q hq base ms
  rw [he] at hp' hq'
  linarith

end Potential


namespace Potential
variable {I : Type*} {A : I → Type*} [DecidableEq I]

/-- The initial profile and each subsequent profile along a deviation path. -/
def vertices (s : Profile A) : List (Move A) → List (Profile A)
  | [] => [s]
  | m :: ms => s :: vertices (Function.update s m.1 m.2) ms

/-- A closed path is simple when its profiles before the return are distinct. -/
def SimpleClosedPathProperty (u : Payoff A) : Prop :=
  ∀ s ms, endpoint s ms = s → (vertices s ms).dropLast.Nodup →
    pathIntegral u s ms = 0

/-- Vanishing of payoff integrals on simple closed paths of length four. -/
def SimpleFourCycleProperty (u : Payoff A) : Prop :=
  ∀ s ms, endpoint s ms = s → (vertices s ms).dropLast.Nodup → ms.length = 4 →
    pathIntegral u s ms = 0

theorem closedPaths_simpleClosedPaths (u : Payoff A) (h : ClosedPathProperty u) :
    SimpleClosedPathProperty u := by
  intro s ms he _
  exact h s ms he

theorem simpleClosedPaths_simpleFourCycles (u : Payoff A)
    (h : SimpleClosedPathProperty u) : SimpleFourCycleProperty u := by
  intro s ms he hn _
  exact h s ms he hn

/-- A nondegenerate two-player rectangle is a simple four-step closed path. -/
lemma rectangle_vertices_nodup (s : Profile A) (i j : I) (hij : i ≠ j)
    (a : A i) (b : A j) (ha : a ≠ s i) (hb : b ≠ s j) :
    (vertices s [⟨i, a⟩, ⟨j, b⟩, ⟨i, s i⟩, ⟨j, s j⟩]).dropLast.Nodup := by
  have hsB : s ≠ Function.update s i a := by
    intro he
    exact ha (by simpa using (congrFun he i).symm)
  have hsC : s ≠ Function.update (Function.update s i a) j b := by
    intro he
    exact ha (by simpa [hij] using (congrFun he i).symm)
  have hsD : s ≠ Function.update s j b := by
    intro he
    exact hb (by simpa using (congrFun he j).symm)
  have hBC : Function.update s i a ≠ Function.update (Function.update s i a) j b := by
    intro he
    exact hb (by simpa [Ne.symm hij] using (congrFun he j).symm)
  have hBD : Function.update s i a ≠ Function.update s j b := by
    intro he
    exact ha (by simpa [hij] using congrFun he i)
  have hCD : Function.update (Function.update s i a) j b ≠ Function.update s j b := by
    intro he
    exact ha (by simpa [hij] using congrFun he i)
  simp only [vertices, List.dropLast_cons_cons, List.dropLast_singleton]
  rw [rectangle_return s i j hij a b]
  simp [List.nodup_cons, hsB, hsC, hsD, hBC, hBD, hCD]

/-- Simple four-cycle vanishing suffices for the two-player rectangle identity;
degenerate rectangles vanish algebraically. -/
theorem simpleFourCycles_fourCycle (u : Payoff A) (h : SimpleFourCycleProperty u) :
    FourCycle u := by
  intro s i j hij a b
  by_cases ha : a = s i
  · rw [ha, Function.update_eq_self]
    ring
  · by_cases hb : b = s j
    · have hupdate : Function.update (Function.update s i a) j b = Function.update s i a := by
        rw [hb]
        have hj : (Function.update s i a) j = s j := by simp [Ne.symm hij]
        rw [← hj, Function.update_eq_self]
      rw [hupdate, hb, Function.update_eq_self]
      ring
    · let ms : List (Move A) := [⟨i, a⟩, ⟨j, b⟩, ⟨i, s i⟩, ⟨j, s j⟩]
      have he : endpoint s ms = s := by
        simp only [ms, endpoint]
        rw [rectangle_return s i j hij a b, Function.update_idem, Function.update_eq_self]
      have hn : (vertices s ms).dropLast.Nodup := rectangle_vertices_nodup s i j hij a b ha hb
      have hz := h s ms he hn (by rfl)
      simp only [ms, pathIntegral] at hz
      rw [rectangle_return s i j hij a b, Function.update_idem, Function.update_eq_self] at hz
      linarith

end Potential


namespace Potential
variable {I : Type*} {A : I → Type*} [Fintype I] [DecidableEq I]
  [∀ i, Nonempty (A i)]

/-- Monderer–Shapley (1996), Corollary 2.9: exact potentials are characterized
by the two-player four-cycle identity for arbitrary dependent action spaces. -/
theorem monderer_shapley_fourCycle (u : Payoff A) :
    (∃ P : Profile A → ℝ, ExactPotential u P) ↔ FourCycle u := by
  constructor
  · rintro ⟨P, hp⟩
    exact exactPotential_fourCycle u P hp
  · exact fourCycle_exists_exactPotential u

/-- Monderer–Shapley (1996), Theorem 2.8, closed-path formulation. All finite
paths are quantified; action spaces need not be finite. -/
theorem monderer_shapley_closedPaths (u : Payoff A) :
    (∃ P : Profile A → ℝ, ExactPotential u P) ↔ ClosedPathProperty u := by
  constructor
  · rintro ⟨P, hp⟩
    exact exactPotential_closedPaths u P hp
  · intro h
    exact fourCycle_exists_exactPotential u (closedPaths_fourCycle u h)

omit [Fintype I] [∀ i, Nonempty (A i)] in
/-- An exact potential's global maximizer is a pure Nash equilibrium. -/
theorem exactPotential_maximizer_pureNash (u : Payoff A) (P : Profile A → ℝ)
    (hp : ExactPotential u P) (s : Profile A) (hs : ∀ t, P t ≤ P s) : PureNash u s := by
  intro i a
  have he := hp s i a
  have hm := hs (Function.update s i a)
  linarith

/-- In the finite-action case, the four-cycle condition implies existence of a
pure Nash equilibrium. No compactness or optimization assumption is supplied. -/
theorem fourCycle_exists_pureNash [∀ i, Fintype (A i)] (u : Payoff A)
    (hu : FourCycle u) : ∃ s : Profile A, PureNash u s := by
  classical
  obtain ⟨P, hp⟩ := fourCycle_exists_exactPotential u hu
  obtain ⟨s, _, hs⟩ := Finset.univ.exists_max_image P Finset.univ_nonempty
  exact ⟨s, exactPotential_maximizer_pureNash u P hp s
    (fun t => hs t (Finset.mem_univ t))⟩

/-- The complete cycle characterization of Monderer–Shapley, Theorem 2.8,
and its explicit rectangle version, Corollary 2.9. -/
theorem monderer_shapley_characterization (u : Payoff A) :
    ((∃ P : Profile A → ℝ, ExactPotential u P) ↔ ClosedPathProperty u) ∧
    ((∃ P : Profile A → ℝ, ExactPotential u P) ↔ SimpleClosedPathProperty u) ∧
    ((∃ P : Profile A → ℝ, ExactPotential u P) ↔ SimpleFourCycleProperty u) ∧
    ((∃ P : Profile A → ℝ, ExactPotential u P) ↔ FourCycle u) := by
  refine ⟨monderer_shapley_closedPaths u, ?_, ?_, monderer_shapley_fourCycle u⟩
  · constructor
    · intro h
      exact closedPaths_simpleClosedPaths u ((monderer_shapley_closedPaths u).mp h)
    · intro h
      exact fourCycle_exists_exactPotential u
        (simpleFourCycles_fourCycle u (simpleClosedPaths_simpleFourCycles u h))
  · constructor
    · intro h
      exact simpleClosedPaths_simpleFourCycles u
        (closedPaths_simpleClosedPaths u ((monderer_shapley_closedPaths u).mp h))
    · intro h
      exact fourCycle_exists_exactPotential u (simpleFourCycles_fourCycle u h)

end Potential
