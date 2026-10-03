# Monderer–Shapley exact-potential characterization in Lean

The complete characterization from Monderer and Shapley, **Potential Games**,
Games and Economic Behavior 14 (1996), Theorem 2.8 and Corollary 2.9.

For **any finite player type**, **arbitrary player-dependent nonempty action
spaces**, and **arbitrary real payoffs**, the following are equivalent:

1. An exact potential exists
2. Every finite closed deviation path has zero total deviator payoff change
3. Every finite simple closed deviation path has zero total payoff change
4. Every simple closed path of length four has zero total payoff change
5. Every two-player deviation rectangle satisfies the four-cycle identity

The main result imposes **no finite-action, continuity, compactness, potential,
path-independence, or Nash-existence premise**. Potentials are unique up to an
additive constant. If each action space is finite, a pure Nash equilibrium exists.
The empty-player case is included.

## Proof surface

- `Challenge.lean`: independent model definitions and three deliberate theorem holes
- `Solution.lean`: standalone complete proofs importing only pinned mathlib
- `Examples.lean`: compiled adversarial and boundary examples
- `comparator.json`: full characterization, uniqueness, equilibrium consequence,
  and every model definition used by the theorem types

The construction inserts players into a finite coordinate set. A two-player
rectangle identity is exactly what makes the next player's payoff difference
preserve the previous players' potential identities. All finite paths then
follow by telescoping. The simple-four-cycle bridge handles degenerate choices
separately and proves nondegenerate rectangle vertices are distinct.

Tagged paths may contain no-op updates. An explicit no-op-removal theorem proves
this does not change the classical path condition.

## Examples

- Coordination satisfies the cycle identity and has a pure equilibrium
- Matching pennies violates the identity and admits no exact potential
- A polynomial game on arbitrary real actions has an exact potential
- Unequal dependent action spaces (`Fin 2` and `Fin 3`) instantiate the results
- Empty players and singleton actions instantiate correctly
- A one-player unbounded real-action game is potential but has no pure Nash,
  showing why the equilibrium companion requires finite actions

## Build

Pinned Lean `v4.35.0-rc2` and mathlib commit
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.

```
lake exe cache get
lake build
python scripts/check_candidate.py
```

Local proof checks passed, including standard-only axiom audits, fresh Lean
kernel checking, NanoDa and verified con-ron replay of the selected declaration
closure. A local independent environment comparison matches every selected
theorem type and definition body after universe-parameter normalization.
Those direct local checks do **not** establish the official sandboxed Comparator,
standard hosted profile, trusted Challenge rendering, or registry acceptance.

The prepared manual workflows use the pinned official pipeline and the supported
GitHub-hosted standard profile. Their security-approval inputs default to false.
Publication, dispatch and registry intake require the maintainer's authorization.

## Attribution and prior art

This formalizes established mathematics and makes no novelty or priority claim.
Existing Lean potential-game definitions, maximizer/Nash consequences and ordinal
potential results informed the prior-art check; the submitted result is the full
exact-potential cycle characterization. No TTC result is part of this package.

Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy Jose Guerra Barretto de Queiroz

Responsible maintainer: Arthur Freitas Ramos

Primary source: [Potential Games](https://doi.org/10.1006/game.1996.0044),
[full-text PDF](https://people.csail.mit.edu/jrennie/trg/papers/monderer-potential-96.pdf)

License: Apache-2.0
