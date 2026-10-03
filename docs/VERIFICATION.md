# Verification record

Date: 2026-10-03

## Passed locally

- Lean 4.35.0-rc2 with mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`
- Standalone `Solution.lean`, `Challenge.lean`, and `Examples.lean` compilation
- Independent mathematical statement and implementation reviews
- Independent fresh compilation and adversarial reviewer tests
- Selected theorem/definition comparison in separate Lean environments:
  exact type and body matches after universe-parameter normalization
- Standard-only axiom audits (`propext`, `Classical.choice`, `Quot.sound`)
- Bundled fresh Lean kernel checker over `Solution`
- Bundled NanoDa 0.4.17 replay: 8,423 declarations, no typechecker errors
- Bundled con-ron verified replay: accepted 7,692 declarations
- Official pinned pipeline source-requirements inspection: 3 Lean files, no errors
- Official metadata loader and local package-shape checks

NanoDa emitted its known pretty-printer notice “Unable to print axioms”. It had
no typechecker errors and exited successfully. No additional axiom was permitted.

## Not established locally

The official sandboxed Comparator could not execute because this cloud runtime's
mount layout yields `bwrap: Destination is not a directory /root`.
No sandbox bypass or security change was used. Direct declaration comparison and
external-kernel replays are separate evidence and are not an official Comparator
verdict.

The supported hosted `palomar-standard-v1` workflow and the official trusted
Verso Challenge rendering are prepared but not yet dispatched. Public repository
publication and registry intake have not occurred. Local success does not mean
registry acceptance or completion of the hosted end-to-end workflow.

## Reviewed scope

The main theorem allows arbitrary finite player types and arbitrary nonempty
player-dependent action types. Infinite action types, repeated players, arbitrary
finite path length, degenerate rectangles, and empty player sets are covered.
Only the pure-Nash existence consequence additionally requires finite actions.

Independent counterexamples reject matching pennies and establish that a
one-player exact-potential game on real actions need not have a pure equilibrium.
The path convention permits no-ops, with endpoint/integral-preserving deletion
proved in the solution.
