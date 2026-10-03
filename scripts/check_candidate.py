#!/usr/bin/env python3
"""Read-only local source-shape checks. Not an official Palomar verifier."""
from pathlib import Path
import json
import re
import yaml

root = Path(__file__).resolve().parent.parent
required = ['Challenge.lean','Solution.lean','lean-toolchain','lakefile.toml','lake-manifest.json','formalization.yaml','comparator.json','LICENSE']
for name in required:
    assert (root/name).is_file(), name
assert (root/'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.35.0-rc2'
assert '065356127b1dc0016f66b7283ce0ce2c4055aa55' in (root/'lakefile.toml').read_text()
files = [root/'Challenge.lean', root/'Solution.lean', root/'Examples.lean']
for p in files:
    text = p.read_text()
    assert re.search(r'^module\s*$', text, re.M), p
    assert len(text.splitlines()) <= 10000, p
    if p.name != 'Challenge.lean':
        assert not re.search(r'\b(sorry|admit|sorryAx|Lean\.ofReduceBool)\b', text), p
        assert not re.search(r'^\s*(axiom|unsafe)\b', text, re.M), p
challenge = (root/'Challenge.lean').read_text()
assert len(challenge.encode()) <= 102400 and len(challenge.splitlines()) <= 1000
assert len(re.findall(r'\bsorry\b', challenge)) == 3
for imp in re.findall(r'^(?:public )?import\s+(\S+)', challenge, re.M):
    assert imp.startswith('Mathlib.'), imp
m = yaml.safe_load((root/'formalization.yaml').read_text())
assert m['version'] == 'v0.4'
assert m['project']['authors'] == ['Arthur Freitas Ramos','David Barros Hulak','Ruy Jose Guerra Barretto de Queiroz']
assert m['project']['responsible_maintainers'] == ['Arthur Freitas Ramos']
assert m['status']['sorry_count'] == m['status']['sorry_in_definitions'] == 0
assert m['project']['license'] == 'Apache-2.0'
c = json.loads((root/'comparator.json').read_text())
assert c['theorem_names'] == ['Potential.monderer_shapley_characterization','Potential.exactPotential_unique','Potential.fourCycle_exists_pureNash']
assert len(c['definition_names']) == 12
assert set(c['permitted_axioms']) == {'propext','Quot.sound','Classical.choice'}
w = (root/'.github/workflows/palomar.yml').read_text()
pin='65f0154ed776cd26c224254aa57b379137f28b0d'
assert '/submission.yml@'+pin in w and 'pipeline_commit: '+pin in w
assert 'execution_profile: palomar-standard-v1' in w
assert re.fullmatch('[0-9a-z]{12}', re.search(r'request_id:\s*(\S+)', w).group(1))
assert 'approve_binary_scoped_apparmor' in w
r = (root/'.github/workflows/palomar-render.yml').read_text()
assert 'DISPATCHED_COMMIT: ${{ github.sha }}' in r
assert '8a32c262e64226e0c4ea84e2c4ac08f86e0df9cd6019cbe4c3b3e18614e6681a' in r
assert '9f8096e40b31715b1d8d5997f15a0bd832f7e37d' in r
assert 'approve_binary_scoped_apparmor' in r
for p in json.loads((root/'lake-manifest.json').read_text())['packages']:
    if p.get('type') == 'git':
        assert p['url'].startswith('https://github.com/'), p
        assert re.fullmatch('[0-9a-f]{40}', p['rev']), p
print(f'PASS: local candidate source-shape checks ({len(files)} Lean files)')
print('This does not establish Comparator, independent external kernels, official runner, or registration success.')
