#!/usr/bin/env bash
# Test that --all mode correctly extracts declarations without @[blueprint] attributes.
set -euo pipefail

cd "$(dirname "$0")"

echo "Building test modules..."
lake build ArchitectTest.BlueprintAll.Basic ArchitectTest.BlueprintAll.Theorems

echo "Testing --all on Basic module..."
rm -f .lake/build/blueprint/module/ArchitectTest/BlueprintAll/Basic.json
lake env .lake/build/bin/extract_blueprint single --json --all --build .lake/build ArchitectTest.BlueprintAll.Basic

basic_json=".lake/build/blueprint/module/ArchitectTest/BlueprintAll/Basic.json"

# Should contain Color and Color.mix (2 nodes)
count=$(python3 -c "import json; d=json.load(open('$basic_json')); print(len(d))")
if [ "$count" != "2" ]; then
  echo "FAIL: Basic module should have 2 nodes, got $count"
  cat "$basic_json"
  exit 1
fi

# Should contain Color and Color.mix by name
names=$(python3 -c "import json; d=json.load(open('$basic_json')); print(' '.join(sorted(n['data']['name'] for n in d)))")
if [ "$names" != "Color Color.mix" ]; then
  echo "FAIL: Basic module should have Color and Color.mix, got: $names"
  exit 1
fi

# Private helperFn should NOT be included (check exact name set, not substring)
if python3 -c "
import json
d = json.load(open('$basic_json'))
names = {n['data']['name'] for n in d}
assert 'Color.helperFn' in names or any('helper' in n for n in names)
" 2>/dev/null; then
  echo "FAIL: Private helperFn should not be included"
  exit 1
fi

echo "Testing --all on Theorems module..."
rm -f .lake/build/blueprint/module/ArchitectTest/BlueprintAll/Theorems.json
lake env .lake/build/bin/extract_blueprint single --json --all --build .lake/build ArchitectTest.BlueprintAll.Theorems

theorems_json=".lake/build/blueprint/module/ArchitectTest/BlueprintAll/Theorems.json"

# Should contain 3 nodes, NOT Color or Color.mix from Basic
count=$(python3 -c "import json; d=json.load(open('$theorems_json')); print(len(d))")
if [ "$count" != "3" ]; then
  echo "FAIL: Theorems module should have 3 nodes, got $count"
  cat "$theorems_json"
  exit 1
fi

names=$(python3 -c "import json; d=json.load(open('$theorems_json')); print(' '.join(sorted(n['data']['name'] for n in d)))")
if [ "$names" != "Color.mix_assoc Color.mix_blue_red_comm Color.mix_comm" ]; then
  echo "FAIL: Theorems module should have mix_comm, mix_assoc, mix_blue_red_comm, got: $names"
  exit 1
fi

echo "Testing without --all (should be empty)..."
rm -f .lake/build/blueprint/module/ArchitectTest/BlueprintAll/Theorems.json
lake env .lake/build/bin/extract_blueprint single --json --build .lake/build ArchitectTest.BlueprintAll.Theorems

count=$(python3 -c "import json; d=json.load(open('$theorems_json')); print(len(d))")
if [ "$count" != "0" ]; then
  echo "FAIL: Without --all, should have 0 nodes, got $count"
  exit 1
fi

echo "Testing LaTeX output (sorry detection and dependency inference)..."
rm -rf .lake/build/blueprint/module/ArchitectTest/BlueprintAll/Theorems.tex .lake/build/blueprint/module/ArchitectTest/BlueprintAll/Theorems.artifacts
lake env .lake/build/bin/extract_blueprint single --all --build .lake/build ArchitectTest.BlueprintAll.Theorems

artifacts=".lake/build/blueprint/module/ArchitectTest/BlueprintAll/Theorems.artifacts"

# mix_assoc is sorry'd — its proof block should NOT contain \leanok
assoc_proof=$(python3 -c "
import re
tex = open('$artifacts/Color.mix_assoc.tex').read()
proof = re.search(r'\\\\begin\{proof\}(.*?)\\\\end\{proof\}', tex, re.DOTALL)
print(proof.group(1) if proof else '')
")
if echo "$assoc_proof" | grep -q '\\leanok'; then
  echo "FAIL: mix_assoc proof should NOT have \\leanok (it has sorry)"
  cat "$artifacts/Color.mix_assoc.tex"
  exit 1
fi

# mix_comm is proved — its proof block SHOULD contain \leanok
comm_proof=$(python3 -c "
import re
tex = open('$artifacts/Color.mix_comm.tex').read()
proof = re.search(r'\\\\begin\{proof\}(.*?)\\\\end\{proof\}', tex, re.DOTALL)
print(proof.group(1) if proof else '')
")
if ! echo "$comm_proof" | grep -q '\\leanok'; then
  echo "FAIL: mix_comm proof SHOULD have \\leanok (it is proved)"
  cat "$artifacts/Color.mix_comm.tex"
  exit 1
fi

# \lean{} should not be empty
if grep -q '\\lean{}' "$artifacts/Color.mix_assoc.tex"; then
  echo "FAIL: \\lean{} should not be empty"
  cat "$artifacts/Color.mix_assoc.tex"
  exit 1
fi

# Dependency inference: mix_blue_red_comm uses mix_comm in its proof
# The proof block should contain \uses{Color.mix_comm}
dep_tex="$artifacts/Color.mix_blue_red_comm.tex"
if ! grep -q '\\uses{Color.mix_comm}' "$dep_tex"; then
  echo "FAIL: mix_blue_red_comm proof should have \\uses{Color.mix_comm} (dependency inference)"
  cat "$dep_tex"
  exit 1
fi

echo "All tests passed!"
