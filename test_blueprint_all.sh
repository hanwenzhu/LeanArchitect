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

# Private helperFn should NOT be included
if python3 -c "import json; d=json.load(open('$basic_json')); assert any('helper' in n['data']['name'] for n in d)" 2>/dev/null; then
  echo "FAIL: Private helperFn should not be included"
  exit 1
fi

echo "Testing --all on Theorems module..."
rm -f .lake/build/blueprint/module/ArchitectTest/BlueprintAll/Theorems.json
lake env .lake/build/bin/extract_blueprint single --json --all --build .lake/build ArchitectTest.BlueprintAll.Theorems

theorems_json=".lake/build/blueprint/module/ArchitectTest/BlueprintAll/Theorems.json"

# Should contain mix_comm and mix_assoc (2 nodes), NOT Color or Color.mix from Basic
count=$(python3 -c "import json; d=json.load(open('$theorems_json')); print(len(d))")
if [ "$count" != "2" ]; then
  echo "FAIL: Theorems module should have 2 nodes, got $count"
  cat "$theorems_json"
  exit 1
fi

names=$(python3 -c "import json; d=json.load(open('$theorems_json')); print(' '.join(sorted(n['data']['name'] for n in d)))")
if [ "$names" != "Color.mix_assoc Color.mix_comm" ]; then
  echo "FAIL: Theorems module should have Color.mix_comm and Color.mix_assoc, got: $names"
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

echo "Testing LaTeX output (sorry detection)..."
rm -rf .lake/build/blueprint/module/ArchitectTest/BlueprintAll/Theorems.tex .lake/build/blueprint/module/ArchitectTest/BlueprintAll/Theorems.artifacts
lake env .lake/build/bin/extract_blueprint single --all --build .lake/build ArchitectTest.BlueprintAll.Theorems

# mix_assoc is sorry'd — proof should NOT have \leanok
assoc_tex=".lake/build/blueprint/module/ArchitectTest/BlueprintAll/Theorems.artifacts/Color.mix_assoc.tex"
if grep -A1 'begin{proof}' "$assoc_tex" | grep -q '\\leanok'; then
  echo "FAIL: mix_assoc proof should NOT have \\leanok (it has sorry)"
  cat "$assoc_tex"
  exit 1
fi

# mix_comm is proved — proof SHOULD have \leanok
comm_tex=".lake/build/blueprint/module/ArchitectTest/BlueprintAll/Theorems.artifacts/Color.mix_comm.tex"
if ! grep -A1 'begin{proof}' "$comm_tex" | grep -q '\\leanok'; then
  echo "FAIL: mix_comm proof SHOULD have \\leanok (it is proved)"
  cat "$comm_tex"
  exit 1
fi

# \lean{} should not be empty
if grep -q '\\lean{}' "$assoc_tex"; then
  echo "FAIL: \\lean{} should not be empty"
  cat "$assoc_tex"
  exit 1
fi

echo "All tests passed!"
