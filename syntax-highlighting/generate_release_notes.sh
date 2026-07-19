#!/usr/bin/env bash
set -euo pipefail

DIR="syntax-highlighting"
FROM_TAG="${1:-}"
TO_REF="${2:-HEAD}"

if [ -z "$FROM_TAG" ]; then
  RANGE="$TO_REF"
else
  RANGE="$FROM_TAG..$TO_REF"
fi

echo "## Changes in $DIR"
echo

git log --pretty=format:"%H %s" "$RANGE" -- "$DIR" | while read -r hash subject; do
  pr=$(gh api "repos/{owner}/{repo}/commits/$hash/pulls" --jq '.[0].number' 2>/dev/null || true)
  if [ -n "$pr" ]; then
    echo "- $subject (#$pr)"
  else
    echo "- $subject (${hash:0:7})"
  fi
done