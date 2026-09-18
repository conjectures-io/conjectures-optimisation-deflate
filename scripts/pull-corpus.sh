#!/usr/bin/env bash
# Fetch the scoring corpora from their own repositories into data/benchmark/.
#
#   scripts/pull-corpus.sh            both stages (stage 2 is skipped if you lack access)
#   scripts/pull-corpus.sh --stage 1  just the public set
#   scripts/pull-corpus.sh --force    discard local edits to the corpus dirs
#
# WHY THE CORPUS LIVES IN SEPARATE REPOSITORIES
#
# Stage 2 is the held-out set. If its bytes are committed here, then this repository
# can never be made public, can never be forked into the miner-facing one, and every
# clone anyone has ever taken carries the hidden corpus forever -- git keeps history,
# so deleting the files later does not undo any of that. Splitting the datasets out
# means the access boundary is a repository ACL, which is a thing you can actually
# change, rather than a property of this history, which is not.
#
# It also means the two corpora can be re-cut for a new round without touching this
# repository's history at all.
#
# WHY IT COPIES INSTEAD OF CLONING IN PLACE
#
# The dataset repos carry a README and (for stage 1) SOURCES.md alongside the bytes,
# but everything that scores a submission treats data/benchmark/corpus-stageN/ as "a
# directory of corpus files" and iterates over it. A clone dropped there directly would
# hand the scorer a README.md and a .git to compress. So the clone lands in
# .corpus-repos/ and the corpus/ subdirectory is mirrored out of it.
#
# WHAT IS NOT CHECKED HERE
#
# Nothing verifies the bytes beyond what git already guarantees on clone. There is no
# checksum manifest on purpose: git objects are content-addressed, so a second hash of
# the same bytes would only restate it.
set -euo pipefail

# A private stage 2 you lack access to must fail fast, not block on a credential
# prompt: git writes that prompt straight to /dev/tty, so stderr redirection alone
# does not silence it.
export GIT_TERMINAL_PROMPT=0

ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
BENCH="$ROOT/data/benchmark"
REPOS="$BENCH/.corpus-repos"

# Override in .env when the datasets live somewhere else -- a sibling checkout, a
# mirror, a round-specific fork. A local path works exactly as well as a URL.
: "${CORPUS_STAGE1_REMOTE:=https://github.com/conjectures-io/conjectures-compression-corpus-1}"
: "${CORPUS_STAGE2_REMOTE:=https://github.com/conjectures-io/conjectures-compression-corpus-2}"

STAGES=""
FORCE=0
while [ $# -gt 0 ]; do
    case "$1" in
        --stage) STAGES="$STAGES $2"; shift 2 ;;
        --force) FORCE=1; shift ;;
        -h|--help) sed -n '2,8p' "${BASH_SOURCE[0]}" | sed 's/^# \?//'; exit 0 ;;
        *) echo "unknown argument: $1" >&2; exit 2 ;;
    esac
done
[ -n "$STAGES" ] || STAGES="1 2"

fetch_stage() {
    local stage=$1 remote=$2
    local repo="$REPOS/stage$stage" dest="$BENCH/corpus-stage$stage"
    # Kept beside the corpus dir, never inside it: everything that scores a submission
    # iterates over corpus-stageN/ and would otherwise compress this and diff against it.
    local stampfile="$REPOS/stage$stage.head"

    if [ -d "$repo/.git" ]; then
        # Honour a changed CORPUS_STAGE*_REMOTE on an existing checkout, rather than
        # silently continuing to fetch from whatever it was first cloned from.
        git -C "$repo" remote set-url origin "$remote" 2>/dev/null || true
        # Reset rather than pull: these are read-only datasets, so a divergence is
        # someone having edited the checkout, not work worth merging.
        if ! git -C "$repo" fetch -q --depth 1 origin HEAD 2>/dev/null; then
            echo "stage $stage  could not reach $remote -- keeping the checkout in place"
            return 1
        fi
        git -C "$repo" reset -q --hard FETCH_HEAD
    else
        mkdir -p "$REPOS"
        rm -rf "$repo"
        if ! git clone -q --depth 1 "$remote" "$repo" 2>/dev/null; then
            rm -rf "$repo"
            return 1
        fi
    fi

    [ -d "$repo/corpus" ] || { echo "stage $stage  no corpus/ in $remote" >&2; return 1; }

    # Refuse to clobber a corpus dir that is not ours and not empty: it could be a
    # hand-placed round corpus, and silently replacing the thing a validator scores
    # against is the worst possible failure here.
    if [ -d "$dest" ] && [ "$FORCE" -eq 0 ] && [ ! -f "$stampfile" ] \
       && [ -n "$(ls -A "$dest" 2>/dev/null)" ]; then
        echo "stage $stage  $dest exists and was not placed by this script." >&2
        echo "             move it aside, or re-run with --force." >&2
        return 1
    fi

    rm -rf "$dest"
    mkdir -p "$dest"
    cp "$repo/corpus/"* "$dest/"
    # formats.json lives at the dataset repo's own root, beside its README and
    # SOURCES.md -- never inside corpus/, so it never gets scored as a corpus file.
    # Mirrored here as a sibling of $dest, for the same reason.
    [ -f "$repo/formats.json" ] && cp "$repo/formats.json" "$BENCH/corpus-stage$stage.formats.json"
    git -C "$repo" rev-parse HEAD > "$stampfile"

    local n bytes
    n=$(find "$dest" -maxdepth 1 -type f | wc -l)
    bytes=$(find "$dest" -maxdepth 1 -type f -printf '%s\n' | awk '{t+=$1} END {print t+0}')
    printf "stage %s  %s files, %'d bytes, at %s\n" \
        "$stage" "$n" "$bytes" "$(git -C "$repo" rev-parse --short HEAD)"
}

rc=0
for stage in $STAGES; do
    case "$stage" in
        1) remote=$CORPUS_STAGE1_REMOTE ;;
        2) remote=$CORPUS_STAGE2_REMOTE ;;
        *) echo "no such stage: $stage" >&2; exit 2 ;;
    esac

    if ! fetch_stage "$stage" "$remote"; then
        if [ "$stage" = 2 ]; then
            # Expected for anyone outside the validator operators. Not an error: a
            # miner with a working stage 1 has everything they need to compete.
            echo "stage 2  unavailable ($remote) -- skipping the held-out corpus."
        else
            echo "stage $stage  FAILED ($remote)" >&2
            rc=1
        fi
    fi
done

exit $rc
