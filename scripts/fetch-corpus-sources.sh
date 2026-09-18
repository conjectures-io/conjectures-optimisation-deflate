#!/usr/bin/env bash
# Download the real-world source pool the benchmark corpus is cut from, into
# data/benchmark/sources/ (gitignored, ~400 MB).
#
#   scripts/fetch-corpus-sources.sh            everything
#   scripts/fetch-corpus-sources.sh --list     print the manifest and exit
#
# Why a pool rather than generated data: a synthetic corpus can be made to match
# real byte statistics, but it can only reproduce the structure someone thought to
# model. Real data brings the irregularity nobody models. It also defends the hidden
# stage far better -- stage 1 and stage 2 are cut from DISJOINT halves of this pool,
# so stage 2 is real data the public set never contained, and the pool is large
# enough that no 1 MB submission can carry a table of it.
#
# Everything here is permissively licensed or public domain; scripts/SOURCES.tsv
# records what each one is. This is preliminary: the list is a starting point, not
# a vetted legal position, and nothing downloaded is redistributed by this repo --
# the pool is gitignored and each machine fetches its own.

set -uo pipefail

DEST="$(cd "$(dirname "${BASH_SOURCE[0]}")/../data/benchmark" && pwd)/sources"
SOURCES_TSV="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/SOURCES.tsv"
UA="conjectures-benchmark/0.1 (corpus builder; contact via repository)"
RANGE_BYTES=16777216   # how much of a `range` source to take (16 MB)

# kind <TAB> name <TAB> license <TAB> url
# kind is how the builder treats it: `tar` is unpacked and mined by extension,
# `file` is kept as-is, `gz` is gunzipped, and `range` takes only the first
# RANGE_BYTES of the URL -- used for model checkpoints, where a few hundred MB
# would be downloaded to slice half a megabyte out of it. The head of the file is
# the right part to take: it carries the real container header (safetensors JSON,
# GGUF metadata and tensor table) as well as tensor data, in about the proportion
# the whole file has.
MANIFEST=$(cat <<'EOM'
tar	sqlite	Public Domain	https://codeload.github.com/sqlite/sqlite/tar.gz/refs/heads/master
tar	redis	BSD-3-Clause	https://codeload.github.com/redis/redis/tar.gz/refs/tags/7.4.0
tar	curl	curl (MIT-like)	https://codeload.github.com/curl/curl/tar.gz/refs/heads/master
tar	ripgrep	MIT/Unlicense	https://codeload.github.com/BurntSushi/ripgrep/tar.gz/refs/heads/master
tar	tokio	MIT	https://codeload.github.com/tokio-rs/tokio/tar.gz/refs/heads/master
tar	serde	MIT/Apache-2.0	https://codeload.github.com/serde-rs/serde/tar.gz/refs/heads/master
tar	requests	Apache-2.0	https://codeload.github.com/psf/requests/tar.gz/refs/heads/main
tar	flask	BSD-3-Clause	https://codeload.github.com/pallets/flask/tar.gz/refs/heads/main
tar	django	BSD-3-Clause	https://codeload.github.com/django/django/tar.gz/refs/heads/main
tar	mathlib4	Apache-2.0	https://codeload.github.com/leanprover-community/mathlib4/tar.gz/refs/heads/master
tar	maven	Apache-2.0	https://codeload.github.com/apache/maven/tar.gz/refs/heads/master
tar	nlohmann-json	MIT	https://codeload.github.com/nlohmann/json/tar.gz/refs/heads/develop
tar	bootstrap	MIT	https://codeload.github.com/twbs/bootstrap/tar.gz/refs/heads/main
tar	loghub	MIT (research logs)	https://codeload.github.com/logpai/loghub/tar.gz/refs/heads/master
tar	typescript	Apache-2.0	https://codeload.github.com/microsoft/TypeScript/tar.gz/refs/heads/main
tar	ansible	GPL-3.0 (YAML playbooks)	https://codeload.github.com/ansible/ansible/tar.gz/refs/heads/devel
tar	kubernetes-examples	Apache-2.0	https://codeload.github.com/kubernetes/examples/tar.gz/refs/heads/master
tar	free-programming-books	CC-BY-4.0	https://codeload.github.com/EbookFoundation/free-programming-books/tar.gz/refs/heads/main
tar	rust-book	MIT/Apache-2.0	https://codeload.github.com/rust-lang/book/tar.gz/refs/heads/main
tar	loghub-zookeeper	MIT (research logs)	https://zenodo.org/records/8196385/files/Zookeeper.tar.gz
tar	loghub-apache	MIT (research logs)	https://zenodo.org/records/8196385/files/Apache.tar.gz
tar	loghub-proxifier	MIT (research logs)	https://zenodo.org/records/8196385/files/Proxifier.tar.gz
tar	loghub-linux	MIT (research logs)	https://zenodo.org/records/8196385/files/Linux.tar.gz
tar	loghub-mac	MIT (research logs)	https://zenodo.org/records/8196385/files/Mac.tar.gz
tar	loghub-healthapp	MIT (research logs)	https://zenodo.org/records/8196385/files/HealthApp.tar.gz
tar	loghub-openstack	MIT (research logs)	https://zenodo.org/records/8196385/files/OpenStack.tar.gz
file	gutenberg-war-and-peace	Public Domain	https://www.gutenberg.org/cache/epub/2600/pg2600.txt
file	gutenberg-moby-dick	Public Domain	https://www.gutenberg.org/cache/epub/2701/pg2701.txt
file	gutenberg-middlemarch	Public Domain	https://www.gutenberg.org/cache/epub/145/pg145.txt
file	gutenberg-quixote	Public Domain	https://www.gutenberg.org/cache/epub/996/pg996.txt
file	gutenberg-monte-cristo	Public Domain	https://www.gutenberg.org/cache/epub/1184/pg1184.txt
file	gutenberg-les-miserables	Public Domain	https://www.gutenberg.org/cache/epub/135/pg135.txt
file	gutenberg-anna-karenina	Public Domain	https://www.gutenberg.org/cache/epub/1399/pg1399.txt
file	gutenberg-bleak-house	Public Domain	https://www.gutenberg.org/cache/epub/1023/pg1023.txt
file	gutenberg-zh-dream	Public Domain	https://www.gutenberg.org/cache/epub/24264/pg24264.txt
file	gutenberg-zh-3kingdoms	Public Domain	https://www.gutenberg.org/cache/epub/23950/pg23950.txt
file	gutenberg-ja-kokoro	Public Domain	https://www.gutenberg.org/cache/epub/1982/pg1982.txt
file	gutenberg-ru-idiot	Public Domain	https://www.gutenberg.org/cache/epub/2638/pg2638.txt
file	sakila-schema.sql	BSD-3-Clause	https://raw.githubusercontent.com/jOOQ/sakila/main/postgres-sakila-db/postgres-sakila-schema.sql
file	sakila-data.sql	BSD-3-Clause	https://raw.githubusercontent.com/jOOQ/sakila/main/postgres-sakila-db/postgres-sakila-insert-data.sql
file	northwind.sql	MIT	https://raw.githubusercontent.com/pthom/northwind_psql/master/northwind.sql
file	chinook-postgres.sql	MIT	https://raw.githubusercontent.com/lerocha/chinook-database/master/ChinookDatabase/DataSources/Chinook_PostgreSql.sql
file	chinook-sqlite.sql	MIT	https://raw.githubusercontent.com/lerocha/chinook-database/master/ChinookDatabase/DataSources/Chinook_Sqlite.sql
file	airports.csv	Public Domain	https://davidmegginson.github.io/ourairports-data/airports.csv
file	runways.csv	Public Domain	https://davidmegginson.github.io/ourairports-data/runways.csv
file	navaids.csv	Public Domain	https://davidmegginson.github.io/ourairports-data/navaids.csv
file	covid-timeseries.csv	PDDL	https://raw.githubusercontent.com/datasets/covid-19/main/data/time-series-19-covid-combined.csv
file	plotly.min.js	MIT	https://cdnjs.cloudflare.com/ajax/libs/plotly.js/2.27.0/plotly.min.js
file	echarts.min.js	Apache-2.0	https://cdnjs.cloudflare.com/ajax/libs/echarts/5.4.3/echarts.min.js
file	jquery.min.js	MIT	https://cdnjs.cloudflare.com/ajax/libs/jquery/3.7.1/jquery.min.js
file	katex.min.js	MIT	https://cdnjs.cloudflare.com/ajax/libs/KaTeX/0.16.9/katex.min.js
file	pyodide.asm.wasm	MPL-2.0 (Pyodide)	https://cdn.jsdelivr.net/pyodide/v0.24.1/full/pyodide.asm.wasm
file	resvg.wasm	MPL-2.0 (resvg)	https://cdn.jsdelivr.net/npm/@resvg/resvg-wasm@2.6.0/index_bg.wasm
file	tiktoken.wasm	MIT (tiktoken)	https://cdn.jsdelivr.net/npm/tiktoken@1.0.15/lite/tiktoken_bg.wasm
file	sql.wasm	MIT (sql.js)	https://cdnjs.cloudflare.com/ajax/libs/sql.js/1.10.3/sql-wasm.wasm
file	three.min.js	MIT	https://cdnjs.cloudflare.com/ajax/libs/three.js/r128/three.min.js
file	lodash.min.js	MIT	https://cdnjs.cloudflare.com/ajax/libs/lodash.js/4.17.21/lodash.min.js
file	d3.min.js	ISC	https://cdnjs.cloudflare.com/ajax/libs/d3/7.8.5/d3.min.js
file	chart.min.js	MIT	https://cdnjs.cloudflare.com/ajax/libs/Chart.js/4.4.0/chart.umd.min.js
file	moment.min.js	MIT	https://cdnjs.cloudflare.com/ajax/libs/moment.js/2.29.4/moment.min.js
file	npm-react.json	npm registry metadata	https://registry.npmjs.org/react
file	npm-vue.json	npm registry metadata	https://registry.npmjs.org/vue
file	npm-express.json	npm registry metadata	https://registry.npmjs.org/express
file	npm-webpack.json	npm registry metadata	https://registry.npmjs.org/webpack
file	arxiv-oai-cs.xml	arXiv metadata (CC0)	http://export.arxiv.org/oai2?verb=ListRecords&metadataPrefix=oai_dc&set=cs
range	weights-f32.safetensors	Apache-2.0 (all-MiniLM-L6-v2)	https://huggingface.co/sentence-transformers/all-MiniLM-L6-v2/resolve/main/model.safetensors
range	weights-f16.safetensors	Apache-2.0 (pythia-70m)	https://huggingface.co/EleutherAI/pythia-70m/resolve/main/model.safetensors
range	weights-bf16.safetensors	Apache-2.0 (SmolLM2-135M)	https://huggingface.co/HuggingFaceTB/SmolLM2-135M/resolve/main/model.safetensors
range	weights-q8_0.gguf	Apache-2.0 (SmolLM2-135M-Instruct, quant by bartowski)	https://huggingface.co/bartowski/SmolLM2-135M-Instruct-GGUF/resolve/main/SmolLM2-135M-Instruct-Q8_0.gguf
range	weights-q4_k_m.gguf	Apache-2.0 (SmolLM2-135M-Instruct, quant by bartowski)	https://huggingface.co/bartowski/SmolLM2-135M-Instruct-GGUF/resolve/main/SmolLM2-135M-Instruct-Q4_K_M.gguf
gz	ecoli-genome.fna	Public Domain (NCBI)	https://ftp.ncbi.nlm.nih.gov/genomes/all/GCF/000/005/845/GCF_000005845.2_ASM584v2/GCF_000005845.2_ASM584v2_genomic.fna.gz
gz	yeast-genome.fna	Public Domain (NCBI)	https://ftp.ncbi.nlm.nih.gov/genomes/all/GCF/000/146/045/GCF_000146045.2_R64/GCF_000146045.2_R64_genomic.fna.gz
EOM
)

# Wikipedia articles -> real rendered HTML. CC-BY-SA; fetched, not redistributed.
WIKI_PAGES=(Data_compression Lossless_compression Huffman_coding DEFLATE LZ77_and_LZ78
            Information_theory "Rust_(programming_language)" Linux_kernel Machine_learning
            "Transformer_(deep_learning_architecture)" History_of_China World_War_II
            Mathematics Quantum_mechanics Economics Photosynthesis)

if [[ "${1:-}" == "--list" ]]; then
    printf '%s\n' "$MANIFEST" | column -t -s$'\t'
    exit 0
fi

mkdir -p "$DEST"/{tar,file,html}
printf 'kind\tname\tlicense\turl\n' > "$SOURCES_TSV"

fetch() {  # kind name license url
    local kind="$1" name="$2" lic="$3" url="$4" out
    case "$kind" in
        tar)  out="$DEST/tar/$name.tar.gz" ;;
        gz)   out="$DEST/file/$name" ;;
        *)    out="$DEST/file/$name" ;;
    esac
    if [[ -s "$out" ]]; then
        echo "  $name: present"
        printf '%s\t%s\t%s\t%s\n' "$kind" "$name" "$lic" "$url" >> "$SOURCES_TSV"
        return 0
    fi
    if [[ "$kind" == range ]]; then
        if curl -sSL --fail --max-time 300 -A "$UA" -r "0-$((RANGE_BYTES - 1))" \
               "$url" -o "$out.part" 2>/dev/null; then
            mv "$out.part" "$out"; echo "  $name: $(du -h "$out" | cut -f1) (head)"
        else
            echo "  $name: FAILED" >&2; rm -f "$out.part"; return 1
        fi
    elif [[ "$kind" == gz ]]; then
        if curl -sSL --fail --max-time 300 -A "$UA" "$url" -o "$out.gz" 2>/dev/null \
           && gunzip -f "$out.gz" 2>/dev/null; then
            echo "  $name: $(du -h "$out" | cut -f1)"
        else
            echo "  $name: FAILED" >&2; rm -f "$out.gz"; return 1
        fi
    else
        if curl -sSL --fail --max-time 300 -A "$UA" "$url" -o "$out.part" 2>/dev/null; then
            mv "$out.part" "$out"; echo "  $name: $(du -h "$out" | cut -f1)"
        else
            echo "  $name: FAILED" >&2; rm -f "$out.part"; return 1
        fi
    fi
    printf '%s\t%s\t%s\t%s\n' "$kind" "$name" "$lic" "$url" >> "$SOURCES_TSV"
}

echo "Fetching into $DEST"
fail=0
while IFS=$'\t' read -r kind name lic url; do
    [[ -z "${kind:-}" ]] && continue
    fetch "$kind" "$name" "$lic" "$url" || fail=$((fail + 1))
done <<< "$MANIFEST"

echo "Wikipedia HTML (CC-BY-SA):"
for pg in "${WIKI_PAGES[@]}"; do
    out="$DEST/html/$pg.html"
    if [[ -s "$out" ]]; then echo "  $pg: present"; continue; fi
    if curl -sSL --fail --max-time 60 -A "$UA" "https://en.wikipedia.org/wiki/$pg" -o "$out.part" 2>/dev/null; then
        mv "$out.part" "$out"; echo "  $pg: $(du -h "$out" | cut -f1)"
    else
        echo "  $pg: FAILED" >&2; rm -f "$out.part"; fail=$((fail + 1))
    fi
done
printf 'html\twikipedia-articles (%d pages)\tCC-BY-SA\thttps://en.wikipedia.org/\n' \
    "${#WIKI_PAGES[@]}" >> "$SOURCES_TSV"

echo
du -sh "$DEST"/* 2>/dev/null
echo "total: $(du -sh "$DEST" | cut -f1), $fail failure(s)"
echo "manifest written to $(basename "$SOURCES_TSV")"
echo
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
if [[ -x "$HERE/verify-corpus.py" ]]; then
    echo "Verifying the pool ..."
    python3 "$HERE/verify-corpus.py" --quick || true
fi
echo
echo "Next: scripts/make-benchmark-corpus.py --stage 1 --force"
