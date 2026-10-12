# Wrap-up status and how to resume

Updated 2026-10-12. Plan: [PLAN.md](PLAN.md). Rules: [PREREGISTRATION.md](PREREGISTRATION.md).
Results so far: [FINDINGS.md](FINDINGS.md). The final deliverable is a blog post for the
website (`conjectures-web-new/posts/<slug>.mdx`).

## Done

- `wrapup/arena`: harness (encoder parity with the gate, adaptive blocks, streaming,
  BGZF, PNG, message flushes, zlib-API libraries by path), 13 tests.
- `wrapup/scripts`: data, tools, benchmarking, ranking, screen and selection, stats.
- s66: tools built, scenario data S1–S7 fetched, set A and C4 generated, PROD export
  unpacked, reference run on c1/c2/c3, stage 1 (public candidates) on C4 and set A.

## In progress

- Stage 1b and the final selection are done (`results/05-select/`: `select-{revised,strict}.{txt,json}`,
  `withheld-fails.tsv` from a supplementary c1–c3 run of the four withheld frontier points,
  `parsers.txt`). Selected: #55 #232 #657 #355 #243; also run: #85 #521, contrasts #649 #632 #125.
- Scenarios S1–S7 running since 2026-10-12 16:35 (`results/06-scenarios`, log
  `results/05-select/scenarios.log`), about 6–7 hours on core 7.

## Next

1. When the scenarios finish: `summarize.py` and `rank.py --ref zlib-6` per scenario
   (`results/06-scenarios/<tag>.jsonl` and `<tag>-ext.jsonl`), finish FINDINGS.md §6–7.
2. Write the blog post (`conjectures-web-new/posts/<slug>.mdx`: `export const meta`,
   `Figures`/`Source`/`Disclaimer`; no pipe tables, no `$`).

## Where things are on s66 (`/root/deflate-wrapup`, nothing else touched)

| path | what |
|---|---|
| `src/` | `git archive` of this branch (s66 cannot fetch GitHub); `src/REVISION` |
| `crates/` | parser builds, keyed by source sha256 |
| `tools/` | zlib-madler/ng/cloudflare `.so`, zopfli, zopflipng, 7zz, oxipng, igzip, nasm |
| `data/` | `s1-web` … `s7-messages`, `setA`, `c4` (private), `MANIFEST.tsv` |
| `prod-export/` | PROD `pg_dump`, sources CSV, `sources/<id>/`, `tables/*.sql` (private) |
| `results/` | `00-pool`, `01-bars`, `02-stage1`, `03-stage1b`, ... |

Shipping code: `git archive --prefix=src/ HEAD wrapup | ssh s66 'cd /root/deflate-wrapup && tar -x'`,
then rebuild `src/wrapup/arena` with `cargo +nightly-2026-08-18 build --release` (with
`/root/.cargo/bin` on `PATH`), never while a timed run is going.

Privacy: c2 per-file numbers, C4 contents and the S6 logs (this host's own) stay on s66;
only aggregates go into reports.
