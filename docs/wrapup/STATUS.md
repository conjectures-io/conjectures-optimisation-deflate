# Wrap-up status and how to resume

Updated 2026-10-13. Plan: [PLAN.md](PLAN.md). Rules: [PREREGISTRATION.md](PREREGISTRATION.md).
Results: [FINDINGS.md](FINDINGS.md). Method and reproduction: [METHODOLOGY.md](METHODOLOGY.md) and `wrapup/scripts/reproduce.sh`. The final deliverable is a blog post for the
website (`conjectures-web-new/posts/<slug>.mdx`).

## Done

- `wrapup/arena`: harness (encoder parity with the gate, adaptive blocks, streaming,
  BGZF, PNG, message flushes, zlib-API libraries by path), 13 tests.
- `wrapup/scripts`: data, tools, benchmarking, ranking, screen and selection, stats.
- s66: tools built, scenario data S1–S7 fetched, set A and C4 generated, PROD export
  unpacked, reference run on c1/c2/c3, stage 1 (public candidates) on C4 and set A.

## Done since

- Stage 1b, final selection (`results/05-select/`), all seven scenarios
  (`results/06-scenarios/`, 2026-10-12 16:35–23:53), report tables
  (`results/07-report/scenarios.{md,json}`).
- FINDINGS.md complete; blog post drafted at `docs/wrapup/blog/deflate-competition-results.mdx`.
- METHODOLOGY.md and `wrapup/scripts/reproduce.sh` (2026-10-13).
- `wrapup/verified-deflate`: the library and `vgzip` CLI with #521/#85/#243 (2026-10-13);
  `publish = false` until the licence of miners' code is decided.

## Open

- Review of the blog post by the team; then copy it to `conjectures-web-new/posts/` (the
  site has no remark-gfm: the post avoids pipe tables and `$`).
- Optional: per-scenario charts for the post; a parser variant with a smaller window for S7.

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
