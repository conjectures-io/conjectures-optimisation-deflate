# The reference corpus

These are the exact bytes every score in this repository's documentation was
measured against. `verifier/make-corpus.py` regenerates the mix from local
sources and will refuse to overwrite these without `--force`; a real round uses
a held-out, commit-revealed corpus instead. See `../docs/SCORING.md`.

| file | bytes | sha256 |
|---|---|---|
| `binary.bin` | 2,000,000 | `2e764f2b66c5ce553d9565b10a7a56e2` |
| `json.txt` | 1,000,000 | `9beb049a5fd7ee055ac5294b39f48d2b` |
| `lean.txt` | 2,000,000 | `f4032f2d3fe4c902d3f42448469696ce` |
| `prose.md.txt` | 1,060,939 | `345aafe9a23e9ed7a9249f13cb30116e` |
| `source.rs.txt` | 2,000,000 | `2e643d25d2b3964aa05795a76cf06d34` |
| **total** | **8,060,939** | |

Five kinds on purpose. A corpus of one kind measures one kind of parse, and the
first headroom measurement in this project's research phase used repetitive
synthetic data, compressed about 300:1, and reported a conclusion that was
backwards.
